import Langlands.GroupScheme.Rational.FiniteCharacterBoundaryCocharacter
import Langlands.GroupScheme.Rational.ParabolicBoundaryRootSupport
import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots
import Langlands.GroupScheme.Rational.NestedParabolicCocharacterFace

/-! # An actual boundary cocharacter for a supplied parabolic presentation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

open RealTorusSpace

variable {k : Type u} [Field k]
  {G P M : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {B : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {m : M ⟶ P} {b : B.toGrp ⟶ M}
  (fine : ParabolicRootPresentation p m b)

private theorem boundary_character_range :
    Set.range (fun α : fine.complementarySimpleRootFinset =>
      (1 : ℝ) ⊗ₜ[ℤ] (fine.data.f ≫ (α : characterLattice fine.data.T))) =
      fine.restrictedRoots := by
  ext y
  constructor
  · rintro ⟨α, rfl⟩
    have hα := fine.mem_complementarySimpleRootFinset.mp α.2
    exact fine.mem_restrictedRoots.mpr ⟨α, hα.1, hα.2, rfl⟩
  · intro hy
    obtain ⟨α, hα, hJ, rfl⟩ := fine.mem_restrictedRoots.mp hy
    exact ⟨⟨α, fine.mem_complementarySimpleRootFinset.mpr ⟨hα, hJ⟩⟩, rfl⟩

/-- The original complementary-root expansion admits an integral supporting
cocharacter of the original split component. -/
theorem exists_boundarySplitComponentCocharacter {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) (hstrict : x ∉ fine.positiveCone) :
    ∃ mu : cocharacterLattice B,
      (∀ α ∈ fine.complementarySimpleRootFinset,
        0 ≤ latticePairing B (fine.data.f ≫ α) mu) ∧
      (∃ α ∈ fine.complementarySimpleRootFinset,
        0 < latticePairing B (fine.data.f ≫ α) mu) ∧
      (∀ α ∈ fine.complementarySimpleRootFinset,
        0 < fine.nonnegRootCoefficients hx α →
          latticePairing B (fine.data.f ≫ α) mu = 0) := by
  classical
  let c : fine.complementarySimpleRootFinset → ℝ :=
    fun α => fine.nonnegRootCoefficients hx α
  let α : fine.complementarySimpleRootFinset → characterLattice B :=
    fun α => fine.data.f ≫ (α : characterLattice fine.data.T)
  have hc (i) : 0 ≤ c i := fine.nonnegRootCoefficients_nonneg hx i.2
  have hsum : (∑ i, c i • ((1 : ℝ) ⊗ₜ[ℤ] α i)) = x := by
    have hs := fine.sum_nonnegRootCoefficients hx
    rw [← Finset.sum_coe_sort] at hs
    simpa only [c, α, ← restrictedRootVector_eq_tmul] using hs
  have hnopos : ¬ ∃ d : fine.complementarySimpleRootFinset → ℝ,
      (∀ i, 0 < d i) ∧
        (∑ i, d i • ((1 : ℝ) ⊗ₜ[ℤ] α i)) =
          ∑ i, c i • ((1 : ℝ) ⊗ₜ[ℤ] α i) := by
    rintro ⟨d, hd, he⟩
    apply hstrict
    exact (RootCombination.mem_positive_iff_fintype fine.finite_restrictedRoots
      (fun i => (1 : ℝ) ⊗ₜ[ℤ] α i) fine.boundary_character_range).mpr
      ⟨d, hd, he.trans hsum⟩
  obtain ⟨mu, hnn, hpos, hz⟩ :=
    RealTorusSpace.exists_boundaryCocharacter
      fine.isCompatible.splitComponent.isCentralSplitTorus.1.1 α c hc hnopos
  refine ⟨mu, ?_, ?_, ?_⟩
  · intro β hβ
    exact hnn ⟨β, hβ⟩
  · obtain ⟨β, hβ⟩ := hpos
    exact ⟨β, β.2, hβ⟩
  · intro β hβ
    exact hz ⟨β, hβ⟩

/-- A chosen actual integral cocharacter of the original fine split component,
obtained from a nonstrict nonnegative vector. -/
def boundarySplitComponentCocharacter {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) (hstrict : x ∉ fine.positiveCone) :
    cocharacterLattice B :=
  (fine.exists_boundarySplitComponentCocharacter hx hstrict).choose

theorem boundarySplitComponentCocharacter_spec {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) (hstrict : x ∉ fine.positiveCone) :
    (∀ α ∈ fine.complementarySimpleRootFinset,
      0 ≤ latticePairing B (fine.data.f ≫ α)
        (fine.boundarySplitComponentCocharacter hx hstrict)) ∧
    (∃ α ∈ fine.complementarySimpleRootFinset,
      0 < latticePairing B (fine.data.f ≫ α)
        (fine.boundarySplitComponentCocharacter hx hstrict)) ∧
    (∀ α ∈ fine.complementarySimpleRootFinset,
      0 < fine.nonnegRootCoefficients hx α →
        latticePairing B (fine.data.f ≫ α)
          (fine.boundarySplitComponentCocharacter hx hstrict) = 0) :=
  (fine.exists_boundarySplitComponentCocharacter hx hstrict).choose_spec

/-- The same cocharacter in the original fine maximal split torus. -/
def boundaryCocharacterInTorus {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) (hstrict : x ∉ fine.positiveCone) :
    cocharacterLattice fine.data.T :=
  cocharacterMapInt fine.data.f (fine.boundarySplitComponentCocharacter hx hstrict)

theorem boundaryCocharacterInTorus_nonneg {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) (hstrict : x ∉ fine.positiveCone)
    {α : characterLattice fine.data.T}
    (hα : α ∈ simpleRelativeRoots fine.data.i fine.data.ν) :
    0 ≤ latticePairing fine.data.T α (fine.boundaryCocharacterInTorus hx hstrict) := by
  rw [boundaryCocharacterInTorus,
    ← RelativeRoot.latticePairing_restrict_cocharacterMapInt]
  by_cases hJ : α ∈ fine.data.J
  · rw [fine.selectedRoot_restrict_eq_zero hJ, map_zero, LinearMap.zero_apply]
  · exact (fine.boundarySplitComponentCocharacter_spec hx hstrict).1 α
      (fine.mem_complementarySimpleRootFinset.mpr ⟨hα, hJ⟩)

theorem boundaryCocharacterInTorus_positive {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) (hstrict : x ∉ fine.positiveCone) :
    ∃ α ∈ simpleRelativeRoots fine.data.i fine.data.ν,
      0 < latticePairing fine.data.T α (fine.boundaryCocharacterInTorus hx hstrict) := by
  obtain ⟨α, hα, hp⟩ := (fine.boundarySplitComponentCocharacter_spec hx hstrict).2.1
  refine ⟨α, (fine.mem_complementarySimpleRootFinset.mp hα).1, ?_⟩
  rwa [boundaryCocharacterInTorus,
    ← RelativeRoot.latticePairing_restrict_cocharacterMapInt]

theorem boundaryRootIndex_subset_boundaryCocharacterFace {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) (hstrict : x ∉ fine.positiveCone) :
    fine.boundaryRootIndex hx ⊆
      simpleRootFace fine.data.i fine.data.ν (fine.boundaryCocharacterInTorus hx hstrict) := by
  intro α hα
  refine ⟨fine.boundaryRootIndex_subset_simpleRoots hx hα, ?_⟩
  rw [boundaryCocharacterInTorus,
    ← RelativeRoot.latticePairing_restrict_cocharacterMapInt]
  by_cases hJ : α ∈ fine.data.J
  · rw [fine.selectedRoot_restrict_eq_zero hJ, map_zero, LinearMap.zero_apply]
  · have hα' := hα.resolve_left hJ
    exact (fine.boundarySplitComponentCocharacter_spec hx hstrict).2.2 α
      (fine.mem_complementarySimpleRootFinset.mpr ⟨hα'.1, hJ⟩) hα'.2

theorem isStandard_boundaryCocharacterInTorus {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) (hstrict : x ∉ fine.positiveCone) :
    IsStandardCocharacter fine.data.i fine.data.ν
      (simpleRootFace fine.data.i fine.data.ν (fine.boundaryCocharacterInTorus hx hstrict))
      (fine.boundaryCocharacterInTorus hx hstrict) :=
  isStandardCocharacter_simpleRootFace _ _
    fun _ hα => fine.boundaryCocharacterInTorus_nonneg hx hstrict hα

variable (hG : IsConnectedReductive G)

include hG in
/-- The boundary cocharacter defines a dynamic parabolic containing the
original supplied parabolic on every test scheme. -/
theorem parabolic_le_boundaryCocharacter {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) (hstrict : x ∉ fine.positiveCone) :
    SubgroupFunctor.range p ≤
      Dynamic.parabolic
        (CommGroupScheme.groupHom (fine.boundaryCocharacterInTorus hx hstrict) ≫
          fine.data.i) := by
  obtain ⟨ζ, hζ, hp, -⟩ := fine.isCompatible.realization
  rw [hp]
  apply (relativeRootSignInclusions k G hG fine.data.T fine.data.i
    fine.isCompatible.maximalSplit ζ (fine.boundaryCocharacterInTorus hx hstrict)).1.mpr
  intro α hα hnn
  exact (hζ.root_pairing_implications_of_subset fine.data.i fine.data.ν
    fine.isCompatible.generic
    (relativeRootNegation k G hG fine.data.T fine.data.i fine.isCompatible.maximalSplit)
    (fine.isStandard_boundaryCocharacterInTorus hx hstrict)
    ((fine.selectedRoots_subset_boundaryRootIndex hx).trans
      (fine.boundaryRootIndex_subset_boundaryCocharacterFace hx hstrict)) hα).1 hnn

include hG in
/-- The resulting dynamic parabolic is proper: its positive simple-root
pairing excludes the corresponding negative root. -/
theorem boundaryCocharacter_parabolic_ne_top {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) (hstrict : x ∉ fine.positiveCone) :
    Dynamic.parabolic
      (CommGroupScheme.groupHom (fine.boundaryCocharacterInTorus hx hstrict) ≫
        fine.data.i) ≠ ⊤ := by
  intro htop
  obtain ⟨α, hα, hpos⟩ := fine.boundaryCocharacterInTorus_positive hx hstrict
  have hle : Dynamic.parabolic (CommGroupScheme.groupHom (-fine.data.ν) ≫ fine.data.i) ≤
      Dynamic.parabolic
        (CommGroupScheme.groupHom (fine.boundaryCocharacterInTorus hx hstrict) ≫
          fine.data.i) := by
    rw [htop]
    intro T
    exact le_top
  have hnegroot := relativeRootNegation k G hG fine.data.T fine.data.i
    fine.isCompatible.maximalSplit α hα.1.1
  have hnn : 0 ≤ latticePairing fine.data.T (-α) (-fine.data.ν) := by
    simpa using hα.1.2.le
  have h := (relativeRootSignInclusions k G hG fine.data.T fine.data.i
    fine.isCompatible.maximalSplit (-fine.data.ν)
    (fine.boundaryCocharacterInTorus hx hstrict)).1.mp hle (-α) hnegroot hnn
  simp only [map_neg, LinearMap.neg_apply] at h
  omega

end Langlands.GroupScheme.ParabolicRootPresentation
