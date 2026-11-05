import Langlands.HarmonicAnalysis.TorusLatticeDuality
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterCoordinates
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.Representation.Plancherel.RationalRestrictionKernel

/-! # Lattice coordinates on `G(F)` and the restriction kernel in torus coordinates

For `G` connected reductive over a nonarchimedean local field, the Library's circle coordinates
`Im X(G) ≃ (Fin r → Circle)` write a unitary unramified character as `χ(g) = ∏ᵢ zᵢ^{n(g)ᵢ}`,
where `n(g) ∈ ℤ^r` are the coordinates of the valuation image of `g`. This module defines `n`,
proves that it is a continuous homomorphism with this character formula, and identifies, for a
central `s : T → G`, the kernel of the restriction `Im X(G) → Im X(T)` with the annihilator of
the lattice `Λ_s = n(s(T(F)))`, which has finite index when the split valuation image does.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.HarmonicAnalysis.TorusFourier
open scoped CategoryTheory.MonObj

namespace Langlands.HarishChandraSchwartz

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance instRationalValuationCoordinates1 :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

variable (hG : GroupScheme.IsConnectedReductive G)

/-- The coordinate isomorphism `Λ(G) ≃ ℤ^r` of the valuation image lattice given by
`rationalReductiveValuationBasis`. -/
def rationalValuationLatticeEquiv :
    Additive (rationalDiscreteValuationImage G) ≃+ (Fin (rationalImageRank G) → ℤ) :=
  (rationalReductiveValuationBasis G hG).repr.toAddEquiv.trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin (rationalImageRank G))).toAddEquiv

/-- The lattice coordinates `n(g) ∈ ℤ^r` of `g ∈ G(F)`: the coordinates of the valuation image
of `g` in the chosen basis `rationalReductiveValuationBasis` of the image lattice. -/
def rationalValuationCoordinates (g : GroupScheme.rationalPoints G) :
    Fin (rationalImageRank G) → ℤ :=
  rationalValuationLatticeEquiv G hG (Additive.ofMul (rationalValuationImageProjection G g))

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem rationalValuationCoordinates_apply (g : GroupScheme.rationalPoints G)
    (i : Fin (rationalImageRank G)) :
    rationalValuationCoordinates G hG g i =
      (rationalReductiveValuationBasis G hG).repr
        (Additive.ofMul (rationalValuationImageProjection G g)) i :=
  rfl

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem rationalValuationCoordinates_mul (g h : GroupScheme.rationalPoints G) :
    rationalValuationCoordinates G hG (g * h) =
      rationalValuationCoordinates G hG g + rationalValuationCoordinates G hG h := by
  simp only [rationalValuationCoordinates, map_mul, ofMul_mul, map_add]

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem rationalValuationCoordinates_one :
    rationalValuationCoordinates G hG 1 = 0 := by
  simp [rationalValuationCoordinates]

/-- `n` is locally constant: it factors through the discrete valuation image. -/
theorem continuous_rationalValuationCoordinates :
    Continuous (rationalValuationCoordinates G hG) :=
  (continuous_of_discreteTopology (f := fun x : rationalDiscreteValuationImage G =>
    rationalValuationLatticeEquiv G hG (Additive.ofMul x))).comp
    (continuous_rationalValuationImageProjection G)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The value of the unitary unramified character with circle coordinates `z` at `g` is the
torus character `∏ᵢ zᵢ^{n(g)ᵢ}`. -/
theorem rationalUnitaryUnramifiedCharacter_apply (z : Fin (rationalImageRank G) → Circle)
    (g : GroupScheme.rationalPoints G) :
    ((((rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).symm z).val g : ℂˣ) : ℂ) =
      torusCharacter (rationalValuationCoordinates G hG g) z := by
  rw [rationalCanonicalUnitaryUnramifiedCharacterCoordinates_symm_apply, torusCharacter]
  exact map_prod Circle.coeHom _ _

theorem measurable_rationalValuationCoordinates [MeasurableSpace (GroupScheme.rationalPoints G)]
    [OpensMeasurableSpace (GroupScheme.rationalPoints G)] :
    Measurable (rationalValuationCoordinates G hG) :=
  (continuous_rationalValuationCoordinates G hG).measurable

section SplitLattice

variable {G} {T : CommGroupScheme (Spec (CommRingCat.of F))} (s : T.toGrp ⟶ G)

/-- The lattice `Λ_s = {n(s(t)) | t ∈ T(F)} ⊆ ℤ^r` of a homomorphism `s : T → G`: the split
valuation image `RenardCartan.splitValuationImage s` in the coordinates of `Λ(G)`. -/
def rationalSplitLattice : AddSubgroup (Fin (rationalImageRank G) → ℤ) :=
  (Subgroup.toAddSubgroup (RenardCartan.splitValuationImage s :
      Subgroup (rationalDiscreteValuationImage G))).comap
    (rationalValuationLatticeEquiv G hG).symm.toAddMonoidHom

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem mem_rationalSplitLattice {m : Fin (rationalImageRank G) → ℤ} :
    m ∈ rationalSplitLattice hG s ↔
      ∃ t : GroupScheme.rationalPoints T.toGrp,
        rationalValuationCoordinates G hG (GroupScheme.rationalPoints.map s t) = m := by
  constructor
  · intro hm
    obtain ⟨t, ht⟩ := hm
    refine ⟨t, ?_⟩
    have h : Additive.ofMul (rationalValuationImageProjection G (GroupScheme.rationalPoints.map s t)) =
        (rationalValuationLatticeEquiv G hG).symm m :=
      congrArg Additive.ofMul ht
    rw [rationalValuationCoordinates, h, AddEquiv.apply_symm_apply]
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    change rationalValuationImageProjection G (GroupScheme.rationalPoints.map s t) =
      Additive.toMul ((rationalValuationLatticeEquiv G hG).symm
        (rationalValuationLatticeEquiv G hG
          (Additive.ofMul (rationalValuationImageProjection G (GroupScheme.rationalPoints.map s t)))))
    rw [AddEquiv.symm_apply_apply]
    rfl

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- `Λ_s` has finite index when the split valuation image has finite index in `Λ(G)`. -/
theorem finiteIndex_rationalSplitLattice
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    (rationalSplitLattice hG s).FiniteIndex := by
  refine ⟨?_⟩
  have h := AddSubgroup.index_comap_of_surjective
    (H := Subgroup.toAddSubgroup (RenardCartan.splitValuationImage s :
      Subgroup (rationalDiscreteValuationImage G)))
    (f := (rationalValuationLatticeEquiv G hG).symm.toAddMonoidHom)
    (rationalValuationLatticeEquiv G hG).symm.surjective
  exact fun h0 => hindex.index_ne_zero (h.symm.trans h0)

omit [LocallyOfFiniteType G.X.hom] in
/-- **The restriction kernel in torus coordinates**: the unitary unramified character with
circle coordinates `z` is trivial on `s(T(F))` if and only if `z` annihilates `Λ_s`. -/
theorem coordinates_symm_mem_restrict_ker_iff [IsAffine T.X.left]
    (z : Fin (rationalImageRank G) → Circle) :
    (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).symm z ∈
        (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker ↔
      z ∈ latticeAnnihilator (rationalSplitLattice hG s) := by
  rw [mem_rationalUnitaryUnramifiedCharacterRestrict_ker, mem_latticeAnnihilator]
  constructor
  · intro h m hm
    obtain ⟨t, rfl⟩ := (mem_rationalSplitLattice hG s).mp hm
    rw [← rationalUnitaryUnramifiedCharacter_apply, h t, Units.val_one]
  · intro h t
    apply Units.ext
    rw [rationalUnitaryUnramifiedCharacter_apply, Units.val_one]
    exact h _ ((mem_rationalSplitLattice hG s).mpr ⟨t, rfl⟩)

end SplitLattice

end Langlands.HarishChandraSchwartz
