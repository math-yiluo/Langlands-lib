import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalChamber
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCartanCellHeight
import Langlands.Representation.Plancherel.SplitTorusCompactKernel

/-! # Height control on the full minimal chamber in the norm kernel

The uniformizer section is used only inside the proof. All conclusions apply
to arbitrary actual points of the maximal split torus.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Plancherel
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.Cartan

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

/-- Root-valuation bounds control the height of every torus point in `G¹`.
Neither a Cartan covering nor a compact-adapted height is assumed. -/
theorem exists_one_add_rationalHeight_le_of_simpleRootOrders
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) :
    ∃ C > 0, ∀ (a : rationalPoints S.toGrp) (T : ℝ), 0 ≤ T →
      (∀ β ∈ simpleRelativeRoots i ν,
        |(RenardLeviCones.characterOrder S β a : ℝ)| ≤ T) →
      rationalPoints.map i a ∈ rationalCommonNormKernel G →
        1 + rationalHeight (F := F) ρ (rationalPoints.map i a) ≤ C * (1 + T) := by
  classical
  let : IsAffineHom S.X.hom := hi.isSplitSubtorus.1.isAffineHom
  let K0 : Subgroup (rationalPoints G) :=
    (rationalCommonNormKernel S.toGrp).map (rationalPoints.map i)
  have hK0 : IsCompact (K0 : Set (rationalPoints G)) := by
    change IsCompact (rationalPoints.map i ''
      (rationalCommonNormKernel S.toGrp : Set (rationalPoints S.toGrp)))
    exact (SplitTorus.isCompact_commonNormKernel hi.isSplitSubtorus.1).image
      (continuous_rationalPointMap F i.hom.hom)
  obtain ⟨B, hB⟩ := exists_rationalHeight_le_of_mem_rationalCartanCell hG hi hν hK0
    ({1} : Finset (centralizerPoints i)) ρ
  refine ⟨|B| + 1, by positivity, fun a T hT hroot hker => ?_⟩
  obtain ⟨c, hc, -⟩ :=
    (CocharacterUniformizer.isUniformizerLatticeSection F S hi.isSplitSubtorus.1).2.2 a
  have hval := (CocharacterUniformizer.mem_normKernel_mul_section_inv_iff F S a c).mp hc
  have hbound : ∀ β : Aubert.General.RationalPointFamily.SimpleRoot i ν,
      |(Aubert.General.simpleRootPairing i ν β c.toAdd : ℝ)| ≤ T := by
    intro β
    change |(latticePairing S β.1 c.toAdd : ℝ)| ≤ T
    rw [← hval β.1]
    exact hroot β.1 β.2
  have hcell : rationalPoints.map i a ∈
      rationalCartanCell i K0 ({1} : Finset (centralizerPoints i)) c.toAdd := by
    refine ⟨rationalPoints.map i (a * (CocharacterUniformizer.latticeSection F S c)⁻¹),
      ⟨_, hc, rfl⟩, 1, K0.one_mem, 1, by simp, ?_⟩
    simp only [Aubert.General.uniformizerPowers, MonoidHom.comp_apply,
      RenardCartan.uniformizerSection_eq_latticeSection, map_mul, map_inv,
      OneMemClass.coe_one, mul_one]
    change rationalPoints.map i a = rationalPoints.map i a *
      (rationalPoints.map i (CocharacterUniformizer.latticeSection F S c))⁻¹ *
        rationalPoints.map i (CocharacterUniformizer.latticeSection F S c)
    group
  have hb := hB c.toAdd T hT hbound _ hcell hker
  have hBT : B * (1 + T) ≤ |B| * (1 + T) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  nlinarith

/-- Source inequality (1) in the sector where the chosen simple-root
valuation dominates all the others. The constant is uniform over the root. -/
theorem exists_one_add_rationalHeight_le_of_maximal_simpleRootOrder
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) :
    ∃ C > 0, ∀ α ∈ simpleRelativeRoots i ν, ∀ a : rationalPoints S.toGrp,
      (∀ β ∈ simpleRelativeRoots i ν,
        0 ≤ RenardLeviCones.characterOrder S β a ∧
          RenardLeviCones.characterOrder S β a ≤ RenardLeviCones.characterOrder S α a) →
      rationalPoints.map i a ∈ rationalCommonNormKernel G →
        1 + rationalHeight (F := F) ρ (rationalPoints.map i a) ≤
          C * (1 + (RenardLeviCones.characterOrder S α a : ℝ)) := by
  obtain ⟨C, hC, h⟩ := exists_one_add_rationalHeight_le_of_simpleRootOrders hG hi hν ρ
  refine ⟨C, hC, fun α hα a ha hker => h a _ ?_ ?_ hker⟩
  · exact_mod_cast (ha α hα).1
  · intro β hβ
    rw [abs_of_nonneg (by exact_mod_cast (ha β hβ).1)]
    exact_mod_cast (ha β hβ).2

/-- The part of the full chamber in `G¹` where `α` has largest root order.
The torus parameter is an arbitrary actual point. -/
def rationalMinimalRootSector (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (α : characterLattice S) : Set (rationalPoints G) :=
  {g | α ∈ simpleRelativeRoots i ν ∧ g ∈ rationalCommonNormKernel G ∧
    ∃ a : rationalPoints S.toGrp, rationalPoints.map i a = g ∧
      ∀ β ∈ simpleRelativeRoots i ν,
        0 ≤ RenardLeviCones.characterOrder S β a ∧
          RenardLeviCones.characterOrder S β a ≤ RenardLeviCones.characterOrder S α a}

omit [LocallyOfFiniteType G.X.hom] in
/-- Each root sector is contained in the full norm-kernel chamber. -/
theorem rationalMinimalRootSector_subset (α : characterLattice S) :
    rationalMinimalRootSector i ν α ⊆ rationalMinimalChamberInNormKernel i ν := by
  rintro g ⟨_, hg, a, rfl, ha⟩
  exact ⟨(mem_rationalMinimalChamber_iff_order i ν _).mpr
    ⟨a, rfl, fun β hβ => (ha β hβ).1⟩, hg⟩

omit [LocallyOfFiniteType G.X.hom] in
/-- With at least one simple root, finitely many maximal-root sectors cover
the full chamber in `G¹`. No genericity hypothesis is needed for this cover. -/
theorem exists_rationalMinimalRootSector_cover
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hne : (simpleRelativeRoots i ν).Nonempty) :
    ∃ R : Finset (characterLattice S),
      (R : Set (characterLattice S)) = simpleRelativeRoots i ν ∧
        rationalMinimalChamberInNormKernel i ν =
          ⋃ α ∈ R, rationalMinimalRootSector i ν α := by
  classical
  have := hi.isSplitSubtorus.mono
  have hf := (relativeRootSystem F G hG S i hi).finite_simpleRelativeRoots
    i hi.isSplitSubtorus.1 ν
  refine ⟨hf.toFinset, hf.coe_toFinset, ?_⟩
  ext g
  simp only [Set.mem_iUnion]
  constructor
  · intro hg
    obtain ⟨a, rfl, ha⟩ := (mem_rationalMinimalChamber_iff_order i ν g).mp hg.1
    have hne' : hf.toFinset.Nonempty := by
      obtain ⟨α, hα⟩ := hne
      exact ⟨α, by simpa using hα⟩
    obtain ⟨α, hα, hmax⟩ := Finset.exists_max_image hf.toFinset
      (fun β => RenardLeviCones.characterOrder S β a) hne'
    exact ⟨α, hα, by simpa using hα, hg.2, a, rfl,
      fun β hβ => ⟨ha β hβ, hmax β (by simpa using hβ)⟩⟩
  · rintro ⟨α, _, hg⟩
    exact rationalMinimalRootSector_subset α hg

/-- The chamber height constant can be chosen uniformly over every root sector. -/
theorem exists_one_add_rationalHeight_le_on_rootSectors
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) :
    ∃ C > 0, ∀ (α : characterLattice S) (g : rationalPoints G),
      g ∈ rationalMinimalRootSector i ν α →
        ∃ a : rationalPoints S.toGrp, rationalPoints.map i a = g ∧
          1 + rationalHeight (F := F) ρ g ≤
            C * (1 + (RenardLeviCones.characterOrder S α a : ℝ)) := by
  obtain ⟨C, hC, h⟩ :=
    exists_one_add_rationalHeight_le_of_maximal_simpleRootOrder hG hi hν ρ
  refine ⟨C, hC, ?_⟩
  rintro α g ⟨hα, hg, a, rfl, ha⟩
  exact ⟨a, rfl, h α hα a ha hg⟩

/-- With no simple roots, the full chamber in `G¹` is compact. Closedness of
the matrix representation is used only to make height sublevels compact. -/
theorem isCompact_rationalMinimalChamberInNormKernel_of_simpleRoots_empty
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {N : ℕ} [Nonempty (Fin N)]
    (ρ : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup ρ)
    (h0 : simpleRelativeRoots i ν = ∅) :
    IsCompact (rationalMinimalChamberInNormKernel i ν) := by
  let : IsAffineHom S.X.hom := hi.isSplitSubtorus.1.isAffineHom
  let : IsClosedImmersion i.hom.hom.left := hi.isSplitSubtorus.2
  have hrange : IsClosed (Set.range (rationalPoints.map i)) :=
    (isClosedEmbedding_rationalPointMap F i.hom.hom).isClosed_range
  have hclosed : IsClosed (rationalMinimalChamberInNormKernel i ν) := by
    rw [rationalMinimalChamberInNormKernel,
      rationalMinimalChamber_eq_range_of_simpleRoots_empty i ν h0]
    exact hrange.inter (isClosed_rationalCommonNormKernel G)
  obtain ⟨C, _, hC⟩ := exists_one_add_rationalHeight_le_of_simpleRootOrders hG hi hν ρ
  apply (isCompact_rationalHeight_le ρ hρ C).of_isClosed_subset hclosed
  intro g hg
  obtain ⟨a, rfl, _⟩ := (mem_rationalMinimalChamber_iff_order i ν g).mp hg.1
  have h := hC a 0 le_rfl (by simp [h0]) hg.2
  change rationalHeight (F := F) ρ (rationalPoints.map i a) ≤ C
  nlinarith

/-- Closed summary of the chamber-height input: absolute root-order control,
finite sector coverage when roots exist, and compactness in the empty case. -/
def RationalMinimalChamberHeightStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)),
      (∃ C > 0, ∀ (a : rationalPoints S.toGrp) (T : ℝ), 0 ≤ T →
        (∀ β ∈ simpleRelativeRoots i ν,
          |(RenardLeviCones.characterOrder S β a : ℝ)| ≤ T) →
        rationalPoints.map i a ∈ rationalCommonNormKernel G →
          1 + rationalHeight (F := F) ρ (rationalPoints.map i a) ≤ C * (1 + T)) ∧
      ((simpleRelativeRoots i ν).Nonempty →
        ∃ R : Finset (characterLattice S),
          (R : Set (characterLattice S)) = simpleRelativeRoots i ν ∧
            rationalMinimalChamberInNormKernel i ν =
              ⋃ α ∈ R, rationalMinimalRootSector i ν α) ∧
      (IsClosedSubgroup ρ → simpleRelativeRoots i ν = ∅ →
        IsCompact (rationalMinimalChamberInNormKernel i ν))

/-- The full chamber-height input holds with the original arbitrary choices. -/
theorem rationalMinimalChamberHeight : RationalMinimalChamberHeightStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν N _ ρ
  exact ⟨exists_one_add_rationalHeight_le_of_simpleRootOrders hG hi hν ρ,
    exists_rationalMinimalRootSector_cover hG hi,
    isCompact_rationalMinimalChamberInNormKernel_of_simpleRoots_empty hG hi hν ρ⟩

end Langlands.HarishChandraSchwartz
