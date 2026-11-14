import Langlands.Sheaf.Renard.ProjectorStalkStatements
import Langlands.Sheaf.Renard.BasisStalkRepresentatives
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Proof of Renard's original-module stalk description -/

noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Langlands.Algebra Langlands.HarmonicAnalysis

universe u v

namespace Langlands.Sheaf.Renard.ProjectorStalk

open ProjectorBasisSheaf ProjectorVectorSheaf

section IndependentUniverses

variable {X : Type u} [TopologicalSpace X]
  (hX : Langlands.Topology.IsLocallyProfinite X)
  {M : Type v} [AddCommGroup M]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
  (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M)

/-- A witness test can be normalized on a compact-open neighborhood. -/
theorem annihilatorDescription : AnnihilatorDescription hX hM := by
  let _ := originalModule hM
  intro x m
  rw [mem_annihilatorSubmodule]
  constructor
  · rintro ⟨f, hfx, hfm⟩
    let V : Opens X := ⟨{y | f y = f x}, (PointwiseTestAlgebra.locallyConstant f).isOpen_fiber _⟩
    obtain ⟨U, hxU, hUV⟩ := (compactOpenBasis hX).exists_subset V (x := x) rfl
    let g : PointwiseTestAlgebra.Carrier X := (f x)⁻¹ • test hX U
    have hgf : g * f = test hX U := by
      ext y
      by_cases hy : y ∈ U.obj
      · have hfy : f y = f x := hUV hy
        simp [g, test, PointwiseTestAlgebra.characteristic_apply, hy, hfy, hfx]
      · simp [g, test, PointwiseTestAlgebra.characteristic_apply, hy]
    refine ⟨U, hxU, ?_⟩
    rw [map_zero]
    change NonUnitalModuleCorner.originalAction (test hX U) m = 0
    rw [← hgf, NonUnitalModuleCorner.originalAction_mul]
    change g • (f • m) = 0
    rw [hfm, smul_zero]
  · rintro ⟨U, hxU, hm⟩
    refine ⟨test hX U, ?_, ?_⟩
    · simp [test, PointwiseTestAlgebra.characteristic_apply, hxU]
    · exact hm.trans (map_zero _)

private def chosenNeighborhood (x : X) : {U : CompactOpen hX // x ∈ U.obj} :=
  let h := (compactOpenBasis hX).exists_subset ⊤ (x := x) (by trivial)
  ⟨h.choose, h.choose_spec.1⟩

/-- Germ of an original vector in the actual compact-open basis colimit. -/
def basisOriginalGerm (x : X) : M →+ rawStalk (rawPresheaf hX M) x :=
  (rawGerm (rawPresheaf hX M) (chosenNeighborhood hX x).val x
    (chosenNeighborhood hX x).property).comp
      (NonUnitalModuleCorner.projection (idempotent hX (chosenNeighborhood hX x).val))

/-- Every compact-open neighborhood gives the same original-vector germ. -/
theorem basisOriginalGerm_eq (x : X) (U : CompactOpen hX) (hxU : x ∈ U.obj) (m : M) :
    basisOriginalGerm hX x m = rawGerm (rawPresheaf hX M) U x hxU
      (NonUnitalModuleCorner.projection (idempotent hX U) m) := by
  let V := (chosenNeighborhood hX x).val
  change rawGerm (rawPresheaf hX M) V x _ _ = _
  apply (rawGerm_eq_iff (rawPresheaf hX M) x V U _ hxU _ _).mpr
  refine ⟨interOpen hX V U, ⟨(chosenNeighborhood hX x).property, hxU⟩,
    inf_le_left, inf_le_right, ?_⟩
  apply Subtype.ext
  change action hX M (interOpen hX V U) (action hX M V m) =
    action hX M (interOpen hX V U) (action hX M U m)
  rw [action_absorb hX M inf_le_left, action_absorb hX M inf_le_right]

/-- Equality in the basis colimit is exactly agreement of neighborhood projectors. -/
theorem basisOriginalGerm_eq_iff (x : X) (m n : M) :
    basisOriginalGerm hX x m = basisOriginalGerm hX x n ↔
      SameProjectorGerm hX x m n := by
  let U := (chosenNeighborhood hX x).val
  have hxU : x ∈ U.obj := (chosenNeighborhood hX x).property
  rw [basisOriginalGerm_eq hX x U hxU m, basisOriginalGerm_eq hX x U hxU n]
  constructor
  · intro h
    obtain ⟨W, hxW, hWU, _, heq⟩ :=
      (rawGerm_eq_iff (rawPresheaf hX M) x U U hxU hxU _ _).mp h
    refine ⟨W, hxW, ?_⟩
    have hv := congrArg Subtype.val heq
    change action hX M W (action hX M U m) = action hX M W (action hX M U n) at hv
    simpa only [action_absorb hX M hWU] using hv
  · rintro ⟨W, hxW, heq⟩
    rw [← basisOriginalGerm_eq hX x U hxU m, ← basisOriginalGerm_eq hX x U hxU n,
      basisOriginalGerm_eq hX x W hxW m, basisOriginalGerm_eq hX x W hxW n]
    exact congrArg (rawGerm (rawPresheaf hX M) W x hxW) (Subtype.ext heq)

/-- Basis-stalk germs of original vectors exhaust the actual colimit. -/
theorem basisOriginalGerm_surjective (x : X) : Function.Surjective (basisOriginalGerm hX (M := M) x) := by
  intro t
  obtain ⟨U, hxU, s, hs⟩ := rawStalk_representative (rawPresheaf hX M) x t
  refine ⟨s.val, ?_⟩
  rw [basisOriginalGerm_eq hX x U hxU]
  have hp : NonUnitalModuleCorner.projection (idempotent hX U) s.val = s :=
    Subtype.ext (value_fixed hX M s)
  rw [hp, hs]

/-- The literal annihilator is the additive kernel of the canonical basis germ map. -/
theorem basisOriginalGerm_ker (x : X) :
    letI := originalModule hM
    (annihilatorSubmodule hX hM x).toAddSubgroup =
      (basisOriginalGerm hX (M := M) x).ker := by
  let _ := originalModule hM
  ext m
  change m ∈ annihilatorSubmodule hX hM x ↔ basisOriginalGerm hX x m = 0
  rw [annihilatorDescription hX hM x m, ← map_zero (basisOriginalGerm hX x)]
  exact (basisOriginalGerm_eq_iff hX x m 0).symm

/-- The quotient comparison has the required formula on every compact-open neighborhood. -/
theorem basisStalkComparison : BasisStalkComparison hX hM := by
  let _ := originalModule hM
  intro x
  refine ⟨QuotientAddGroup.liftEquiv (annihilatorSubmodule hX hM x).toAddSubgroup
    (basisOriginalGerm_surjective hX x) (basisOriginalGerm_ker hX hM x), ?_⟩
  intro U hxU m
  exact basisOriginalGerm_eq hX x U hxU m

end IndependentUniverses

section VectorStalk

/- Mathlib's instance uses the scalar universe for the module universe. Its
explicit filtered-colimit cocone also handles small scalars in arbitrary `u`. -/
private instance complexForget₂PreservesFilteredColimits :
    Limits.PreservesFilteredColimits (forget₂ (ModuleCat.{u} ℂ) AddCommGrpCat.{u}) where
  preserves_filtered_colimits _ _ _ :=
    { preservesColimit := fun {F} =>
        Limits.preservesColimit_of_preserves_colimit_cocone
          (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
          (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ (ModuleCat.{u} ℂ) AddCommGrpCat.{u})) }

private instance complexForgetPreservesFilteredColimits :
    Limits.PreservesFilteredColimits (forget (ModuleCat.{u} ℂ)) :=
  Limits.comp_preservesFilteredColimits (forget₂ (ModuleCat.{u} ℂ) AddCommGrpCat.{u})
    (forget AddCommGrpCat.{u})

variable {X : Type u} [TopologicalSpace X]
  (hX : Langlands.Topology.IsLocallyProfinite X)
  {M : Type u} [AddCommGroup M]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
  (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M)

/-- The original-vector germ can be computed on every open neighborhood. -/
theorem originalGerm_eq (x : X) (U : Opens X) (hxU : x ∈ U) (m : M) :
    originalGerm hX hM x m =
      (presheaf.{u,u} hX hM).germ U x hxU (originalSection.{u,u} hX hM U m) := by
  let _ := originalModule hM
  exact (TopCat.Presheaf.Γgerm_res_apply (presheaf.{u,u} hX hM)
    (U := U) (i := homOfLE le_top) x hxU (originalSection.{u,u} hX hM ⊤ m)).symm

/-- Equality in the all-open stalk is agreement after a compact-open projector. -/
theorem originalGerm_eq_iff (x : X) (m n : M) :
    originalGerm hX hM x m = originalGerm hX hM x n ↔
      SameProjectorGerm hX x m n := by
  let _ := originalModule hM
  constructor
  · intro h
    obtain ⟨W, hxW, iWm, iWn, heq⟩ :=
      TopCat.Presheaf.germ_eq (presheaf.{u,u} hX hM) x (by trivial) (by trivial)
        (originalSection.{u,u} hX hM ⊤ m) (originalSection.{u,u} hX hM ⊤ n) h
    obtain ⟨K, hxK, hKW⟩ := (compactOpenBasis hX).exists_subset W hxW
    refine ⟨K, hxK, ?_⟩
    exact congrArg (fun s : (presheaf.{u,u} hX hM).obj (op W) =>
      (s.val ⟨K, hKW⟩).val) heq
  · rintro ⟨K, hxK, hK⟩
    rw [originalGerm_eq hX hM x K.obj hxK m, originalGerm_eq hX hM x K.obj hxK n]
    apply congrArg ((presheaf.{u,u} hX hM).germ K.obj x hxK)
    apply section_ext.{u,u} hX hM
    intro U
    change action hX M U.val m = action hX M U.val n
    rw [← action_absorb hX M U.property m, ← action_absorb hX M U.property n, hK]

/-- Every actual vector-sheaf stalk element comes from an original module vector. -/
theorem originalGerm_surjective (x : X) :
    Function.Surjective (originalGerm hX hM x) := by
  let _ := originalModule hM
  intro t
  obtain ⟨U, hxU, s, hs⟩ :=
    TopCat.Presheaf.exists_germ_eq (presheaf.{u,u} hX hM) t
  obtain ⟨K, hxK, hKU⟩ := (compactOpenBasis hX).exists_subset U hxU
  refine ⟨(s.val ⟨K, hKU⟩).val, ?_⟩
  rw [originalGerm_eq hX hM x K.obj hxK, ← hs,
    ← TopCat.Presheaf.germ_res_apply (presheaf.{u,u} hX hM) (homOfLE hKU) x hxK s]
  apply congrArg ((presheaf.{u,u} hX hM).germ K.obj x hxK)
  apply section_ext.{u,u} hX hM
  intro W
  exact (congrArg Subtype.val (section_compatible.{u,u} hX hM s
    ⟨K, hKU⟩ ⟨W.val, W.property.trans hKU⟩ W.property))

/-- The actual complex-linear germ kernel is Renard's literal annihilator. -/
theorem originalGerm_ker (x : X) :
    letI := originalModule hM
    LinearMap.ker (originalGerm hX hM x) = annihilatorSubmodule hX hM x := by
  let _ := originalModule hM
  ext m
  change originalGerm hX hM x m = 0 ↔ m ∈ annihilatorSubmodule hX hM x
  rw [← map_zero (originalGerm hX hM x), originalGerm_eq_iff hX hM,
    annihilatorDescription hX hM]

/-- The canonical complex-linear quotient comparison for the actual all-open stalk. -/
theorem vectorStalkComparison : VectorStalkComparison hX hM := by
  let _ := originalModule hM
  intro x
  refine ⟨(Submodule.quotEquivOfEq _ _ (originalGerm_ker hX hM x).symm).trans
    (LinearMap.quotKerEquivOfSurjective (originalGerm hX hM x)
      (originalGerm_surjective hX hM x)), ?_⟩
  intro m
  rfl

end VectorStalk

/-- Renard II.2.5, original-module stalk description with both universe parameters. -/
theorem projectorStalkDescription : ProjectorStalkDescription.{u,v} := by
  constructor
  · intro X _ hX M _ _ hM
    exact ⟨annihilatorDescription hX hM, basisStalkComparison hX hM⟩
  · intro X _ hX M _ _ hM
    exact ⟨originalGerm_surjective hX hM, originalGerm_ker hX hM,
      originalGerm_eq_iff hX hM, vectorStalkComparison hX hM⟩

end Langlands.Sheaf.Renard.ProjectorStalk
