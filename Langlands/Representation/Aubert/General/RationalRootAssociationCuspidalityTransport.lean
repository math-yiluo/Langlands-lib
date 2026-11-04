import Langlands.Representation.Aubert.General.RationalRootAssociationLeviTransport
import Langlands.GroupScheme.Rational.StandardRestrictedConjugation
import Langlands.Representation.Aubert.General.CuspidalityTransport

/-! # Actual cuspidal transport from root association -/

noncomputable section

set_option maxHeartbeats 1600000

universe u v uG uH

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.SmoothRep

/-- The same-carrier smooth pullback preserves and reflects irreducibility. -/
theorem isIrreducible_pullbackFunctor_obj_iff
    {A : Type uG} [Group A] [TopologicalSpace A]
    {B : Type uH} [Group B] [TopologicalSpace B]
    (e : B ≃ₜ* A) (σ : SmoothRep.{0, uG, v} ℂ A) :
    ((pullbackFunctor e).obj σ).IsIrreducible ↔ σ.IsIrreducible :=
  isIrreducible_comp_continuousMulEquiv_iff σ.representation e

end Langlands.SmoothRep

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})

include hG hi hν hStandard in
/-- Within the associated parent Levi, the original normalizer representative
matches the actual parabolic and unipotent tests for every descendant subset. -/
theorem rootAssociation_restrictedParabolic_unipotent_mem
    {I J : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (hIJ : rootAssociation i ν hN hZ I J n) (K : Finset I) (x : levi i ν J) :
    ((x : RationalPoint k G.X) ∈
        parabolic i ν (leviIndex J (rootAssociationFinsetEquiv i ν hN hZ hIJ K)) ↔
      n⁻¹ * (x : RationalPoint k G.X) * n ∈ parabolic i ν (leviIndex I K)) ∧
    ((x : RationalPoint k G.X) ∈
        unipotent i ν (leviIndex J (rootAssociationFinsetEquiv i ν hN hZ hIJ K)) ↔
      n⁻¹ * (x : RationalPoint k G.X) * n ∈ unipotent i ν (leviIndex I K)) := by
  have hfinite : (simpleRelativeRoots i ν).Finite := by
    rw [← rootSet_univ i ν]
    exact rootSet_finite i ν Finset.univ
  have hI0 := (rootSet_subset_iff i ν _ _).mpr (leviIndex_subset I K)
  have hI1 := (rootSet_subset_iff i ν _ _).mpr
    (leviIndex_subset J (rootAssociationFinsetEquiv i ν hN hZ hIJ K))
  have hJ0 := (hStandard k G hG T i hi ν hν
    (rootSet i ν I) (rootSet_subset i ν I)).1
  have hJ1 := (hStandard k G hG T i hi ν hν
    (rootSet i ν J) (rootSet_subset i ν J)).1
  have hI := rootAssociation_character_image i ν hN hZ
    (rootAssociation_leviIndex i ν hN hZ hIJ K)
  have hJ := rootAssociation_character_image i ν hN hZ hIJ
  have h := mem_standardParabolic_unipotent_inv_conj_iff_of_character_images
    i ν hfinite hI0 hI1 hJ0 hJ1
    ((normalizerEquiv i hN).symm ⟨n, Classical.choose hIJ⟩)
    hI hJ (Over.mk (𝟙 _)) (x : RationalPoint k G.X) x.property
  have hnpoint :
      ((normalizerEquiv i hN).symm ⟨n, Classical.choose hIJ⟩ : RationalPoint k G.X) = n :=
    rfl
  simpa only [constantPoint_self, hnpoint] using h

section Topology

variable [TopologicalSpace (RationalPoint k G.X)]
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hInter : StandardLeviIntersectionStatement.{u})
  (hU : ∀ K, IsClosed (unipotent i ν K : Set (RationalPoint k G.X)))
  {I J : Finset (SimpleRoot i ν)}
  (hMI : IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (hMJ : IsClosed (levi i ν J : Set (RationalPoint k G.X)))
  {n : RationalPoint k G.X}
  (hIJ : rootAssociation i ν hN hZ I J n)

/-- Root association preserves the precise inside-Levi cuspidality predicate
under pullback by its original inverse-conjugating representative. -/
theorem isLeviCuspidal_rootAssociation_conjugation_iff
    (σ : SmoothRep.{0, u, v} ℂ (levi i ν I)) :
    IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU J hMJ
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J)
        ((conjugationFunctor n
          (rootAssociation_levi_mem i ν hN hZ hG hi hν hStandard hIJ)).obj σ) ↔
      IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I hMI
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) σ := by
  let := hMI.locallyCompactSpace
  let := hMJ.locallyCompactSpace
  let f := (rootAssociationProperFinsetEquiv i ν hN hZ hIJ).symm
  apply isCuspidalFor_pullback_iff
    (rootAssociationLeviEquiv i ν hN hZ hG hi hν hStandard hIJ) f f.surjective
  · intro K x
    have he :
        rootAssociationFinsetEquiv i ν hN hZ hIJ (f K).val = K.val :=
      congrArg Subtype.val
        ((rootAssociationProperFinsetEquiv i ν hN hZ hIJ).apply_symm_apply K)
    simpa only [he] using rootAssociationLeviEquiv_descendant_mem
      i ν hN hZ hG hi hν hStandard hIJ (f K).val x
  · intro K x
    have he :
        rootAssociationFinsetEquiv i ν hN hZ hIJ (f K).val = K.val :=
      congrArg Subtype.val
        ((rootAssociationProperFinsetEquiv i ν hN hZ hIJ).apply_symm_apply K)
    simpa only [Subgroup.mem_subgroupOf, rootAssociationLeviEquiv_apply, he] using
      (rootAssociation_restrictedParabolic_unipotent_mem
        i ν hN hZ hG hi hν hStandard hIJ (f K).val x).2

/-- An actual irreducible cuspidal datum transported by the given
root-association representative, with no extra matching premise. -/
def rootAssociationConjugateCuspidalDatum
    (σ : {σ : SmoothRep.{0, u, v} ℂ (levi i ν I) //
      σ.IsIrreducible ∧
        IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I hMI
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) σ}) :
    {τ : SmoothRep.{0, u, v} ℂ (levi i ν J) //
      τ.IsIrreducible ∧
        IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU J hMJ
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) τ} :=
  ⟨(conjugationFunctor n
      (rootAssociation_levi_mem i ν hN hZ hG hi hν hStandard hIJ)).obj σ.val,
    (SmoothRep.isIrreducible_pullbackFunctor_obj_iff
      (rootAssociationLeviEquiv i ν hN hZ hG hi hν hStandard hIJ) σ.val).mpr σ.property.1,
    (isLeviCuspidal_rootAssociation_conjugation_iff
      i ν hN hZ hG hi hν hStandard hInter hU hMI hMJ hIJ σ.val).mpr σ.property.2⟩

end Topology

end Langlands.Aubert.General.RationalPointFamily
