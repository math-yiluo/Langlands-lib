import Langlands.GroupScheme.IntegralModel.SplitTorusConjugacy
import Langlands.GroupScheme.Torus.UnipotentQuotientMaximalSplit

/-! # Generic maximality from a residue-maximal split torus and a reference -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  {T T' : CommGroupScheme (Spec (CommRingCat.of R))}
  {i : T.toGrp ⟶ M.group} {i' : T'.toGrp ⟶ M.group}

/-- The actual generic conjugacy square preserves maximal split tori. -/
theorem SplitTorusConjugator.isMaximalSplitTorus_generic_iff
    (A : SplitTorusConjugator i i') :
    IsMaximalSplitTorus (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T)
        (M.genericHom i) ↔
      IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T')
        (M.genericHom i') := by
  let e := (CommGroupScheme.baseChange (Spec.algebraMap R K)).mapIso A.torusIso
  let eG : ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T).toGrp ≅
      ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T').toGrp :=
    { hom := CommGroupScheme.groupHom e.hom
      inv := CommGroupScheme.groupHom e.inv
      hom_inv_id := congrArg Additive.toMul e.hom_inv_id
      inv_hom_id := congrArg Additive.toMul e.inv_hom_id }
  exact (show SubgroupConjugate (M.genericHom i) (M.genericHom i') from
    ⟨A.genericPoint M, eG, A.generic_comm M⟩).isMaximalSplitTorus_iff

namespace IntegralModel

variable [HenselianLocalRing R]
  {k : Type u} [Field k] [Algebra R k]

/-- Conjugate a residue-maximal integral split torus to a closed reference
integral split torus already maximal in the specified generic group. -/
def henselianSplitTorusConjugatorOfResidueGeneric
    (hM : M.IsSmooth) (hk : Function.Surjective (algebraMap R k))
    (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    [ConnectedSpace ((baseChange (Spec.algebraMap R k)).obj M.group).X.left]
    (hi' : IsClosedSubgroup i')
    (hik : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T)
      ((baseChange (Spec.algebraMap R k)).map i))
    (hi'K : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T')
      (M.genericHom i')) : SplitTorusConjugator i i' := by
  let : Smooth M.group.X.hom := hM
  exact Langlands.GroupScheme.henselianSplitTorusConjugatorOfResidue
    i i' hM hk hT hT' hik
    (isMaximalSplitTorus_residue_of_generic hk M.group (hG.of_iso M.genericIso)
      T' hT' i' hi' ((IsMaximalSplitTorus.comp_iso_iff _ M.genericIso).mp hi'K))

/-- Residue maximality implies generic maximality in the presence of a
closed split reference torus maximal in the generic connected reductive group. -/
theorem isMaximalSplitTorus_generic_of_residue_of_reference
    (hM : M.IsSmooth) (hk : Function.Surjective (algebraMap R k))
    (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    [ConnectedSpace ((baseChange (Spec.algebraMap R k)).obj M.group).X.left]
    (hi' : IsClosedSubgroup i')
    (hik : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T)
      ((baseChange (Spec.algebraMap R k)).map i))
    (hi'K : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T')
      (M.genericHom i')) :
    IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T)
      (M.genericHom i) := by
  let A := M.henselianSplitTorusConjugatorOfResidueGeneric
    hM hk hG hT hT' hi' hik hi'K
  exact (A.isMaximalSplitTorus_generic_iff M).mpr hi'K

end IntegralModel

end Langlands.GroupScheme
