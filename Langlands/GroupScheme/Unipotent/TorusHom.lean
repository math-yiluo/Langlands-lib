import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.Unipotent.SplitTorusHom
import Langlands.GroupScheme.Absolute.CocharacterDescentGroup

/-! # Homomorphisms from tori to unipotent group schemes are trivial -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {S U : GroupScheme (Spec (CommRingCat.of k))}

/-- Every homomorphism from a torus to an affine unipotent group scheme over a field is
trivial. -/
theorem IsTorus.hom_eq_zero_of_isUnipotent [IsAffineHom U.X.hom] (hS : IsTorus S)
    (hU : IsUnipotent U) (j : S ⟶ U) : j = 0 := by
  obtain ⟨K, _, _, hSK⟩ := hS
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : IsAffineHom ((GroupScheme.baseChange b).obj U).X.hom := by
    change IsAffineHom (pullback.snd U.X.hom b)
    infer_instance
  have : IsAffine ((GroupScheme.baseChange b).obj U).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange b).obj U).X.hom
  have h := hSK.hom_eq_zero_of_isUnipotent (hU.baseChange (K := K))
    ((GroupScheme.baseChange b).map j)
  have := GaloisCocharacterDescent.faithful_algebraPullback k K
  apply (Grp.forget _).map_injective
  change j.hom.hom = (1 : S.X ⟶ U.X)
  apply (Over.pullback b).map_injective
  rw [Functor.map_one]
  exact congrArg (fun f => f.hom.hom) h

/-- The image of a homomorphism from a torus to an affine unipotent group scheme over a field
is trivial on every test scheme. -/
theorem IsUnipotent.range_eq_bot_of_isTorus [IsAffineHom U.X.hom] (hU : IsUnipotent U)
    (hS : IsTorus S) (j : S ⟶ U) : SubgroupFunctor.range j = ⊥ := by
  rw [hS.hom_eq_zero_of_isUnipotent hU j, SubgroupFunctor.range_zero]

end Langlands.GroupScheme
