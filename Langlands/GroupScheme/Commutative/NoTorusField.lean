import Langlands.GroupScheme.Commutative.SeparablyClosedNoTorus
import Langlands.GroupScheme.Torus.CocharacterFiniteGaloisDescent
import Mathlib.FieldTheory.IsSepClosed

/-! # Commutative groups without tori over arbitrary fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The commutative case of no-torus unipotence over arbitrary fields. -/
def CommutativeNoTorusUnipotentStatement : Prop :=
  ∀ (k : Type u) [Field k] (Z : CommGroupScheme (Spec (CommRingCat.of k)))
    [Smooth Z.toGrp.X.hom] [IsAffineHom Z.toGrp.X.hom]
    [ConnectedSpace Z.toGrp.X.left],
    (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
      ∀ f : T.toGrp ⟶ Z.toGrp, SubgroupFunctor.range f = ⊥) →
    IsUnipotent Z.toGrp

namespace CommutativeNoTorus

variable {k : Type u} [Field k]
    (Z : CommGroupScheme (Spec (CommRingCat.of k)))
    [Smooth Z.toGrp.X.hom] [IsAffineHom Z.toGrp.X.hom]
    [ConnectedSpace Z.toGrp.X.left]

/-- A smooth connected affine commutative group without torus maps is unipotent
over any field. -/
theorem isUnipotent_of_no_torus_over_field
    (hZ : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))),
      IsTorus T.toGrp → ∀ f : T.toGrp ⟶ Z.toGrp, SubgroupFunctor.range f = ⊥) :
    IsUnipotent Z.toGrp := by
  let K := SeparableClosure k
  let ZK := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj Z
  have : IsAffine Z.toGrp.X.left := isAffine_of_isAffineHom Z.toGrp.X.hom
  have : ConnectedSpace ZK.toGrp.X.left :=
    GroupScheme.connectedSpace_baseChange_of_smooth_affine Z.toGrp (algebraBaseMap k K)
  have : Smooth ZK.toGrp.X.hom := by
    change Smooth (pullback.snd Z.toGrp.X.hom (algebraBaseMap k K))
    infer_instance
  have : IsAffineHom ZK.toGrp.X.hom := by
    change IsAffineHom (pullback.snd Z.toGrp.X.hom (algebraBaseMap k K))
    infer_instance
  apply IsUnipotent.of_baseChange (K := K)
  apply isUnipotent_of_gm_hom_eq_zero_of_isSepClosed ZK
  exact CocharacterDatum.gm_hom_eq_zero_of_isGalois (Z := Z) hZ K

end CommutativeNoTorus

/-- Proof of the commutative no-torus implication in the original universe. -/
theorem commutativeNoTorusUnipotent : CommutativeNoTorusUnipotentStatement.{u} := by
  intro k _ Z _ _ _ hZ
  exact CommutativeNoTorus.isUnipotent_of_no_torus_over_field Z hZ

end Langlands.GroupScheme
