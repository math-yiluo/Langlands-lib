import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Statement: Chevalley groups over the integers are split and classified by one fibre -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Chevalley groups over `ℤ`** (Conrad, *Reductive group schemes* (2014), p.230 and
Proposition 6.4.1). A *Chevalley group* is a reductive group scheme `G` over `Spec ℤ` that
admits a maximal torus over `ℤ`: a closed subgroup `t : T ⟶ G` whose source `T` is a torus
(étale-locally a finite split torus) and which is a maximal torus on every fibre. Then

1. every Chevalley group is split: its maximal torus `T` is isomorphic to a split torus
   `𝔾_m^I`, the roots on every fibre are given by one finite reduced root datum `P` on the
   coordinate lattices `ℤ^I`, and every root space is a free `ℤ`-module of rank one;
2. two Chevalley groups `G`, `G'` are isomorphic over `ℤ` if and only if they become
   isomorphic over some (equivalently, every) field `k`; in particular, if and only if they
   are isomorphic over `ℂ`.

Here `ℤ` is `ULift ℤ` in the universe of the group schemes and test fields. -/
def ChevalleyGroupClassificationStatement : Prop :=
  let IsChevalley : GroupScheme (Spec (CommRingCat.of (ULift.{u} ℤ))) → Prop := fun G =>
    IsReductive G ∧
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of (ULift.{u} ℤ)))) (t : T.toGrp ⟶ G),
        RelativeTorus.IsTorus T.toGrp ∧ IsClosedSubgroup t ∧ IsFibrewiseMaximalTorus t
  (∀ (G : GroupScheme (Spec (CommRingCat.of (ULift.{u} ℤ)))) (hG : IsReductive G)
      (T : CommGroupScheme (Spec (CommRingCat.of (ULift.{u} ℤ)))) (t : T.toGrp ⟶ G),
      RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t → IsFibrewiseMaximalTorus t →
      ∃ (I : Type u) (_ : Fintype I)
        (e : splitTorus (Spec (CommRingCat.of (ULift.{u} ℤ))) I ≅ T.toGrp)
        (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
        haveI := hG.isAffineHom
        IsFibrewiseRootDatumOf I G (e.hom ≫ t) P ∧
          ∀ α : J, Nonempty (splitTorus.exponentWeightSpace I G (e.hom ≫ t) (P.root α) ≃ₗ[
            CommRingCat.of (ULift.{u} ℤ)] CommRingCat.of (ULift.{u} ℤ))) ∧
    ∀ G G' : GroupScheme (Spec (CommRingCat.of (ULift.{u} ℤ))), IsChevalley G → IsChevalley G' →
      ∀ (k : Type u) [Field k] [Algebra (ULift.{u} ℤ) k],
        Nonempty (G ≅ G') ↔
          Nonempty ((baseChange (algebraBaseMap (ULift.{u} ℤ) k)).obj G ≅
            (baseChange (algebraBaseMap (ULift.{u} ℤ) k)).obj G')

end Langlands.GroupScheme
