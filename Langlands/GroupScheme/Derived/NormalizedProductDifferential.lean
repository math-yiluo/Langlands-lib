import Langlands.GroupScheme.AutomorphicAction.SemidirectHomLift
import Langlands.GroupScheme.Lie.SurjectiveDifferentialProof
import Langlands.GroupScheme.Rational.ProductDetection

/-! # Normalized subgroup multiplication from its tangent span -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace AutomorphicAction

/-- Compatible smooth affine factors with spanning tangent images multiply
smoothly and surjectively onto a connected smooth affine group. -/
theorem smoothSurjective_of_tangentSpan
    {k : Type u} [Field k] {G D T : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [Smooth D.X.hom] [Smooth T.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom D.X.hom] [IsAffineHom T.X.hom]
    [ConnectedSpace G.X.left]
    (a : AutomorphicAction T D) (d : D ⟶ G) (i : T ⟶ G)
    (hc : ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ T.X) (x : V ⟶ D.X),
      a.act t x ≫ d.hom.hom =
        (t ≫ i.hom.hom) * (x ≫ d.hom.hom) * (t ≫ i.hom.hom)⁻¹)
    (hspan : LinearMap.range (Lie.targetMapLinear d k) ⊔
        LinearMap.range (Lie.targetMapLinear i k) = ⊤) :
    Smooth (subgroupProductMap d i).left ∧
      Surjective (subgroupProductMap d i).left := by
  let m := a.semidirectHomLift d i hc
  have hleft : LinearMap.range (Lie.targetMapLinear d k) ≤
      LinearMap.range (Lie.targetMapLinear m k) := by
    rintro _ ⟨X, rfl⟩
    refine ⟨Lie.targetMapLinear a.semidirectInl k X, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change (X.toMul.val ≫ a.semidirectInl.hom.hom) ≫ m.hom.hom = _
    rw [Category.assoc]
    change X.toMul.val ≫ (a.semidirectInl ≫ m).hom.hom = _
    rw [semidirectInl_comp_lift]
    rfl
  have hright : LinearMap.range (Lie.targetMapLinear i k) ≤
      LinearMap.range (Lie.targetMapLinear m k) := by
    rintro _ ⟨X, rfl⟩
    refine ⟨Lie.targetMapLinear a.semidirectInr k X, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change (X.toMul.val ≫ a.semidirectInr.hom.hom) ≫ m.hom.hom = _
    rw [Category.assoc]
    change X.toMul.val ≫ (a.semidirectInr ≫ m).hom.hom = _
    rw [semidirectInr_comp_lift]
    rfl
  have hsurj : Function.Surjective (Lie.targetMapLinear m k) := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← hspan]
    exact sup_le hleft hright
  have h := Lie.smoothSurjectiveOfSurjectiveDifferential k a.semidirectProduct G
    inferInstance inferInstance inferInstance inferInstance inferInstance m hsurj
  simpa only [m, semidirectHomLift_hom, subgroupProductMap] using h

end AutomorphicAction

/-- If the first subgroup is normal, smoothness and the spanning of the two
actual tangent images imply smooth surjectivity of ordered multiplication. -/
theorem smoothSurjective_subgroupProductMap_of_normal_of_tangentSpan
    {k : Type u} [Field k] {G D T : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [Smooth D.X.hom] [Smooth T.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom D.X.hom] [IsAffineHom T.X.hom]
    [ConnectedSpace G.X.left]
    (d : D ⟶ G) (i : T ⟶ G) [Mono d.hom.hom]
    (hn : (SubgroupFunctor.range d).IsNormal)
    (hspan : LinearMap.range (Lie.targetMapLinear d k) ⊔
        LinearMap.range (Lie.targetMapLinear i k) = ⊤) :
    Smooth (subgroupProductMap d i).left ∧
      Surjective (subgroupProductMap d i).left := by
  let hn' : (SubgroupFunctor.range d).IsNormalizedBy (SubgroupFunctor.range i) :=
    fun V g x _ hx => hn V g x (Subgroup.mem_top _) hx
  exact (AutomorphicAction.ofNormalizedConjugation d i hn').smoothSurjective_of_tangentSpan
    d i (fun V t x => SubgroupFunctor.lift_comp_normalizedConjugation_comp d i hn' t x)
    hspan

end Langlands.GroupScheme
