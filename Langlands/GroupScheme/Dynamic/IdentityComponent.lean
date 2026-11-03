import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.Dynamic.Action
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Identity-limit extensions lie in the actual identity component -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]

namespace IdentityComponent

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] in
/-- An affine-line family with identity zero section lands in the actual
identity component, even over a disconnected or nonreduced test scheme. -/
theorem range_subset_identitySet_of_evalZero_eq_one
    {T : Over (Spec (CommRingCat.of k))}
    (e : T ⊗ AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ G.X)
    (he0 : Dynamic.evalZero e = 1) :
    Set.range e.left ⊆ identitySet G := by
  have : GeometricallyIrreducible
      (AffineLine.scheme (Spec (CommRingCat.of k))).hom := by
    change GeometricallyIrreducible (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k)) ↘ _)
    infer_instance
  have : GeometricallyConnected
      (AffineLine.scheme (Spec (CommRingCat.of k))).hom :=
    GeometricallyIrreducible.geometricallyConnected _
  rintro _ ⟨z, rfl⟩
  let p : (T ⊗ AffineLine.scheme (Spec (CommRingCat.of k))).left ⟶ T.left :=
    pullback.fst T.hom (AffineLine.scheme (Spec (CommRingCat.of k))).hom
  let s : T ⟶ T ⊗ AffineLine.scheme (Spec (CommRingCat.of k)) :=
    lift (𝟙 T) (toUnit T ≫ AffineLine.zeroSection _)
  have hF : _root_.IsConnected (p ⁻¹' {p z}) :=
    Scheme.Hom.isConnected_preimage_singleton p (p z)
  have hs : s ≫ e = toUnit T ≫ η[G.X] := he0
  have hsz : s.left (p z) ∈ p ⁻¹' {p z} := by
    change (s ≫ fst _ _).left (p z) = p z
    rw [lift_fst]
    rfl
  have hconn : _root_.IsConnected (e.left '' (p ⁻¹' {p z})) :=
    hF.image _ e.left.continuous.continuousOn
  refine hconn.isPreconnected.subset_connectedComponent ⟨_, hsz, ?_⟩
    ⟨z, rfl, rfl⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hs, Over.comp_left,
    Scheme.Hom.comp_apply, unit_left_apply]

/-- The actual affine-line family lifted into the open identity component. -/
def affineLineLift
    {T : Over (Spec (CommRingCat.of k))}
    (e : T ⊗ AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ G.X)
    (he0 : Dynamic.evalZero e = 1) :
    T ⊗ AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ (identityComponent G).X :=
  FiniteEtaleImage.liftOver (identityComponentι G).hom.hom e (by
    rw [range_identityComponentι]
    exact range_subset_identitySet_of_evalZero_eq_one e he0)

@[reassoc (attr := simp)]
theorem affineLineLift_comp
    {T : Over (Spec (CommRingCat.of k))}
    (e : T ⊗ AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ G.X)
    (he0 : Dynamic.evalZero e = 1) :
    affineLineLift e he0 ≫ (identityComponentι G).hom.hom = e :=
  FiniteEtaleImage.liftOver_fac _ _ _

/-- The lifted family still has the identity as its zero section. -/
theorem affineLineLift_evalZero
    {T : Over (Spec (CommRingCat.of k))}
    (e : T ⊗ AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ G.X)
    (he0 : Dynamic.evalZero e = 1) :
    Dynamic.evalZero (affineLineLift e he0) = 1 := by
  apply (cancel_mono (identityComponentι G).hom.hom).mp
  rw [← Dynamic.evalZero_comp, affineLineLift_comp, he0, MonObj.one_comp]

end IdentityComponent

namespace AutomorphicAction

/-- Every identity-limit point of any actual Gm action lies in the actual
identity component, on every test scheme. -/
theorem unipotent_le_identityComponent
    (a : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp G) :
    a.unipotent ≤ SubgroupFunctor.range (identityComponentι G) := by
  rintro T g ⟨e, he, he0⟩
  refine ⟨lift (𝟙 T) (1 : T ⟶ (Gm (Spec (CommRingCat.of k))).X) ≫
    T ◁ AffineLine.unitInclusion _ ≫ IdentityComponent.affineLineLift e he0, ?_⟩
  change (lift (𝟙 T) (1 : T ⟶ (Gm (Spec (CommRingCat.of k))).X) ≫
    T ◁ AffineLine.unitInclusion _ ≫ IdentityComponent.affineLineLift e he0) ≫
    (identityComponentι G).hom.hom = g
  rw [Category.assoc, Category.assoc, IdentityComponent.affineLineLift_comp, he,
    orbit, naturality, lift_snd, lift_fst_assoc, Category.id_comp, act_one_left]

end AutomorphicAction

end Langlands.GroupScheme
