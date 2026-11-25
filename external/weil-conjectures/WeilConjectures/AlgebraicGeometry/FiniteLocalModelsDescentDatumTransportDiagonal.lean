/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FiniteLocalModelsDescentDatumCompatibilityDatum
@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme
/-- The identity law for compatible transport.

Source: Stacks Project, Tags 03RV and 02W5.
(blueprint: lem-weil-pbc-finite-local-model-compatible-transport-diagonal)
Proof: The universal Q-point on Q,
compatibility, and naturality identify transport along equal lifts with the
identity; pulling back the universal equality along an arbitrary scheme point
proves the displayed statement. -/
theorem finiteLocalModels_descentDatum_compatibility_transport_diagonal
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj)
    (t : FiniteLocalModelCompatibleTransport T E U Q e) :
    ∀ (W : Scheme.{u}) (a : W ⟶ U.left)
      (x : Over.mk a ⟶ Over.mk Q.obj.hom),
      t.transport a a rfl x = x := by
  intro W a x
  obtain ⟨g, hg, rfl⟩ := Over.homMk_surjective x
  change W ⟶ Q.obj.left at g
  change g ≫ Q.obj.hom = a at hg
  subst a
  let V : T.Etale := Etale.mk (Q.obj.hom ≫ U.hom)
  let q : V ⟶ U := MorphismProperty.Over.homMk Q.obj.hom rfl
  let z : ((Etale.overToEtale U).op ⋙ uliftYoneda.{u + 1}.obj Q.obj).obj
      (op (Over.mk q)) := ULift.up (𝟙 Q.obj)
  let s := e.inv.app (op (Over.mk q)) z
  have hs : e.hom.app (op (Over.mk q)) s = z := by
    exact ConcreteCategory.congr_hom (e.inv_hom_id_app (op (Over.mk q))) z
  have h := t.compatibility V q q s
  simp only [hs] at h
  have hn := t.naturality g Q.obj.hom Q.obj.hom rfl
    (𝟙 (Over.mk Q.obj.hom))
  apply Over.OverMorphism.ext
  simp only [Category.comp_id] at hn
  have hh : t.transport Q.obj.hom Q.obj.hom rfl
      (𝟙 (Over.mk Q.obj.hom)) = 𝟙 (Over.mk Q.obj.hom) := by
    apply Over.OverMorphism.ext
    exact h
  rw [hh] at hn
  simpa using congrArg Over.Hom.left hn
end AlgebraicGeometry.Scheme
