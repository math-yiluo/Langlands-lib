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

private theorem transport_cocycle_etale
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj)
    (t : FiniteLocalModelCompatibleTransport T E U Q e)
    (V : T.Etale) (a b c : V ⟶ U)
    (x : Over.mk a.left ⟶ Over.mk Q.obj.hom) :
    t.transport b.left c.left
        ((MorphismProperty.Over.w b).trans (MorphismProperty.Over.w c).symm)
        (t.transport a.left b.left
          ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm) x) =
      t.transport a.left c.left
        ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w c).symm) x := by
  let z : ((Etale.overToEtale U).op ⋙ uliftYoneda.{u + 1}.obj Q.obj).obj
      (op (Over.mk a)) := ULift.up (MorphismProperty.Over.homMk x.left (Over.w x))
  let s := e.inv.app (op (Over.mk a)) z
  have hs : e.hom.app (op (Over.mk a)) s = z :=
    ConcreteCategory.congr_hom (e.inv_hom_id_app (op (Over.mk a))) z
  let p (d : V ⟶ U) : Over.mk d.left ⟶ Over.mk Q.obj.hom :=
    Over.homMk ((e.hom.app (op (Over.mk d))) s).down.left
      (MorphismProperty.Over.w ((e.hom.app (op (Over.mk d))) s).down)
  have hpa : p a = x := by
    apply Over.OverMorphism.ext
    change ((e.hom.app (op (Over.mk a))) s).down.left = x.left
    rw [hs]
    rfl
  have hp (d f : V ⟶ U) :
      t.transport d.left f.left
        ((MorphismProperty.Over.w d).trans (MorphismProperty.Over.w f).symm) (p d) =
      p f := by
    apply Over.OverMorphism.ext
    exact t.compatibility V d f s
  rw [← hpa, hp a b, hp b c, hp a c]

private theorem transport_cocycle_of_lift
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj)
    (t : FiniteLocalModelCompatibleTransport T E U Q e)
    (R W : Scheme.{u}) (g : W ⟶ R) (aa bb cc : R ⟶ U.left)
    (hab' : aa ≫ U.hom = bb ≫ U.hom) (hbc' : bb ≫ U.hom = cc ≫ U.hom)
    (z : Over.mk aa ⟶ Over.mk Q.obj.hom)
    (hz : t.transport bb cc hbc' (t.transport aa bb hab' z) =
      t.transport aa cc (hab'.trans hbc') z)
    (a b c : W ⟶ U.left) (hab : a ≫ U.hom = b ≫ U.hom)
    (hbc : b ≫ U.hom = c ≫ U.hom) (x : Over.mk a ⟶ Over.mk Q.obj.hom)
    (ga : g ≫ aa = a) (gb : g ≫ bb = b) (gc : g ≫ cc = c)
    (gx : g ≫ z.left = x.left) :
    t.transport b c hbc (t.transport a b hab x) =
      t.transport a c (hab.trans hbc) x := by
  subst a b c
  have hx : (Over.homMk g : Over.mk (g ≫ aa) ⟶ Over.mk aa) ≫ z = x :=
    Over.OverMorphism.ext gx
  have hnab := t.naturality g aa bb hab' z
  have hnbc := t.naturality g bb cc hbc' (t.transport aa bb hab' z)
  have hnac := t.naturality g aa cc (hab'.trans hbc') z
  rw [hx] at hnab hnac
  rw [hnab, hnbc, hz]
  exact hnac.symm

/-- The cocycle law for compatible transport.

Source: Stacks Project, Tags 03RV and 02W5.
(blueprint: lem-weil-pbc-finite-local-model-compatible-transport-cocycle)
Proof: Put R = Q ×_T U ×_T U, with its three maps to U. Since Q → U and
U → T are etale, R → T is etale. Its projection to Q is the universal point
above the first lift. Apply e inverse to that point to obtain a section s of
E on R. Compatibility identifies the first transport with the point obtained
from s above the second lift, and its subsequent transport with the point
obtained from s above the third lift. Direct transport also equals the third
point, so these transports coincide. Given arbitrary W, x, a, b, c, the maps
x.left, b, c have equal composites to T. The Limits.pullback universal property
therefore gives W → R whose composites are the given maps. Apply naturality
three times to pull back the universal equality. Functoriality of composition
then gives the displayed equality. Proof irrelevance identifies the equalities
of composites used as transport arguments. Empty schemes satisfy the same
universal properties; neither surjectivity nor nonemptiness is needed. -/
theorem finiteLocalModels_descentDatum_compatibility_transport_cocycle
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj)
    (t : FiniteLocalModelCompatibleTransport T E U Q e) :
    ∀ (W : Scheme.{u}) (a b c : W ⟶ U.left)
      (hab : a ≫ U.hom = b ≫ U.hom)
      (hbc : b ≫ U.hom = c ≫ U.hom)
      (x : Over.mk a ⟶ Over.mk Q.obj.hom),
      t.transport b c hbc (t.transport a b hab x) =
        t.transport a c (hab.trans hbc) x := by
  intro W a b c hab hbc x
  have hw : x.left ≫ Q.obj.hom = a := Over.w x
  let f : Q.obj.left ⟶ T := Q.obj.hom ≫ U.hom
  let B := Limits.pullback f U.hom
  let v : B ⟶ T := Limits.pullback.snd f U.hom ≫ U.hom
  let R := Limits.pullback v U.hom
  let q : R ⟶ Q.obj.left := Limits.pullback.fst v U.hom ≫ Limits.pullback.fst f U.hom
  let aa : R ⟶ U.left := q ≫ Q.obj.hom
  let bb : R ⟶ U.left := Limits.pullback.fst v U.hom ≫ Limits.pullback.snd f U.hom
  let cc : R ⟶ U.left := Limits.pullback.snd v U.hom
  have hab' : aa ≫ U.hom = bb ≫ U.hom := by
    dsimp [aa, bb, q]
    simp only [Category.assoc]
    exact congrArg (Limits.pullback.fst v U.hom ≫ ·)
      (Limits.pullback.condition (f := f) (g := U.hom))
  have hbc' : bb ≫ U.hom = cc ≫ U.hom := by
    exact (Category.assoc _ _ _).trans (Limits.pullback.condition (f := v) (g := U.hom))
  let V : T.Etale := Etale.mk (cc ≫ U.hom)
  let a' : V ⟶ U := MorphismProperty.Over.homMk aa (hab'.trans hbc')
  let b' : V ⟶ U := MorphismProperty.Over.homMk bb hbc'
  let c' : V ⟶ U := MorphismProperty.Over.homMk cc rfl
  let z : Over.mk aa ⟶ Over.mk Q.obj.hom := Over.homMk q rfl
  have hz : t.transport bb cc hbc' (t.transport aa bb hab' z) =
      t.transport aa cc (hab'.trans hbc') z :=
    transport_cocycle_etale T E U Q e t V a' b' c' z
  let g₀ : W ⟶ B := Limits.pullback.lift x.left b (by
    change x.left ≫ Q.obj.hom ≫ U.hom = b ≫ U.hom
    rw [← Category.assoc, hw]
    exact hab)
  let g : W ⟶ R := Limits.pullback.lift g₀ c (by
    dsimp [v]
    rw [← Category.assoc, Limits.pullback.lift_snd]
    exact hbc)
  have ga : g ≫ aa = a := by
    dsimp [g, aa, q, g₀]
    simp only [Limits.pullback.lift_fst_assoc, Category.assoc]
    exact hw
  have gb : g ≫ bb = b := by
    dsimp [g, bb, g₀]
    simp only [Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd]
  have gc : g ≫ cc = c := by
    exact Limits.pullback.lift_snd _ _ _
  have gx : g ≫ z.left = x.left := by
    change g ≫ q = x.left
    dsimp [g, q, g₀]
    simp only [Limits.pullback.lift_fst_assoc, Limits.pullback.lift_fst]
  exact transport_cocycle_of_lift T E U Q e t R W g aa bb cc hab' hbc' z hz
    a b c hab hbc x ga gb gc gx
end AlgebraicGeometry.Scheme
