/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatAffineGlobalHomComparison
public import WeilConjectures.AlgebraicGeometry.MixedGlobalHomAdjunctionIso
import WeilConjectures.AlgebraicGeometry.MixedGlobalHomBaseChangeExchange
import all WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso

/-!
# Transport of global Hom comparisons across a counit square

Source: Stacks Project, Tag 0AA8, the commutative diagrams in the final part of the proof.
(blueprint: lem-sc-mixed-global-hom-base-change-counit-transport).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry

private theorem homMap_comp {C D : Type*} [Category* C] [Category* D]
    (H : Cᵒᵖ × C ⥤ D) {P P' P'' Q Q' Q'' : C}
    (a : P' ⟶ P) (b : P'' ⟶ P') (t : Q ⟶ Q') (v : Q' ⟶ Q'') :
    H.map (X := (op P, Q)) (Y := (op P', Q')) (a.op, t) ≫
      H.map (X := (op P', Q')) (Y := (op P'', Q'')) (b.op, v) =
    H.map (X := (op P, Q)) (Y := (op P'', Q'')) ((b ≫ a).op, t ≫ v) := by
  rw [← H.map_comp]
  rfl

private theorem pullbackMate_naturality
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (H : Cᵒᵖ × C ⥤ C) (J : Dᵒᵖ × D ⥤ D)
    (F : C ⥤ D) (R : D ⥤ C) (adj : F ⊣ R)
    (τ : MonoidalCategory.tensor C ⋙ F ≅ F.prod F ⋙ MonoidalCategory.tensor D)
    (ex : ∀ A P Q : C, (A ⟶ H.obj (op P, Q)) ≃ (MonoidalCategory.tensorObj A P ⟶ Q))
    (ey : ∀ A P Q : D, (A ⟶ J.obj (op P, Q)) ≃ (MonoidalCategory.tensorObj A P ⟶ Q))
    (hx : ∀ (A A' P Q Q' : C) (a : A' ⟶ A) (t : Q ⟶ Q')
      (z : A ⟶ H.obj (op P, Q)),
      ex A' P Q' (a ≫ z ≫ H.map (X := (op P, Q)) (Y := (op P, Q')) ((𝟙 P).op, t)) =
        (MonoidalCategory.tensorHom a (𝟙 P)) ≫ ex A P Q z ≫ t)
    (hy : ∀ (A A' P Q Q' : D) (a : A' ⟶ A) (t : Q ⟶ Q')
      (z : A ⟶ J.obj (op P, Q)),
      ey A' P Q' (a ≫ z ≫ J.map ((𝟙 P).op, t)) =
        (MonoidalCategory.tensorHom a (𝟙 P)) ≫ ey A P Q z ≫ t)
    (P Q Q' : C) (t : Q ⟶ Q') :
    let c := fun P Q ↦ adj.homEquiv _ _
      ((ey _ _ _).symm (τ.inv.app (H.obj (op P, Q), P) ≫
        F.map (ex _ _ _ (𝟙 (H.obj (op P, Q))))))
    H.map (X := (op P, Q)) (Y := (op P, Q')) ((𝟙 P).op, t) ≫ c P Q' =
      c P Q ≫ R.map (J.map ((𝟙 (F.obj P)).op, F.map t)) := by
  dsimp only
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  congr 1
  apply (ey _ _ _).injective
  have hleft := hy (F.obj (H.obj (op P, Q'))) (F.obj (H.obj (op P, Q)))
    (F.obj P) (F.obj Q') (F.obj Q')
    (F.map (H.map (X := (op P, Q)) (Y := (op P, Q')) ((𝟙 P).op, t))) (𝟙 _)
    ((ey _ _ _).symm (τ.inv.app (H.obj (op P, Q'), P) ≫
      F.map (ex _ _ _ (𝟙 (H.obj (op P, Q'))))))
  have hright := hy (F.obj (H.obj (op P, Q))) (F.obj (H.obj (op P, Q)))
    (F.obj P) (F.obj Q) (F.obj Q') (𝟙 _) (F.map t)
    ((ey _ _ _).symm (τ.inv.app (H.obj (op P, Q), P) ≫
      F.map (ex _ _ _ (𝟙 (H.obj (op P, Q))))))
  have hid : J.map (X := (op (F.obj P), F.obj Q'))
      (Y := (op (F.obj P), F.obj Q')) ((𝟙 (F.obj P)).op, 𝟙 (F.obj Q')) = 𝟙 _ :=
    J.map_id (op (F.obj P), F.obj Q')
  rw [hid] at hleft
  simp only [Category.comp_id, Category.id_comp, MonoidalCategory.id_tensorHom_id,
    Equiv.apply_symm_apply] at hleft hright
  dsimp only [Functor.prod_obj]
  rw [hleft, hright]
  have hτ := τ.inv.naturality
    (X := (H.obj (op P, Q), P)) (Y := (H.obj (op P, Q'), P))
    (H.map (X := (op P, Q)) (Y := (op P, Q')) ((𝟙 P).op, t), 𝟙 P)
  dsimp only [Functor.comp_map, Functor.prod_map] at hτ
  simp only [CategoryTheory.Functor.map_id] at hτ
  dsimp only [MonoidalCategory.tensor] at hτ
  rw [← Category.assoc, hτ, Category.assoc, ← F.map_comp, Category.assoc, ← F.map_comp]
  congr 2
  have h₁ := hx _ _ _ _ _ (𝟙 _) t (𝟙 (H.obj (op P, Q)))
  have h₂ := hx _ _ _ _ _ (H.map (X := (op P, Q)) (Y := (op P, Q')) ((𝟙 P).op, t)) (𝟙 Q')
    (𝟙 (H.obj (op P, Q')))
  have hidH : H.map (X := (op P, Q')) (Y := (op P, Q'))
      ((𝟙 P).op, 𝟙 Q') = 𝟙 _ := H.map_id (op P, Q')
  rw [hidH] at h₂
  simp only [Category.comp_id, Category.id_comp, MonoidalCategory.id_tensorHom_id] at h₁ h₂
  exact h₂.symm.trans h₁

private theorem directImage_naturality
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q Q' : schemeDerivedCategory X) (t : Q ⟶ Q') :
    (schemeGlobalScalarRestriction f).map
        ((schemeGlobalDerivedHom X).map ((𝟙 P).op, t)) ≫
      mixedGlobalHomDirectImageMap f P Q' =
    mixedGlobalHomDirectImageMap f P Q ≫
      (schemeGlobalDerivedHom Y).map
        ((𝟙 ((schemeDerivedDirectImage f).obj P)).op,
          (schemeDerivedDirectImage f).map t) := by
  let H := derivedInternalHom (Opens.grothendieckTopology X) X.sheaf
  let c := Classical.choose (exists_schemeHomDirectImageComparison f)
  have hn := c.naturality (X := (op P, Q)) (Y := (op P, Q')) ((𝟙 P).op, t)
  have hl := (mixedGlobalSectionsDirectImageIso f).inv.naturality
    (H.map (X := (op P, Q)) (Y := (op P, Q')) ((𝟙 P).op, t))
  dsimp only [mixedGlobalHomDirectImageMap, mixedHomDirectImageComparison,
    schemeGlobalDerivedHom, Functor.comp_map]
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.op_map] at hn hl
  change (schemeDerivedDirectImage f).map
      (H.map (X := (op P, Q)) (Y := (op P, Q')) ((𝟙 P).op, t)) ≫
      c.app (op P, Q') = c.app (op P, Q) ≫
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf).map
          (X := (op ((schemeDerivedDirectImage f).obj P),
            (schemeDerivedDirectImage f).obj Q))
          (Y := (op ((schemeDerivedDirectImage f).obj P),
            (schemeDerivedDirectImage f).obj Q'))
          (((schemeDerivedDirectImage f).map (𝟙 P)).op,
            (schemeDerivedDirectImage f).map t) at hn
  simp only [CategoryTheory.Functor.map_id] at hn
  have hn' := congrArg ((schemeDerivedGlobalSections Y).map) hn
  simp only [CategoryTheory.Functor.map_comp] at hn'
  rw [← Category.assoc, hl, Category.assoc]
  simpa only [Category.assoc] using
    congrArg ((mixedGlobalSectionsDirectImageIso f).inv.app _ ≫ ·) hn'

private theorem pullback_naturality
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {S T : Scheme.{u}} (f : T ⟶ S)
    (P Q Q' : schemeDerivedCategory S) (t : Q ⟶ Q') :
    (schemeGlobalDerivedHom S).map ((𝟙 P).op, t) ≫
      mixedGlobalHomPullbackComparison f P Q' =
    mixedGlobalHomPullbackComparison f P Q ≫
      (schemeGlobalScalarRestriction f).map
        ((schemeGlobalDerivedHom T).map
          ((𝟙 ((derivedPullback f).obj P)).op, (derivedPullback f).map t)) := by
  let H := derivedInternalHom (Opens.grothendieckTopology S) S.sheaf
  let J := derivedInternalHom (Opens.grothendieckTopology T) T.sheaf
  let F := derivedPullback f
  let R := schemeDerivedDirectImage f
  let adj := schemeHomPullbackAdjunction f
  let ex := schemeDerivedTensorHomEquiv S
  let ey := schemeDerivedTensorHomEquiv T
  let τ := mixedHomTensorPullbackIso f
  have hx := (Classical.choose_spec (exists_canonicalDerivedTensorHom S)).1
  have hy := (Classical.choose_spec (exists_canonicalDerivedTensorHom T)).1
  have hn := pullbackMate_naturality H J F R adj τ ex ey
    (fun A A' L M M' a d z ↦ hx A A' L L M M' a (𝟙 L) d z)
    (fun A A' L M M' a d z ↦ hy A A' L L M M' a (𝟙 L) d z) P Q Q' t
  let c (P Q : schemeDerivedCategory S) :
      H.obj (op P, Q) ⟶ R.obj (J.obj (op (F.obj P), F.obj Q)) :=
    adj.homEquiv _ _ ((ey _ _ _).symm
      (τ.inv.app (H.obj (op P, Q), P) ≫ F.map (ex _ _ _ (𝟙 _))))
  change H.map (X := (op P, Q)) (Y := (op P, Q')) ((𝟙 P).op, t) ≫ c P Q' =
    c P Q ≫ R.map (J.map (X := (op (F.obj P), F.obj Q))
      (Y := (op (F.obj P), F.obj Q')) ((𝟙 (F.obj P)).op, F.map t)) at hn
  have hn' := congrArg ((schemeDerivedGlobalSections S).map) hn
  simp only [CategoryTheory.Functor.map_comp] at hn'
  have hl := (mixedGlobalSectionsDirectImageIso f).hom.naturality
    (J.map (X := (op (F.obj P), F.obj Q)) (Y := (op (F.obj P), F.obj Q'))
      ((𝟙 (F.obj P)).op, F.map t))
  dsimp only [Functor.comp_map] at hl
  dsimp only [mixedGlobalHomPullbackComparison, schemeGlobalDerivedHom,
    Functor.comp_map]
  rw [← Category.assoc, hn', Category.assoc, hl]
  simp only [Category.assoc]
  rfl

/-- The pullback and direct-image global Hom comparisons transport a commuting
counit square. This assertion concerns arbitrary derived objects and morphisms;
no right adjoints on quasi-coherent categories or right-adjoint base-change map
are used.

Source: Stacks Project, Tag 0AA8, the final commutative diagrams; the comparisons
are the evaluation mates of Tags 08I3 and 0B6I.
(blueprint: lem-sc-mixed-global-hom-base-change-counit-transport).

Proof:
1. Expand the pullback comparison and direct-image comparison as evaluation mates.
Transpose under the pinned tensor-Hom bijections and pullback/direct-image
adjunctions. Their naturality shows that the square comparing pullback followed
by direct image with direct image followed by pullback commutes, with the
canonical base-change maps in the two Hom entries. The tensor comparisons and
Leray comparisons are the canonical ones, so their composition identifications
agree with the scalar square isomorphism.
2. Postcompose the square with Hom of the morphism t and then Hom of e'.
Naturality in the second Hom entry replaces this by Hom of Rf'(t) followed by e'.
Use the assumed counit square to replace beta_N followed by these maps by Lg*(e).
Naturality of the pullback comparison in its second entry now moves e to the
source, giving the comparison applied to (Rf*M,K).
3. The remaining map in the first Hom entry is beta_M. Since beta_M is invertible,
cancel it contravariantly; its inverse gives exactly the final displayed factor.
The tensorators are normalized by their K-flat equations and Leray comparisons by
their derived-unit equations, so the computation holds with independent sheaf and
module localization universes. All steps hold before extension of scalars and give the identity
of transposes. -/
theorem mixedGlobalHom_baseChange_counit_transport
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (M N : schemeDerivedCategory X) (E : schemeDerivedCategory (pullback f g))
    (K : schemeDerivedCategory Y)
    (t : (derivedPullback (pullback.fst f g)).obj N ⟶ E)
    (e : (schemeDerivedDirectImage f).obj N ⟶ K)
    (e' : (schemeDerivedDirectImage (pullback.snd f g)).obj E ⟶
      (derivedPullback g).obj K)
    [IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
      (pullback.fst f g) pullback.condition M)]
    (h : schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition N ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map t ≫ e' =
        (derivedPullback g).map e) :
    (schemeGlobalScalarRestriction f).map
      (mixedGlobalHomPullbackComparison (pullback.fst f g) M N ≫
        (schemeGlobalScalarRestriction (pullback.fst f g)).map
          ((schemeGlobalDerivedHom (pullback f g)).map ((𝟙 _).op, t))) ≫
      (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition).hom.app
          ((schemeGlobalDerivedHom (pullback f g)).obj
            (op ((derivedPullback (pullback.fst f g)).obj M), E)) ≫
      (schemeGlobalScalarRestriction g).map
        (mixedGlobalHomDirectImageMap (pullback.snd f g)
            ((derivedPullback (pullback.fst f g)).obj M) E ≫
          (schemeGlobalDerivedHom Y').map ((𝟙 _).op, e')) =
    (mixedGlobalHomDirectImageMap f M N ≫
        (schemeGlobalDerivedHom Y).map ((𝟙 _).op, e)) ≫
      mixedGlobalHomPullbackComparison g
        ((schemeDerivedDirectImage f).obj M) K ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeGlobalDerivedHom Y').map
          (X := (op ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj M)),
            (derivedPullback g).obj K))
          (Y := (op ((schemeDerivedDirectImage (pullback.snd f g)).obj
            ((derivedPullback (pullback.fst f g)).obj M)), (derivedPullback g).obj K))
          ((inv (schemeDerivedBaseChangeMap f (pullback.snd f g) g
            (pullback.fst f g) pullback.condition M)).op, 𝟙 _)) := by
  let F := schemeDerivedDirectImage f
  let F' := schemeDerivedDirectImage (pullback.snd f g)
  let L := derivedPullback g
  let LX := derivedPullback (pullback.fst f g)
  let Sf := schemeGlobalScalarRestriction f
  let Sg := schemeGlobalScalarRestriction g
  let H := schemeGlobalDerivedHom Y' ⋙ Sg
  let A := F'.obj (LX.obj M)
  let B := F'.obj (LX.obj N)
  let U := L.obj (F.obj M)
  let V := L.obj (F.obj N)
  let β : U ⟶ A := schemeDerivedBaseChangeMap f (pullback.snd f g) g
    (pullback.fst f g) pullback.condition M
  let γ : V ⟶ B := schemeDerivedBaseChangeMap f (pullback.snd f g) g
    (pullback.fst f g) pullback.condition N
  let θ : B ⟶ L.obj K := F'.map t ≫ e'
  let s := schemeGlobalScalarSquareIso f (pullback.snd f g) g
    (pullback.fst f g) pullback.condition
  let α := Sf.map (mixedGlobalHomPullbackComparison (pullback.fst f g) M N) ≫
    s.hom.app ((schemeGlobalDerivedHom (pullback f g)).obj (op (LX.obj M), LX.obj N)) ≫
    Sg.map (mixedGlobalHomDirectImageMap (pullback.snd f g) (LX.obj M) (LX.obj N))
  let ρ := mixedGlobalHomDirectImageMap f M N ≫
    mixedGlobalHomPullbackComparison g (F.obj M) (F.obj N)
  have : IsIso β := by dsimp only [β]; infer_instance
  have hs : γ ≫ θ = L.map e := h
  have hex : α ≫ H.map (X := (op A, B)) (Y := (op U, B)) (β.op, 𝟙 B) =
      ρ ≫ H.map (X := (op U, V)) (Y := (op U, B)) ((𝟙 U).op, γ) := by
    simpa only [α, ρ, H, Functor.comp_map, Category.assoc] using
      mixedGlobalHom_baseChange_exchange f g M N
  have hc := congrArg
    (fun z ↦ z ≫ H.map (X := (op U, B)) (Y := (op A, L.obj K)) ((inv β).op, θ)) hex
  have core : α ≫ H.map (X := (op A, B)) (Y := (op A, L.obj K)) ((𝟙 A).op, θ) =
      ρ ≫ H.map (X := (op U, V)) (Y := (op A, L.obj K)) ((inv β).op, L.map e) := by
    simp only [Category.assoc, ← H.map_comp] at hc
    change α ≫ H.map (X := (op A, B)) (Y := (op A, L.obj K))
        ((β.op ≫ (inv β).op), (𝟙 B ≫ θ)) =
      ρ ≫ H.map (X := (op U, V)) (Y := (op A, L.obj K))
        (((𝟙 U).op ≫ (inv β).op), (γ ≫ θ)) at hc
    rw [Category.id_comp, ← op_comp, IsIso.inv_hom_id,
      ← op_comp, Category.comp_id, hs] at hc
    exact hc
  have hd := directImage_naturality (pullback.snd f g) (LX.obj M) (LX.obj N) E t
  have hp := pullback_naturality g (F.obj M) (F.obj N) K e
  have hn := s.hom.naturality
    ((schemeGlobalDerivedHom (pullback f g)).map
      (X := (op (LX.obj M), LX.obj N)) (Y := (op (LX.obj M), E)) ((𝟙 _).op, t))
  dsimp only [Functor.comp_map] at hn
  have hd' := congrArg Sg.map hd
  simp only [CategoryTheory.Functor.map_comp] at hd'
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hd', reassoc_of% hp]
  dsimp only [α, ρ, H, Functor.comp_map] at core
  simp only [Category.assoc] at core
  rw [← Sg.map_comp, homMap_comp, Category.id_comp]
  have hr := homMap_comp H (𝟙 U) (inv β) (L.map e) (𝟙 (L.obj K))
  simp only [Category.comp_id] at hr
  dsimp only [H, Functor.comp_map] at hr
  rw [hr]
  exact core


end AlgebraicGeometry
