/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
import WeilConjectures.AlgebraicGeometry.DirectImageSquareUnitTransport
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate

/-! # Unit compatibility of the sheaf direct-image square mate

Source: Stacks Project, cohomology.tex, Tags 08HY and 0D5T.
(blueprint: lem-pc-derived-pushforward-square-mate-unit).
-/

@[expose] public section

set_option autoImplicit false
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem square_paste {C : Type*} [Category C]
    {A₁ A₂ B₁ B₂ P Q : C} (c₁ : A₁ ≅ B₁) (c₂ : A₂ ≅ B₂)
    (u₁ : P ⟶ A₁) (u₂ : Q ⟶ A₂) (b₁ : P ⟶ B₁) (b₂ : Q ⟶ B₂)
    (d : A₁ ⟶ A₂) (e : P ⟶ Q) (δ : B₁ ⟶ B₂)
    (h₁ : u₁ ≫ c₁.hom = b₁) (h₂ : u₂ ≫ c₂.hom = b₂)
    (hδ : δ = c₁.inv ≫ d ≫ c₂.hom) (he : u₁ ≫ d = e ≫ u₂) :
    b₁ ≫ δ = e ≫ b₂ := by
  rw [← h₁, hδ]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, he, Category.assoc, h₂]

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh

-- Comparing the composite pushforward objects requires extra elaboration.
private theorem normalized_unit {A B C : Scheme.{u}} (s : A ⟶ B) (t : B ⟶ C)
    (J : HomotopyCategory (SheafOfModules.{u} (moduleRings A.toRingedSpace)) (.up ℤ)) :
    (RingedSpace.moduleDirectImage (s ≫ t).toLRSHom.toShHom).rightDerivedFunctorUnit.app J ≫
      (schemeNormalizedDirectImageCompIso s t).inv.app (DerivedCategory.Qh.obj J) =
    (RingedSpace.moduleDirectImage t.toLRSHom.toShHom).rightDerivedFunctorUnit.app
      (((RingedSpace.moduleDirectImage s.toLRSHom.toShHom).mapHomotopyCategory (.up ℤ)).obj J) ≫
    (schemeDerivedDirectImage t).map
      ((RingedSpace.moduleDirectImage s.toLRSHom.toShHom).rightDerivedFunctorUnit.app J) := by
  exact (Classical.choose_spec (RingedSpace.exists_derivedModuleDirectImageComposition
    s.toLRSHom.toShHom t.toLRSHom.toShHom)) J

attribute [local irreducible] schemeNormalizedDirectImageCompIso

-- Match the pinned adjunctions once, before comparing their composite mates.
private theorem canonical_adjoint_eq {A B : Scheme.{u}} (h : A ⟶ B) :
    canonicalPullbackAdjunction.{u, w} h = schemeHomPullbackAdjunction.{u, w} h := rfl

set_option linter.all false in
private theorem canonical_conjugate_eq {A B C D : Scheme.{u}}
    (s : A ⟶ B) (t : B ⟶ D) (q : A ⟶ C) (r : C ⟶ D)
    (κ : derivedPullback r ⋙ derivedPullback q ⟶ derivedPullback t ⋙ derivedPullback s) :
    conjugateEquiv ((canonicalPullbackAdjunction t).comp (canonicalPullbackAdjunction s))
      ((canonicalPullbackAdjunction r).comp (canonicalPullbackAdjunction q)) κ =
    conjugateEquiv ((schemeHomPullbackAdjunction t).comp (schemeHomPullbackAdjunction s))
      ((schemeHomPullbackAdjunction r).comp (schemeHomPullbackAdjunction q)) κ := by
  exact congrArg₂ (fun a b ↦ conjugateEquiv a b κ)
    (congrArg₂ (fun a b ↦ a.comp b) (canonical_adjoint_eq t) (canonical_adjoint_eq s))
    (congrArg₂ (fun a b ↦ a.comp b) (canonical_adjoint_eq r) (canonical_adjoint_eq q))

-- Avoid linting the large chosen adjunction/comparison data again after kernel checking.
set_option linter.all false in
-- Matching the canonical composition choices expands derived-functor instance data.
/-- The sheaf-level unit equation for the square conjugate.
Source: Stacks Project, cohomology.tex, Tags 08HY and 0D5T.
(blueprint: lem-pc-derived-pushforward-square-mate-unit).
Proof: construct the ordinary comparison from pushforward composition and equality
transport; its whole-space section map is the identity. Keep the homotopy
object arbitrary. The existing normalized square-mate theorem identifies the
derived mate with the first composition comparison, equality transport, and the
inverse second comparison. Rewrite the two pasted units using the normalized
composition-unit equations. Associativity cancels the adjacent comparison and its
inverse; single-unit equality transport supplies the middle equation. Substitute
the second composition-unit equation. Only isomorphisms are cancelled, never a
unit, so no injectivity hypothesis is needed. Identity and zero cases agree. -/
theorem exists_derivedPushforwardSquareMateUnit
    {R B : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R) :
    let P₀ := RingedSpace.moduleDirectImage (pullback.fst f g).toLRSHom.toShHom
    let Q₀ := RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom
    let F₀ := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let G₀ := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let RF := schemeDerivedDirectImage f
    let RG := schemeDerivedDirectImage g
    let a := fun {A D : Scheme.{u}} (h : A ⟶ D) ↦ canonicalPullbackAdjunction h
    let p : ∀ {X Y Z : Scheme.{u}} (h : X ⟶ Y) (i : Y ⟶ Z),
        derivedPullback i ⋙ derivedPullback h ≅ derivedPullback (h ≫ i) :=
      @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    let k := p (pullback.snd f g) g ≪≫
      eqToIso (congrArg (fun h ↦ derivedPullback h)
        (pullback.condition (f := f) (g := g)).symm) ≪≫
      (p (pullback.fst f g) f).symm
    let δ := conjugateEquiv ((a f).comp (a (pullback.fst f g)))
      ((a g).comp (a (pullback.snd f g))) k.hom
    ∃ e : P₀ ⋙ F₀ ≅ Q₀ ⋙ G₀,
      (∀ (M : SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))
        (x : M.val.obj (op ⊤)), ((e.hom.app M).val.app (op ⊤)) x = x) ∧
      ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) (.up ℤ),
        F₀.rightDerivedFunctorUnit.app ((P₀.mapHomotopyCategory (.up ℤ)).obj J) ≫
          RF.map (P₀.rightDerivedFunctorUnit.app J) ≫
          δ.app (DerivedCategory.Qh.obj J) =
        DerivedCategory.Qh.map ((e.hom.mapHomotopyCategory (.up ℤ)).app J) ≫
          G₀.rightDerivedFunctorUnit.app ((Q₀.mapHomotopyCategory (.up ℤ)).obj J) ≫
          RG.map (Q₀.rightDerivedFunctorUnit.app J) := by
  extract_lets P₀ Q₀ F₀ G₀ RF RG a p k δ
  let h := pullback.condition (f := f) (g := g)
  let e := directImageSquareIso (pullback.fst f g) f (pullback.snd f g) g h
  refine ⟨e, directImageSquareIso_top _ _ _ _ h, ?_⟩
  intro J
  have hc₁ := normalized_unit (pullback.fst f g) f J
  have hc₂ := normalized_unit (pullback.snd f g) g J
  have he := directImageSquare_unit_transport (pullback.fst f g) f (pullback.snd f g) g h J
  have hd := derivedDirectImage_square_mate f (pullback.snd f g) g (pullback.fst f g) h
  have hm := canonical_conjugate_eq (pullback.fst f g) f (pullback.snd f g) g k.hom
  have hd' := congrArg (fun τ ↦ τ.app (DerivedCategory.Qh.obj J)) (hm.trans hd)
  simp only [NatTrans.comp_app] at hd'
  let c₁ := schemeNormalizedDirectImageCompIso (pullback.fst f g) f
  let c₂ := schemeNormalizedDirectImageCompIso (pullback.snd f g) g
  let u₁ := (RingedSpace.moduleDirectImage
    ((pullback.fst f g) ≫ f).toLRSHom.toShHom).rightDerivedFunctorUnit.app J
  let u₂ := (RingedSpace.moduleDirectImage
    ((pullback.snd f g) ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app J
  let d := (eqToHom (congrArg (fun v ↦ schemeDerivedDirectImage.{u, w} v) h)).app
    (DerivedCategory.Qh.obj J)
  let v := DerivedCategory.Qh.map ((e.hom.mapHomotopyCategory (.up ℤ)).app J)
  rw [← Category.assoc]
  exact square_paste (C := schemeDerivedCategory.{u, w} (Spec R))
    (c₁.app (DerivedCategory.Qh.obj J)).symm (c₂.app (DerivedCategory.Qh.obj J)).symm
    u₁ u₂ _ _ d v _ hc₁ hc₂ hd' he

end AlgebraicGeometry
