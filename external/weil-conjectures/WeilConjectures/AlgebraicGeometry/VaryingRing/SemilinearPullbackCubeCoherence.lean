/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence

/-! # Ordinary semilinear inverse-image cube coherence

Source: Stacks Project, Tags 03DI, 0F7B and 0F7F.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
attribute [local instance] moduleJAdj_unit_isIso

attribute [local irreducible] moduleGComp moduleSquareG modulePComp moduleAdj
  Functor.leftAdjoint

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem direct_transport
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g)
    (N : Modules R φ X) (n : ℕ) (U : Y.ProEt)
    (x : ((push R φ f).obj N).val.obj (op (n, U))) :
    ((eqToIso (congrArg (push R φ) e)).hom.app N).val.app (op (n, U)) x =
      N.val.map (Prod.mkHom (𝟙 n)
        (eqToHom (congrArg (fun t ↦ (Scheme.proEtaleBaseChange t).obj U) e.symm))).op x := by
  cases e
  change x = N.val.map (𝟙 _) x
  rw [PresheafOfModules.map_id]
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem direct_comp_apply
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Modules R φ X) (n : ℕ) (U : Z.ProEt)
    (x : ((push R φ f ⋙ push R φ g).obj N).val.obj (op (n, U))) :
    ((modulePComp R φ f g).hom.app N).val.app (op (n, U)) x =
      N.val.map (Prod.mkHom (𝟙 n)
        ((MorphismProperty.Over.pullbackComp f g).hom.app U)).op x := by
  unfold modulePComp
  exact (modulePComp_existsUnique R φ f g).choose_spec.1 N n U x

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem direct_map_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) {N N' : Modules R φ X}
    (a : N ⟶ N') (n : ℕ) (U : Y.ProEt)
    (x : ((push R φ f).obj N).val.obj (op (n, U))) :
    (((push R φ f).map a).val.app (op (n, U))) x =
      a.val.app (op (n, (Scheme.proEtaleBaseChange f).obj U)) x := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem direct_obj_map_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Modules R φ X)
    (n : ℕ) {U V : Y.ProEt} (a : U ⟶ V)
    (x : ((push R φ f).obj N).val.obj (op (n, V))) :
    (((push R φ f).obj N).val.map (Prod.mkHom (𝟙 n) a).op) x =
      N.val.map (Prod.mkHom (𝟙 n) ((Scheme.proEtaleBaseChange f).map a)).op x := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem direct_coherence
    {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft (push R φ f) (modulePComp R φ g h) ≪≫
        modulePComp R φ f (g ≫ h) =
      (Functor.associator (push R φ f) (push R φ g) (push R φ h)).symm ≪≫
        Functor.isoWhiskerRight (modulePComp R φ f g) (push R φ h) ≪≫
        modulePComp R φ (f ≫ g) h ≪≫
        eqToIso (congrArg (push R φ) (Category.assoc f g h)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  rcases U with ⟨n, U⟩
  ext x
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [direct_map_apply R φ h ((modulePComp R φ f g).hom.app N) n U]
  erw [direct_comp_apply R φ f g N n ((Scheme.proEtaleBaseChange h).obj U)]
  erw [direct_comp_apply R φ (f ≫ g) h N n U]
  conv_rhs => erw [direct_transport R φ (Category.assoc f g h) N n U]
  conv_lhs => erw [direct_comp_apply R φ g h ((push R φ f).obj N) n U x]
  conv_lhs => erw [direct_comp_apply R φ f (g ≫ h) N n U]
  conv_lhs => erw [direct_obj_map_apply R φ f N n
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app U)]
  apply StrictTower.restriction_pasting N.val
  · apply Prod.hom_ext
    · simp
    · exact StrictTower.site_pasting (P := @WeaklyEtale) (Q := ⊤) f g h U

-- Ordinary inverse-image coherence is the adjoint of the section calculation.

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_coherence
    {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (M : Modules R φ T) :
    (moduleGComp R φ f (g ≫ h)).hom.app M ≫
        (pull R φ f).map ((moduleGComp R φ g h).hom.app M) =
      (eqToIso (congrArg (pull R φ)
        (Category.assoc f g h).symm)).hom.app M ≫
        (moduleGComp R φ (f ≫ g) h).hom.app M ≫
        (moduleGComp R φ f g).hom.app ((pull R φ h).obj M) := by
  have hh := Adjunction.leftAdjointCompIso_assoc
    (moduleAdj R φ h) (moduleAdj R φ g) (moduleAdj R φ f)
    (moduleAdj R φ (g ≫ h)) (moduleAdj R φ (f ≫ g))
    (moduleAdj R φ (f ≫ g ≫ h))
    (modulePComp R φ g h) (modulePComp R φ f g)
    ((modulePComp R φ (f ≫ g) h) ≪≫
      eqToIso (congrArg (push R φ) (Category.assoc f g h)))
    (modulePComp R φ f (g ≫ h)) (direct_coherence R φ f g h)
  have ht := StrictTower.mate_transport (pull R φ) (push R φ) (moduleAdj R φ)
    (moduleAdj R φ h) (moduleAdj R φ (f ≫ g)) (Category.assoc f g h)
    (modulePComp R φ (f ≫ g) h)
  rw [ht] at hh
  have hi := NatTrans.congr_app (congrArg Iso.inv hh) M
  simpa only [moduleGComp, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Iso.symm_inv, Category.id_comp, Category.comp_id, Category.assoc, eqToIso.inv, eqToIso.hom]
    using hi.symm

private def cubeComposition {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (t : A ⟶ C) (h : a ≫ b = t) :
    pull R φ b ⋙ pull R φ a ≅ pull R φ t :=
  (moduleGComp R φ a b).symm ≪≫ eqToIso (congrArg (pull R φ) h)

private theorem cubeComposition_assoc
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (ab : A ⟶ C) (bc : B ⟶ D) (t : A ⟶ D)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (ht : ab ≫ c = t) (ht' : a ≫ bc = t) (M : Modules R φ D) :
    (cubeComposition R φ a b ab hab).hom.app ((pull R φ c).obj M) ≫
      (cubeComposition R φ ab c t ht).hom.app M =
    (pull R φ a).map ((cubeComposition R φ b c bc hbc).hom.app M) ≫
      (cubeComposition R φ a bc t ht').hom.app M := by
  subst ab bc
  cases ht'
  have hi : eqToIso (congrArg (pull R φ) (Category.assoc a b c).symm) ≪≫
      moduleGComp R φ (a ≫ b) c ≪≫
      Functor.isoWhiskerLeft (pull R φ c) (moduleGComp R φ a b) =
      moduleGComp R φ a (b ≫ c) ≪≫
      Functor.isoWhiskerRight (moduleGComp R φ b c) (pull R φ a) := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    exact (ordinary_coherence R φ a b c N).symm
  have hh := congrArg (fun z ↦ z.inv.app M) hi
  simpa only [cubeComposition, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, NatTrans.id_app, Category.comp_id, Category.assoc] using hh

private def cubeSquare {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ D)
    (d : A ⟶ C) (e : C ⟶ D) (h : a ≫ b = d ≫ e) :
    pull R φ b ⋙ pull R φ a ⟶ pull R φ e ⋙ pull R φ d :=
  (cubeComposition R φ a b (d ≫ e) h).hom ≫
    (cubeComposition R φ d e (d ≫ e) rfl).inv

private theorem cubeSquare_cube
    {X X' S S' U U' V V' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (iU : U ⟶ X) (iU' : U' ⟶ X') (iV : V ⟶ S) (iV' : V' ⟶ S')
    (f₀ : U ⟶ V) (f₀' : U' ⟶ V') (g₀ : V' ⟶ V) (j : U' ⟶ U)
    (hd : f₀ ≫ iV = iU ≫ f) (hd' : f₀' ≫ iV' = iU' ≫ f')
    (he : g₀ ≫ iV = iV' ≫ g) (hj : j ≫ iU = iU' ≫ g')
    (h₀ : j ≫ f₀ = f₀' ≫ g₀) (M : Modules R φ S) :
    (cubeSquare R φ f₀' g₀ j f₀ h₀.symm).app ((pull R φ iV).obj M) ≫
        (pull R φ j).map ((cubeSquare R φ f₀ iV iU f hd).app M) ≫
        (cubeSquare R φ j iU iU' g' hj).app ((pull R φ f).obj M) =
      (pull R φ f₀').map ((cubeSquare R φ g₀ iV iV' g he).app M) ≫
        (cubeSquare R φ f₀' iV' iU' f' hd').app ((pull R φ g).obj M) ≫
        (pull R φ iU').map ((cubeSquare R φ f' g g' f h.symm).app M) := by
  classical
  let t := j ≫ (iU ≫ f)
  have ht₄ : (iU' ≫ g') ≫ f = t := by
    dsimp only [t]
    rw [← hj, Category.assoc]
  have ht₅ : (j ≫ f₀) ≫ iV = t := by
    dsimp only [t]
    rw [Category.assoc, hd]
  have ht₃ : f₀' ≫ (iV' ≫ g) = t := by
    dsimp only [t]
    rw [← he, ← Category.assoc, ← h₀, Category.assoc, hd]
  have ht₂ : (iU' ≫ f') ≫ g = t := by
    rw [Category.assoc, ← h, ← Category.assoc, ht₄]
  have ht₆ : iU' ≫ (g' ≫ f) = t := by
    rw [← Category.assoc, ht₄]
  have ha := cubeComposition_assoc R φ j iU f (iU' ≫ g') (iU ≫ f) t
    hj rfl ht₄ rfl M
  have hb := cubeComposition_assoc R φ j f₀ iV (j ≫ f₀) (iU ≫ f) t
    rfl hd ht₅ rfl M
  have hc := cubeComposition_assoc R φ f₀' g₀ iV (j ≫ f₀) (iV' ≫ g) t
    h₀.symm he ht₅ ht₃ M
  have hd₁ := cubeComposition_assoc R φ iU' g' f (iU' ≫ g') (g' ≫ f) t
    rfl rfl ht₄ ht₆ M
  have hd₂ := cubeComposition_assoc R φ iU' f' g (iU' ≫ f') (g' ≫ f) t
    rfl h.symm ht₂ ht₆ M
  have hd₃ := cubeComposition_assoc R φ f₀' iV' g (iU' ≫ f') (iV' ≫ g) t
    hd' rfl ht₂ ht₃ M
  apply (cancel_mono
    ((cubeComposition R φ iU' g' (iU' ≫ g') rfl).hom.app ((pull R φ f).obj M) ≫
      (cubeComposition R φ (iU' ≫ g') f t ht₄).hom.app M)).mp
  simp only [cubeSquare, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [ha]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [← hb]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [hc]
  rw [hd₁]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [← hd₂]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [hd₃]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem cubeSquare_eq {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ D)
    (d : A ⟶ C) (e : C ⟶ D) (h : a ≫ b = d ≫ e) :
    cubeSquare R φ a b d e h = (moduleSquareG R φ a d b e h).inv := by
  rw [moduleSquareG_eq]
  simp only [cubeSquare, cubeComposition, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, eqToIso_refl, Iso.refl_inv,
    eqToIso.hom, eqToIso.inv, Category.id_comp, Category.assoc]

private theorem cubeSquare_swap {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ D)
    (d : A ⟶ C) (e : C ⟶ D) (h : a ≫ b = d ≫ e) :
    cubeSquare R φ d e a b h.symm = (moduleSquareG R φ a d b e h).hom := by
  rw [moduleSquareG_eq]
  simp only [cubeSquare, cubeComposition, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, eqToIso_refl, Iso.refl_inv,
    eqToIso.hom, Category.id_comp, Category.assoc]

/-- The canonical ordinary inverse-image comparisons agree around a commutative cube.
No cartesian, open, or proper hypothesis is needed.
Source: Stacks Project, Tags 03D8, 07A7 and the compositor calculation in Tag 0F7F
(blueprint: lem-sf-semilinear-pullback-cube-coherence).
Proof: expand each square comparison as inverse composition, equality transport,
and forward composition. Direct-image composition is identity on section carriers
up to the canonical iterated fibre-product comparison. The universal property of
the fibre product identifies its two triple-composition maps. Taking adjoints gives
inverse-image associativity. Use this associativity on both sides of the cube and
cancel inverse composition comparisons. Both resulting maps are the comparison
from k1-star p1-star h-star to r1-star c-star i-star along the same scheme composite.
Equality transports agree by proof irrelevance. -/
theorem moduleSquareG_cube
    {U V W Z U₁ V₁ W₁ Z₁ : Scheme.{u}}
    (k : U ⟶ V) (i : W ⟶ Z) (r : U ⟶ W) (p : V ⟶ Z)
    (k₁ : U₁ ⟶ V₁) (i₁ : W₁ ⟶ Z₁) (r₁ : U₁ ⟶ W₁) (p₁ : V₁ ⟶ Z₁)
    (a : V₁ ⟶ V) (h : Z₁ ⟶ Z) (c : W₁ ⟶ W) (d : U₁ ⟶ U)
    (w : k ≫ p = r ≫ i) (w₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ h)
    (wp : a ≫ p = p₁ ≫ h) (wr : d ≫ r = r₁ ≫ c) (M : Modules R φ Z) :
    (moduleSquareG R φ k₁ r₁ p₁ i₁ w₁).inv.app ((pull R φ h).obj M) ≫
        (pull R φ r₁).map ((moduleSquareG R φ c i₁ i h wi).hom.app M) =
      (pull R φ k₁).map ((moduleSquareG R φ a p₁ p h wp).hom.app M) ≫
        (moduleSquareG R φ d k₁ k a wk).hom.app ((pull R φ p).obj M) ≫
        (pull R φ d).map ((moduleSquareG R φ k r p i w).inv.app M) ≫
        (moduleSquareG R φ d r₁ r c wr).inv.app ((pull R φ i).obj M) := by
  have H := cubeSquare_cube R φ i i₁ h c wi r r₁ p p₁ k k₁ a d
    w w₁ wp wr wk M
  rw [cubeSquare_swap R φ d k k₁ a wk,
    cubeSquare_eq R φ k p r i w,
    cubeSquare_eq R φ d r r₁ c wr,
    cubeSquare_eq R φ a p p₁ h wp,
    cubeSquare_eq R φ k₁ p₁ r₁ i₁ w₁,
    cubeSquare_swap R φ c i i₁ h wi] at H
  rw [← cancel_epi ((pull R φ k₁).map
    ((moduleSquareG R φ a p₁ p h wp).inv.app M))]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact H.symm

end AlgebraicGeometry.ProEtale.VaryingRing
