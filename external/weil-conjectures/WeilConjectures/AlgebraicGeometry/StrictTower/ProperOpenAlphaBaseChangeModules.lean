/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.CategoryTheory.ExactDerivedPasting.ExactDerivedPastingComponents
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import all WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenAlphaRestriction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono

/-! # Intrinsic alpha baseChange identity on module sheaves

Source: Stacks Project, Tag 0F7F, with the arbitrary-ring underived refinement.
(blueprint: lem-cbc-proper-open-alpha-base-change-modules)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

attribute [local irreducible] Functor.leftAdjoint modulePullback singleAlpha moduleGComp
attribute [local irreducible] moduleSquareG openBetaModule openBetaModuleJComp

private instance cubeUnitIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (moduleJAdj B j).unit :=
  clopenModule_openUnit_isIso B j

private theorem cubeAlphaRestriction {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Modules B S) :
    (modulePullback B k).map ((singleAlpha B k r p i h).app M) ≫
        inv ((moduleJAdj B k).unit.app ((modulePullback B r).obj M)) =
      (moduleSquareG B k r p i h).inv.app ((moduleJ B i).obj M) ≫
        (modulePullback B r).map (inv ((moduleJAdj B i).unit.app M)) := by
  simpa only [moduleOpenUnitInv, NatIso.isIso_inv_app] using
    singleAlpha_restriction B k r p i h M

private theorem moduleJ_map_injective {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {N : Modules B X} {M : Modules B U}
    (f g : N ⟶ (moduleJ B j).obj M)
    (h : (modulePullback B j).map f = (modulePullback B j).map g) : f = g := by
  let A := ModuleCat.{u + 1} B
  let P := fixedRestriction B X
  let R := upperStar A j
  let e := (fixedOpen B j).app M
  have he : R.map (P.map f ≫ e.hom) = R.map (P.map g ≫ e.hom) := by
    apply (cancel_epi ((fixedPull B j).hom.app N)).1
    simp only [Functor.map_comp, ← Category.assoc]
    have hf := (fixedPull B j).hom.naturality f
    have hg := (fixedPull B j).hom.naturality g
    dsimp only [Functor.comp_map] at hf hg
    rw [← hf, ← hg]
    rw [h]
  have hm : P.map f ≫ e.hom = P.map g ≫ e.hom := by
    have := mono_openImmersionLowerShriekToLowerStar_app A j
      ((fixedRestriction B U).obj M)
    apply (cancel_mono ((openImmersionLowerShriekToLowerStar A j).app
      ((fixedRestriction B U).obj M))).1
    apply ((upperStarLowerStarAdjunction A j).homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp]
    have he' := he
    dsimp only [R] at he'
    simp only [Functor.map_comp] at he'
    rw [he']
  exact P.map_injective ((cancel_mono e.hom).1 hm)

private def cubeComposition {A B₀ C : Scheme.{u}} (a : A ⟶ B₀) (b : B₀ ⟶ C)
    (t : A ⟶ C) (h : a ≫ b = t) :
    modulePullback B b ⋙ modulePullback B a ≅ modulePullback B t :=
  (moduleGComp B a b).symm ≪≫ eqToIso (congrArg (modulePullback B) h)

private theorem cubeComposition_assoc
    {A B₀ C D : Scheme.{u}} (a : A ⟶ B₀) (b : B₀ ⟶ C) (c : C ⟶ D)
    (ab : A ⟶ C) (bc : B₀ ⟶ D) (t : A ⟶ D)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (ht : ab ≫ c = t) (ht' : a ≫ bc = t) (M : Modules B D) :
    (cubeComposition B a b ab hab).hom.app ((modulePullback B c).obj M) ≫
      (cubeComposition B ab c t ht).hom.app M =
    (modulePullback B a).map ((cubeComposition B b c bc hbc).hom.app M) ≫
      (cubeComposition B a bc t ht').hom.app M := by
  subst ab bc
  cases ht'
  have hi : eqToIso (congrArg (modulePullback B) (Category.assoc a b c).symm) ≪≫
      moduleGComp B (a ≫ b) c ≪≫
      Functor.isoWhiskerLeft (modulePullback B c) (moduleGComp B a b) =
      moduleGComp B a (b ≫ c) ≪≫
      Functor.isoWhiskerRight (moduleGComp B b c) (modulePullback B a) := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    exact (ordinary_coherence a b c B N).symm
  have hh := congrArg (fun z ↦ z.inv.app M) hi
  simpa only [cubeComposition, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, NatTrans.id_app, Category.comp_id, Category.assoc] using hh

private def cubeSquare {A B₀ C D : Scheme.{u}} (a : A ⟶ B₀) (b : B₀ ⟶ D)
    (d : A ⟶ C) (e : C ⟶ D) (h : a ≫ b = d ≫ e) :
    modulePullback B b ⋙ modulePullback B a ⟶ modulePullback B e ⋙ modulePullback B d :=
  (cubeComposition B a b (d ≫ e) h).hom ≫
    (cubeComposition B d e (d ≫ e) rfl).inv

private theorem cubeSquare_cube
    {X X' S S' U U' V V' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (iU : U ⟶ X) (iU' : U' ⟶ X') (iV : V ⟶ S) (iV' : V' ⟶ S')
    (f₀ : U ⟶ V) (f₀' : U' ⟶ V') (g₀ : V' ⟶ V) (j : U' ⟶ U)
    (hd : f₀ ≫ iV = iU ≫ f) (hd' : f₀' ≫ iV' = iU' ≫ f')
    (he : g₀ ≫ iV = iV' ≫ g) (hj : j ≫ iU = iU' ≫ g')
    (h₀ : j ≫ f₀ = f₀' ≫ g₀) (M : Modules B S) :
    (cubeSquare B f₀' g₀ j f₀ h₀.symm).app ((modulePullback B iV).obj M) ≫
        (modulePullback B j).map ((cubeSquare B f₀ iV iU f hd).app M) ≫
        (cubeSquare B j iU iU' g' hj).app ((modulePullback B f).obj M) =
      (modulePullback B f₀').map ((cubeSquare B g₀ iV iV' g he).app M) ≫
        (cubeSquare B f₀' iV' iU' f' hd').app ((modulePullback B g).obj M) ≫
        (modulePullback B iU').map ((cubeSquare B f' g g' f h.symm).app M) := by
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
  have ha := cubeComposition_assoc B j iU f (iU' ≫ g') (iU ≫ f) t
    hj rfl ht₄ rfl M
  have hb := cubeComposition_assoc B j f₀ iV (j ≫ f₀) (iU ≫ f) t
    rfl hd ht₅ rfl M
  have hc := cubeComposition_assoc B f₀' g₀ iV (j ≫ f₀) (iV' ≫ g) t
    h₀.symm he ht₅ ht₃ M
  have hd₁ := cubeComposition_assoc B iU' g' f (iU' ≫ g') (g' ≫ f) t
    rfl rfl ht₄ ht₆ M
  have hd₂ := cubeComposition_assoc B iU' f' g (iU' ≫ f') (g' ≫ f) t
    rfl h.symm ht₂ ht₆ M
  have hd₃ := cubeComposition_assoc B f₀' iV' g (iU' ≫ f') (iV' ≫ g) t
    hd' rfl ht₂ ht₃ M
  apply (cancel_mono
    ((cubeComposition B iU' g' (iU' ≫ g') rfl).hom.app ((modulePullback B f).obj M) ≫
      (cubeComposition B (iU' ≫ g') f t ht₄).hom.app M)).mp
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

private theorem cubeSquare_eq {A B₀ C D : Scheme.{u}} (a : A ⟶ B₀) (b : B₀ ⟶ D)
    (d : A ⟶ C) (e : C ⟶ D) (h : a ≫ b = d ≫ e) :
    cubeSquare B a b d e h = (moduleSquareG B a d b e h).inv := by
  rw [moduleSquareG_eq]
  simp only [cubeSquare, cubeComposition, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, eqToIso_refl, Iso.refl_inv,
    eqToIso.hom, eqToIso.inv, Category.id_comp, Category.assoc]

private theorem cubeSquare_swap {A B₀ C D : Scheme.{u}} (a : A ⟶ B₀) (b : B₀ ⟶ D)
    (d : A ⟶ C) (e : C ⟶ D) (h : a ≫ b = d ≫ e) :
    cubeSquare B d e a b h.symm = (moduleSquareG B a d b e h).hom := by
  rw [moduleSquareG_eq]
  simp only [cubeSquare, cubeComposition, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, eqToIso_refl, Iso.refl_inv,
    eqToIso.hom, Category.id_comp, Category.assoc]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem constantSquareCube
    {U V W Z U₁ V₁ W₁ Z₁ : Scheme.{u}}
    (k : U ⟶ V) (i : W ⟶ Z) (r : U ⟶ W) (p : V ⟶ Z)
    (k₁ : U₁ ⟶ V₁) (i₁ : W₁ ⟶ Z₁) (r₁ : U₁ ⟶ W₁) (p₁ : V₁ ⟶ Z₁)
    (a : V₁ ⟶ V) (h : Z₁ ⟶ Z) (c : W₁ ⟶ W) (d : U₁ ⟶ U)
    (w : k ≫ p = r ≫ i) (w₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ h)
    (wp : a ≫ p = p₁ ≫ h) (wr : d ≫ r = r₁ ≫ c) (M : Modules B Z) :
    (moduleSquareG B k₁ r₁ p₁ i₁ w₁).inv.app ((modulePullback B h).obj M) ≫
        (modulePullback B r₁).map ((moduleSquareG B c i₁ i h wi).hom.app M) =
      (modulePullback B k₁).map ((moduleSquareG B a p₁ p h wp).hom.app M) ≫
        (moduleSquareG B d k₁ k a wk).hom.app ((modulePullback B p).obj M) ≫
        (modulePullback B d).map ((moduleSquareG B k r p i w).inv.app M) ≫
        (moduleSquareG B d r₁ r c wr).inv.app ((modulePullback B i).obj M) := by
  have H := cubeSquare_cube B i i₁ h c wi r r₁ p p₁ k k₁ a d
    w w₁ wp wr wk M
  rw [cubeSquare_swap B d k k₁ a wk,
    cubeSquare_eq B k p r i w,
    cubeSquare_eq B d r r₁ c wr,
    cubeSquare_eq B a p p₁ h wp,
    cubeSquare_eq B k₁ p₁ r₁ i₁ w₁,
    cubeSquare_swap B c i i₁ h wi] at H
  have H' := congrArg (fun z ↦ (modulePullback B k₁).map
    ((moduleSquareG B a p₁ p h wp).hom.app M) ≫ z) H
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app] at H'
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at H'
  exact H'.symm

/-- Intrinsic alpha obeys cube pasting on module sheaves.
Source: Stacks, Tag 0F7F, and the parent restriction argument, steps 1--3 and 6
(blueprint: lem-cbc-proper-open-alpha-base-change-modules).
Proof: Restriction detects maps into open extension: transport to fixed-scalar sheaves,
compose with the monomorphism from open extension to direct image, and use the
restriction/direct-image adjunction. Faithfulness transports equality back to modules.
The inverse-transpose definition of beta gives its restriction normalization through
the specified open units. The clopen projector restricts to the identity, so intrinsic
alpha restricts to the canonical inverse-image square identification followed by
inverse image of the inverse open unit. All detection opens are quasi-compact.
For base change, restrict along k₁. The original-alpha route reduces through
ak₁ = kd to d* r*, then through rd = cr₁ to r₁* c*. The beta for k is exactly
the open-unit identification. On the changed-alpha route the beta for i first gives
that same open-unit identification, and intrinsic alpha for Q₁ reduces to r₁* c*.
The square identification for p₁ followed by b equal to a followed by p makes the
starting comparisons equal.
Detection gives the cube equation without proper direct-image base change.
Apply this calculation to every module sheaf M to obtain the displayed component
identity. Empty schemes and the zero coefficient ring give the unique zero maps;
identity opens give the unit-normalized inverse-image compositor identity. -/
theorem singleAlpha_baseChange {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
    (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
    (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c) :
    ∀ M : Modules B S,
      (moduleSquareG B a p₁ p b wp).hom.app ((moduleJ B i).obj M) ≫
          (modulePullback B a).map ((singleAlpha B k r p i h).app M) ≫
          (openBetaModule B d k₁ k a wk sk).hom.app ((modulePullback B r).obj M) ≫
          (moduleJ B k₁).map ((moduleSquareG B d r₁ r c wr).inv.app M) =
        (modulePullback B p₁).map ((openBetaModule B c i₁ i b wi si).hom.app M) ≫
          (singleAlpha B k₁ r₁ p₁ i₁ h₁).app ((modulePullback B c).obj M) := by
  intro M
  have _sp := sp
  have _sr := sr
  symm
  apply moduleJ_map_injective B k₁
  apply (cancel_mono (inv ((moduleJAdj B k₁).unit.app
    ((modulePullback B r₁).obj ((modulePullback B c).obj M))))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [cubeAlphaRestriction]
  have hn := (moduleSquareG B k₁ r₁ p₁ i₁ h₁).inv.naturality
    ((openBetaModule B c i₁ i b wi si).hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    beta_restriction, Functor.map_comp]
  have hu := (asIso (moduleJAdj B k₁).unit).inv.naturality
    ((moduleSquareG B d r₁ r c wr).inv.app M)
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj,
    asIso_inv, NatIso.isIso_inv_app] at hu
  rw [hu]
  slice_rhs 3 4 => rw [beta_restriction]
  have hk := (moduleSquareG B d k₁ k a wk).hom.naturality
    ((singleAlpha B k r p i h).app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hk
  slice_rhs 2 3 => rw [hk]
  slice_rhs 3 4 => rw [← Functor.map_comp, cubeAlphaRestriction, Functor.map_comp]
  have hr := (moduleSquareG B d r₁ r c wr).inv.naturality
    (inv ((moduleJAdj B i).unit.app M))
  simp only [Functor.comp_map, Functor.comp_obj] at hr
  simp only [Functor.comp_obj, Functor.id_obj] at hr ⊢
  slice_rhs 4 5 => rw [hr]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ (modulePullback B r₁).map ((modulePullback B c).map
      (inv ((moduleJAdj B i).unit.app M))))
    (constantSquareCube B k i r p k₁ i₁ r₁ p₁ a b c d
      h h₁ wk wi wp wr ((moduleJ B i).obj M))

open CategoryTheory.ExactDerivedPasting
set_option linter.unusedSimpArgs false

private structure NativeCubeData (Xv Xs Xw Xt Xv₁ Xs₁ Xw₁ Xt₁ : Scheme.{u}) where
  K : Modules B Xv ⥤ Modules B Xw
  V : Modules B Xs ⥤ Modules B Xt
  R : Modules B Xs ⥤ Modules B Xv
  P : Modules B Xt ⥤ Modules B Xw
  K₁ : Modules B Xv₁ ⥤ Modules B Xw₁
  V₁ : Modules B Xs₁ ⥤ Modules B Xt₁
  R₁ : Modules B Xs₁ ⥤ Modules B Xv₁
  P₁ : Modules B Xt₁ ⥤ Modules B Xw₁
  A : Modules B Xw ⥤ Modules B Xw₁
  B' : Modules B Xt ⥤ Modules B Xt₁
  C' : Modules B Xs ⥤ Modules B Xs₁
  D : Modules B Xv ⥤ Modules B Xv₁
  ao : V ⋙ P ⟶ R ⋙ K
  a₁ : V₁ ⋙ P₁ ⟶ R₁ ⋙ K₁
  bk : K ⋙ A ≅ D ⋙ K₁
  bi : V ⋙ B' ≅ C' ⋙ V₁
  sp : B' ⋙ P₁ ≅ P ⋙ A
  sr : C' ⋙ R₁ ≅ R ⋙ D
  h : ∀ M : Modules B Xs,
      sp.hom.app (V.obj M) ≫ A.map (ao.app M) ≫ bk.hom.app (R.obj M) ≫
          K₁.map (sr.inv.app M) =
        P₁.map (bi.hom.app M) ≫ a₁.app (C'.obj M)

@[irreducible] private def nativeCubeData {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
    (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
    (hp : IsPullback a p₁ p b) (hr : IsPullback d r₁ r c) :
    NativeCubeData B V S W T V₁ S₁ W₁ T₁ where
  K := moduleJ B k
  V := moduleJ B i
  R := modulePullback B r
  P := modulePullback B p
  K₁ := moduleJ B k₁
  V₁ := moduleJ B i₁
  R₁ := modulePullback B r₁
  P₁ := modulePullback B p₁
  A := modulePullback B a
  B' := modulePullback B b
  C' := modulePullback B c
  D := modulePullback B d
  ao := singleAlpha B k r p i h
  a₁ := singleAlpha B k₁ r₁ p₁ i₁ h₁
  bk := openBetaModule B d k₁ k a wk sk
  bi := openBetaModule B c i₁ i b wi si
  sp := moduleSquareG B a p₁ p b wp
  sr := moduleSquareG B d r₁ r c wr
  h := singleAlpha_baseChange B k i r p k₁ i₁ r₁ p₁ a b c d h h₁ wk wi wp wr sk si hp hr

private theorem nativeCubeLaw {V S W T V₁ S₁ W₁ T₁ : Scheme.{u}}
    (T₀ : NativeCubeData B V S W T V₁ S₁ W₁ T₁) :
    Functor.whiskerLeft (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.V) (twIso (fun X :
      Scheme.{u} ↦ Modules B X) T₀.B' T₀.P₁ T₀.P T₀.A T₀.sp).hom ≫
        (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.V) (twFunctor (fun X
      : Scheme.{u} ↦ Modules B X) T₀.P) (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.A)).inv ≫
        Functor.whiskerRight
          (Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ T₀.V T₀.P T₀.R T₀.K T₀.ao)
          (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.A) ≫
        (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.R) (twFunctor (fun X
      : Scheme.{u} ↦ Modules B X) T₀.K) (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.A)).hom ≫
        Functor.whiskerLeft (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.R) (twIso (fun X :
      Scheme.{u} ↦ Modules B X) T₀.K T₀.A T₀.D T₀.K₁ T₀.bk).hom ≫
        (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.R) (twFunctor (fun X
      : Scheme.{u} ↦ Modules B X) T₀.D) (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.K₁)).inv ≫
        Functor.whiskerRight (twIso (fun X : Scheme.{u} ↦ Modules B X) T₀.C' T₀.R₁ T₀.R T₀.D
      T₀.sr).inv (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.K₁) =
      (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.V) (twFunctor (fun X :
      Scheme.{u} ↦ Modules B X) T₀.B') (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.P₁)).inv ≫
        Functor.whiskerRight (twIso (fun X : Scheme.{u} ↦ Modules B X) T₀.V T₀.B' T₀.C' T₀.V₁
      T₀.bi).hom (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.P₁) ≫
        (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.C') (twFunctor (fun
      X : Scheme.{u} ↦ Modules B X) T₀.V₁) (twFunctor (fun X : Scheme.{u} ↦ Modules B X)
      T₀.P₁)).hom ≫
        Functor.whiskerLeft (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.C')
          (Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ T₀.V₁ T₀.P₁ T₀.R₁ T₀.K₁ T₀.a₁) ≫
        (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.C') (twFunctor (fun
      X : Scheme.{u} ↦ Modules B X) T₀.R₁) (twFunctor (fun X : Scheme.{u} ↦ Modules B X)
      T₀.K₁)).inv :=
  @cubeTowerLaw Scheme.{u} (fun X : Scheme.{u} ↦ Modules B X)
    (fun X ↦ inferInstanceAs (Category.{u + 1} (Modules B X))) V S W T V₁ S₁ W₁ T₁
    T₀.K T₀.V T₀.R T₀.P T₀.K₁ T₀.V₁ T₀.R₁ T₀.P₁ T₀.A T₀.B' T₀.C' T₀.D T₀.ao T₀.a₁ T₀.bk T₀.bi
      T₀.sp T₀.sr T₀.h

private theorem towerAlpha_baseChange {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
    (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
    (hp : IsPullback a p₁ p b) (hr : IsPullback d r₁ r c) :
    Functor.whiskerLeft (towerJ B i) ((towerSquare (modulePullback B b) (modulePullback B p₁)
      (modulePullback B p) (modulePullback B a) (moduleSquareG B a p₁ p b wp)).hom) ≫
      (Functor.associator (towerJ B i) (towerPullback B p) (towerPullback B a)).inv ≫
        Functor.whiskerRight (towerAlpha B k r p i h) (towerPullback B a) ≫ (Functor.associator
      (towerPullback B r) (towerJ B k) (towerPullback B a)).hom ≫
        Functor.whiskerLeft (towerPullback B r) ((openBetaTower B d k₁ k a wk sk).hom) ≫
      (Functor.associator (towerPullback B r) (towerPullback B d) (towerJ B k₁)).inv ≫
        Functor.whiskerRight ((towerSquare (modulePullback B c) (modulePullback B r₁)
      (modulePullback B r) (modulePullback B d) (moduleSquareG B d r₁ r c wr)).inv) (towerJ B k₁) =
      (Functor.associator (towerJ B i) (towerPullback B b) (towerPullback B p₁)).inv ≫
      Functor.whiskerRight ((openBetaTower B c i₁ i b wi si).hom) (towerPullback B p₁) ≫
        (Functor.associator (towerPullback B c) (towerJ B i₁) (towerPullback B p₁)).hom ≫
      Functor.whiskerLeft (towerPullback B c) (towerAlpha B k₁ r₁ p₁ i₁ h₁) ≫
        (Functor.associator (towerPullback B c) (towerPullback B r₁) (towerJ B k₁)).inv := by
  with_unfolding_all
    exact nativeCubeLaw B (nativeCubeData B k i r p k₁ i₁ r₁ p₁ a b c d h h₁ wk wi wp wr sk si hp
      hr)

-- Capture the public derived-category instances before installing the tower instance.
private abbrev nativeCubeDerivedFunctor (X Y : Scheme.{u}) :=
  Derived B X ⥤ Derived B Y

section DerivedTransport
attribute [local instance] exactPairAdditive
attribute [local instance] clopenTowerAbelian towers_hasDerivedCategory
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] G J alpha beta gComp jComp squareG

private theorem nativeCubeDerivedExternal {Xv Xs Xw Xt Xv₁ Xs₁ Xw₁ Xt₁ : Scheme.{u}}
    (K : Towers B Xv ⥤ₑ Towers B Xw)
    (V : Towers B Xs ⥤ₑ Towers B Xt)
    (R : Towers B Xs ⥤ₑ Towers B Xv)
    (P : Towers B Xt ⥤ₑ Towers B Xw)
    (K₁ : Towers B Xv₁ ⥤ₑ Towers B Xw₁)
    (V₁ : Towers B Xs₁ ⥤ₑ Towers B Xt₁)
    (R₁ : Towers B Xs₁ ⥤ₑ Towers B Xv₁)
    (P₁ : Towers B Xt₁ ⥤ₑ Towers B Xw₁)
    (A : Towers B Xw ⥤ₑ Towers B Xw₁)
    (B' : Towers B Xt ⥤ₑ Towers B Xt₁)
    (C' : Towers B Xs ⥤ₑ Towers B Xs₁)
    (D : Towers B Xv ⥤ₑ Towers B Xv₁)
    (KD : nativeCubeDerivedFunctor B Xv Xw)
    (VD : nativeCubeDerivedFunctor B Xs Xt)
    (RD : nativeCubeDerivedFunctor B Xs Xv)
    (PD : nativeCubeDerivedFunctor B Xt Xw)
    (K₁D : nativeCubeDerivedFunctor B Xv₁ Xw₁)
    (V₁D : nativeCubeDerivedFunctor B Xs₁ Xt₁)
    (R₁D : nativeCubeDerivedFunctor B Xs₁ Xv₁)
    (P₁D : nativeCubeDerivedFunctor B Xt₁ Xw₁)
    (AD : nativeCubeDerivedFunctor B Xw Xw₁)
    (BD : nativeCubeDerivedFunctor B Xt Xt₁)
    (CD : nativeCubeDerivedFunctor B Xs Xs₁)
    (DD : nativeCubeDerivedFunctor B Xv Xv₁)
    (hKD : K.obj.mapDerivedCategory = KD)
    (hVD : V.obj.mapDerivedCategory = VD)
    (hRD : R.obj.mapDerivedCategory = RD)
    (hPD : P.obj.mapDerivedCategory = PD)
    (hK₁D : K₁.obj.mapDerivedCategory = K₁D)
    (hV₁D : V₁.obj.mapDerivedCategory = V₁D)
    (hR₁D : R₁.obj.mapDerivedCategory = R₁D)
    (hP₁D : P₁.obj.mapDerivedCategory = P₁D)
    (hAD : A.obj.mapDerivedCategory = AD)
    (hBD : B'.obj.mapDerivedCategory = BD)
    (hCD : C'.obj.mapDerivedCategory = CD)
    (hDD : D.obj.mapDerivedCategory = DD)
    (ao : V.obj ⋙ P.obj ⟶ R.obj ⋙ K.obj)
    (a₁ : V₁.obj ⋙ P₁.obj ⟶ R₁.obj ⋙ K₁.obj)
    (bk : K.obj ⋙ A.obj ⟶ D.obj ⋙ K₁.obj)
    (bi : V.obj ⋙ B'.obj ⟶ C'.obj ⋙ V₁.obj)
    (sp : B'.obj ⋙ P₁.obj ⟶ P.obj ⋙ A.obj)
    (sr : R.obj ⋙ D.obj ⟶ C'.obj ⋙ R₁.obj)
    (d₀ : VD ⋙ PD ⟶
      RD ⋙ KD)
    (d₁ : V₁D ⋙ P₁D ⟶
      R₁D ⋙ K₁D)
    (dbk : KD ⋙ AD ⟶
      DD ⋙ K₁D)
    (dbi : VD ⋙ BD ⟶
      CD ⋙ V₁D)
    (dp : BD ⋙ P₁D ⟶
      PD ⋙ AD)
    (dr : RD ⋙ DD ⟶
      CD ⋙ R₁D)
    (c₀ : HEq (Word.cell (pastingCategories B) (P := .comp (.edge V) (.edge P))
      (R := .comp (.edge R) (.edge K)) ao) d₀)
    (c₁ : HEq (Word.cell (pastingCategories B) (P := .comp (.edge V₁) (.edge P₁))
      (R := .comp (.edge R₁) (.edge K₁)) a₁) d₁)
    (ckFac : HEq (Word.cell (pastingCategories B) (P := .comp (.edge K) (.edge A))
      (R := .comp (.edge D) (.edge K₁)) bk) dbk)
    (ciFac : HEq (Word.cell (pastingCategories B) (P := .comp (.edge V) (.edge B'))
      (R := .comp (.edge C') (.edge V₁)) bi) dbi)
    (cpFac : HEq (Word.cell (pastingCategories B) (P := .comp (.edge B') (.edge P₁))
      (R := .comp (.edge P) (.edge A)) sp) dp)
    (crFac : HEq (Word.cell (pastingCategories B) (P := .comp (.edge R) (.edge D))
      (R := .comp (.edge C') (.edge R₁)) sr) dr)
    (law : Functor.whiskerLeft V.obj sp ≫ (Functor.associator V.obj P.obj A.obj).inv ≫
        Functor.whiskerRight ao A.obj ≫ (Functor.associator R.obj K.obj A.obj).hom ≫
        Functor.whiskerLeft R.obj bk ≫ (Functor.associator R.obj D.obj K₁.obj).inv ≫
        Functor.whiskerRight sr K₁.obj =
      (Functor.associator V.obj B'.obj P₁.obj).inv ≫ Functor.whiskerRight bi P₁.obj ≫
        (Functor.associator C'.obj V₁.obj P₁.obj).hom ≫ Functor.whiskerLeft C'.obj a₁ ≫
        (Functor.associator C'.obj R₁.obj K₁.obj).inv)
    : ∀ N : Derived B Xs,
      dp.app (VD.obj N) ≫ AD.map (d₀.app
      N) ≫
          dbk.app (RD.obj N) ≫ K₁D.map
      (dr.app N) =
        P₁D.map (dbi.app N) ≫ d₁.app
      (CD.obj N) := by
  cases hKD
  cases hVD
  cases hRD
  cases hPD
  cases hK₁D
  cases hV₁D
  cases hR₁D
  cases hP₁D
  cases hAD
  cases hBD
  cases hCD
  cases hDD
  exact
    @genericCubeDerived Scheme.{u} (pastingCategories B)
      (fun X ↦ inferInstanceAs (Category.{u + 1} (Towers B X)))
      (fun X ↦ clopenTowerAbelian B X) (fun X ↦ towers_hasDerivedCategory B X)
      Xv Xs Xw Xt Xv₁ Xs₁ Xw₁ Xt₁
      K V R P K₁ V₁ R₁ P₁ A B' C' D ao a₁ bk bi
        sp sr d₀ d₁ dbk dbi dp dr (eq_of_heq c₀) (eq_of_heq c₁) (eq_of_heq ckFac)
        (eq_of_heq ciFac) (eq_of_heq cpFac)
        (eq_of_heq crFac) law

private theorem cube_derived {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
    (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
    (hp : IsPullback a p₁ p b) (hr : IsPullback d r₁ r c) :
    ∀ N : Derived B S,
      (squareG B a p₁ p b wp).hom.app ((J B i).obj N) ≫
          (G B a).map ((alpha B k r p i h).app N) ≫
          (beta B d k₁ k a wk sk).hom.app ((G B r).obj N) ≫
          (J B k₁).map ((squareG B d r₁ r c wr).inv.app N) =
        (G B p₁).map ((beta B c i₁ i b wi si).hom.app N) ≫
          (alpha B k₁ r₁ p₁ i₁ h₁).app ((G B c).obj N) := by
  exact @nativeCubeDerivedExternal B _ V S W T V₁ S₁ W₁ T₁
    (ExactFunctor.of (towerJ B k))
    (ExactFunctor.of (towerJ B i))
    (ExactFunctor.of (towerPullback B r))
    (ExactFunctor.of (towerPullback B p))
    (ExactFunctor.of (towerJ B k₁))
    (ExactFunctor.of (towerJ B i₁))
    (ExactFunctor.of (towerPullback B r₁))
    (ExactFunctor.of (towerPullback B p₁))
    (ExactFunctor.of (towerPullback B a))
    (ExactFunctor.of (towerPullback B b))
    (ExactFunctor.of (towerPullback B c))
    (ExactFunctor.of (towerPullback B d))
    (by
      with_unfolding_all
        exact J B k)
    (by
      with_unfolding_all
        exact J B i)
    (by
      with_unfolding_all
        exact G B r)
    (by
      with_unfolding_all
        exact G B p)
    (by
      with_unfolding_all
        exact J B k₁)
    (by
      with_unfolding_all
        exact J B i₁)
    (by
      with_unfolding_all
        exact G B r₁)
    (by
      with_unfolding_all
        exact G B p₁)
    (by
      with_unfolding_all
        exact G B a)
    (by
      with_unfolding_all
        exact G B b)
    (by
      with_unfolding_all
        exact G B c)
    (by
      with_unfolding_all
        exact G B d)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (towerAlpha B k r p i h)
    (towerAlpha B k₁ r₁ p₁ i₁ h₁)
    ((openBetaTower B d k₁ k a wk sk).hom)
    ((openBetaTower B c i₁ i b wi si).hom)
    ((towerSquare (modulePullback B b) (modulePullback B p₁) (modulePullback B p)
        (modulePullback B a) (moduleSquareG B a p₁ p b wp)).hom)
    ((towerSquare (modulePullback B c) (modulePullback B r₁) (modulePullback B r)
        (modulePullback B d) (moduleSquareG B d r₁ r c wr)).inv)
    (by
      with_unfolding_all
        exact alpha B k r p i h)
    (by
      with_unfolding_all
        exact alpha B k₁ r₁ p₁ i₁ h₁)
    (by
      with_unfolding_all
        exact (beta B d k₁ k a wk sk).hom)
    (by
      with_unfolding_all
        exact (beta B c i₁ i b wi si).hom)
    (by
      with_unfolding_all
        exact (squareG B a p₁ p b wp).hom)
    (by
      with_unfolding_all
        exact (squareG B d r₁ r c wr).inv)
    (by
      with_unfolding_all
        exact heq_of_eq (pastingAlpha B k r p i h))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingAlpha B k₁ r₁ p₁ i₁ h₁))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingBeta B d k₁ k a wk sk))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingBeta B c i₁ i b wi si))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingSquare B a p₁ p b wp))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingSquareInv B d r₁ r c wr))
    (by
      exact towerAlpha_baseChange B k i r p k₁ i₁ r₁ p₁ a b c d h h₁ wk wi wp wr sk si hp hr)

end DerivedTransport

end AlgebraicGeometry.ProEtale.StrictTower
