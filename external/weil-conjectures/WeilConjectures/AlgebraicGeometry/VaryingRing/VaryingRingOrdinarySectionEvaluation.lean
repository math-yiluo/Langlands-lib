/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryEvaluationComparisons
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingClopenArrowFactors
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryComparisonNormalization
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryClopenProjectorEvaluation

/-!
# Ordinary realization of the clopen section factor

Source: Zheng, Construction 4.1; Stacks Project, Tags 03DI and 09AE.
(blueprint: lem-sp-varying-ring-ordinary-section-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
attribute [local instance 2000] WeilConjectures.SemilinearSections.sequenceSmall
  StrictTower.towers_hasDerivedCategory Scheme.proEtaleRingModules_hasDerivedCategory

attribute [local irreducible] ordinaryRealization ordinaryPullComparison ordinaryOpenComparison
  modulePi StrictTower.pi moduleGComp moduleJComp StrictTower.gComp StrictTower.jComp
  StrictTower.G StrictTower.J Functor.leftAdjoint

private def openCompatible
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    {EA : A ⥤ A'} {EB : B ⥤ B'} {EC : C ⥤ C'}
    {H : A ⥤ B} {B₀ : B ⥤ C} {K : A ⥤ C}
    {j : A' ⥤ B'} {b : B' ⥤ C'} {k : A' ⥤ C'}
    (eJ : H ⋙ EB ≅ EA ⋙ j) (eB : B₀ ⋙ EC ≅ EB ⋙ b)
    (eK : K ⋙ EC ≅ EA ⋙ k) (jc : H ⋙ B₀ ≅ K) (jc' : j ⋙ b ≅ k) : Prop :=
  ∀ M, EC.map (jc.hom.app M) ≫ eK.hom.app M =
    eB.hom.app (H.obj M) ≫ b.map (eJ.hom.app M) ≫ jc'.hom.app (EA.obj M)

private def pullCompatible
    {A B D A' B' D' : Type*}
    [Category A] [Category B] [Category D] [Category A'] [Category B'] [Category D']
    {EA : A ⥤ A'} {EB : B ⥤ B'} {ED : D ⥤ D'}
    {G : B ⥤ A} {Q : D ⥤ B} {R₀ : D ⥤ A}
    {g : B' ⥤ A'} {q : D' ⥤ B'} {r : D' ⥤ A'}
    (eG : G ⋙ EA ≅ EB ⋙ g) (eQ : Q ⋙ EB ≅ ED ⋙ q)
    (eR : R₀ ⋙ EA ≅ ED ⋙ r) (gc : R₀ ≅ Q ⋙ G) (gc' : r ≅ q ⋙ g) : Prop :=
  ∀ N, EA.map (gc.hom.app N) ≫ eG.hom.app (Q.obj N) ≫
    g.map (eQ.hom.app N) = eR.hom.app N ≫ gc'.hom.app (ED.obj N)

private theorem section_comparison
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {EA : A ⥤ A'} {EB : B ⥤ B'} {EC : C ⥤ C'} {ED : D ⥤ D'}
    {G : B ⥤ A} {H : A ⥤ B} {B₀ : B ⥤ C} {Q : D ⥤ B}
    {K : A ⥤ C} {R₀ : D ⥤ A}
    {g : B' ⥤ A'} {j : A' ⥤ B'} {b : B' ⥤ C'} {q : D' ⥤ B'}
    {k : A' ⥤ C'} {r : D' ⥤ A'}
    (eG : G ⋙ EA ≅ EB ⋙ g) (eJ : H ⋙ EB ≅ EA ⋙ j)
    (eB : B₀ ⋙ EC ≅ EB ⋙ b) (eQ : Q ⋙ EB ≅ ED ⋙ q)
    (eK : K ⋙ EC ≅ EA ⋙ k) (eR : R₀ ⋙ EA ≅ ED ⋙ r)
    (jc : H ⋙ B₀ ≅ K) (jc' : j ⋙ b ≅ k)
    (gc : R₀ ≅ Q ⋙ G) (gc' : r ≅ q ⋙ g)
    (π₀ : 𝟭 B ⟶ G ⋙ H) (π₁ : 𝟭 B' ⟶ g ⋙ j)
    (hj : openCompatible
      (EA := EA) (EB := EB) (EC := EC) (H := H) (B₀ := B₀) (K := K)
      (j := j) (b := b) (k := k) eJ eB eK jc jc')
    (hg : pullCompatible
      (EA := EA) (EB := EB) (ED := ED) (G := G) (Q := Q) (R₀ := R₀)
      (g := g) (q := q) (r := r) eG eQ eR gc gc')
    (hp : ∀ M, EB.map (π₀.app M) ≫ eJ.hom.app (G.obj M) ≫
      j.map (eG.hom.app M) = π₁.app (EB.obj M)) :
    OrdinarySquareComparison eR eB eK eQ
      (Functor.whiskerRight (Functor.whiskerLeft Q π₀) B₀ ≫
        Functor.whiskerRight (Functor.associator Q G H).inv B₀ ≫
        (Functor.associator (Q ⋙ G) H B₀).hom ≫
        Functor.whiskerLeft (Q ⋙ G) jc.hom ≫ Functor.whiskerRight gc.inv K)
      (Functor.whiskerRight (Functor.whiskerLeft q π₁) b ≫
        Functor.whiskerRight (Functor.associator q g j).inv b ≫
        (Functor.associator (q ⋙ g) j b).hom ≫
        Functor.whiskerLeft (q ⋙ g) jc'.hom ≫ Functor.whiskerRight gc'.inv k) := by
  constructor
  intro N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp]
  dsimp only [Functor.comp_obj]
  erw [B₀.map_id, Category.id_comp, b.map_id, Category.id_comp]
  have hgi : EA.map (gc.inv.app N) ≫ eR.hom.app N =
      eG.hom.app (Q.obj N) ≫ g.map (eQ.hom.app N) ≫ gc'.inv.app (ED.obj N) := by
    apply (Iso.inv_comp_eq (EA.mapIso (gc.app N))).2
    change eR.hom.app N = EA.map (gc.hom.app N) ≫ eG.hom.app (Q.obj N) ≫
      g.map (eQ.hom.app N) ≫ gc'.inv.app (ED.obj N)
    rw [reassoc_of% (hg N)]
    simp only [Iso.hom_inv_id_app, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (eK.hom.naturality (gc.inv.app N))]
  rw [reassoc_of% (hj (G.obj (Q.obj N)))]
  rw [← Functor.map_comp, hgi]
  simp only [Functor.map_comp]
  rw [← reassoc_of% (jc'.hom.naturality (eG.hom.app (Q.obj N)))]
  rw [← reassoc_of% (jc'.hom.naturality (g.map (eQ.hom.app N)))]
  rw [reassoc_of% (eB.hom.naturality (π₀.app (Q.obj N)))]
  have hpm := congrArg b.map (hp (Q.obj N))
  simp only [Functor.map_comp] at hpm
  rw [reassoc_of% hpm]
  have hpn := congrArg b.map (π₁.naturality (eQ.hom.app N))
  dsimp only [Functor.id_map, Functor.comp_map] at hpn
  simp only [Functor.map_comp] at hpn
  rw [← reassoc_of% hpn]

private theorem comparison_comp
    {C D : Type*} [Category C] [Category D] (E : C ⥤ D)
    {X Y Z : C} {X' Y' Z' : D} (u : X ⟶ Y) (v : Y ⟶ Z)
    (u' : X' ⟶ Y') (v' : Y' ⟶ Z')
    (eX : E.obj X ⟶ X') (eY : E.obj Y ⟶ Y') (eZ : E.obj Z ⟶ Z')
    (hu : E.map u ≫ eY = eX ≫ u') (hv : E.map v ≫ eZ = eY ≫ v') :
    E.map (u ≫ v) ≫ eZ = eX ≫ u' ≫ v' := by
  rw [E.map_comp, Category.assoc, hv, ← Category.assoc, hu, Category.assoc]

private theorem comparison_inv
    {C D : Type*} [Category C] [Category D] (E : C ⥤ D)
    {X Y : C} {X' Y' : D} (u : X ≅ Y) (u' : X' ≅ Y')
    (eX : E.obj X ⟶ X') (eY : E.obj Y ⟶ Y')
    (hu : E.map u.hom ≫ eY = eX ≫ u'.hom) :
    E.map u.inv ≫ eX = eY ≫ u'.inv := by
  apply (Iso.inv_comp_eq (E.mapIso u)).2
  change eX = E.map u.hom ≫ eY ≫ u'.inv
  rw [← Category.assoc, hu, Category.assoc, u'.hom_inv_id, Category.comp_id]

private structure ComparisonCell
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    (E : A ⥤ A') (F : B ⥤ B') where
  source : A ⥤ B
  target : A' ⥤ B'
  comparison : source ⋙ F ≅ E ⋙ target

private def cellCompatible
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {E : A ⥤ A'} {F : B ⥤ B'} (D D' : ComparisonCell E F)
    (p : D.source = D'.source) (p' : D.target = D'.target) (M : A) : Prop :=
  F.map ((eqToIso p).hom.app M) ≫ D'.comparison.hom.app M =
    D.comparison.hom.app M ≫ (eqToIso p').hom.app (E.obj M)

private theorem cell_congr
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {E : A ⥤ A'} {F : B ⥤ B'} (D D' : ComparisonCell E F) (h : D = D')
    (p : D.source = D'.source) (p' : D.target = D'.target) (M : A) :
    cellCompatible D D' p p' M := by
  unfold cellCompatible
  subst D'
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  dsimp only [Functor.comp_obj]
  simp only [F.map_id, Category.id_comp, Category.comp_id]

private def ordinaryOpenCell (n : ℕ) (jIso : OrdinaryOpenComparison R φ n)
    {U X : Scheme.{u}}
    (a : {f : U ⟶ X // IsOpenImmersion f}) :
    ComparisonCell (ordinaryRealization R φ n U) (ordinaryRealization R φ n X) where
  source := @extension R φ U X a.val a.property
  target := @StrictTower.J (R n) _ U X a.val a.property
  comparison := @jIso U X a.val a.property

private theorem openComparison_congr (n : ℕ) (jIso : OrdinaryOpenComparison R φ n)
    {U X : Scheme.{u}}
    {f g : U ⟶ X} [hf : IsOpenImmersion f] [hg : IsOpenImmersion g] (h : f = g)
    (M : Modules R φ U) :
    cellCompatible
      (ordinaryOpenCell R φ n jIso (U := U) (X := X) ⟨f, hf⟩)
      (ordinaryOpenCell R φ n jIso (U := U) (X := X) ⟨g, hg⟩)
      (moduleJ_congr R φ h) (StrictTower.J_congr (R n) h) M :=
  cell_congr (E := ordinaryRealization R φ n U) (F := ordinaryRealization R φ n X)
    (ordinaryOpenCell R φ n jIso (U := U) (X := X) ⟨f, hf⟩)
    (ordinaryOpenCell R φ n jIso (U := U) (X := X) ⟨g, hg⟩)
    (congrArg (ordinaryOpenCell R φ n jIso (U := U) (X := X)) (Subtype.ext h :
      (⟨f, hf⟩ : {f : U ⟶ X // IsOpenImmersion f}) = ⟨g, hg⟩))
    (moduleJ_congr R φ h) (StrictTower.J_congr (R n) h) M

private def ordinaryPullCell (n : ℕ) (gIso : OrdinaryPullComparison R φ n)
    {U X : Scheme.{u}} (f : U ⟶ X) :
    ComparisonCell (ordinaryRealization R φ n X) (ordinaryRealization R φ n U) where
  source := pull R φ f
  target := StrictTower.G (R n) f
  comparison := gIso U X f

private theorem pullComparison_congr (n : ℕ) (gIso : OrdinaryPullComparison R φ n)
    {U X : Scheme.{u}}
    {f g : U ⟶ X} (h : f = g) (M : Modules R φ X) :
    cellCompatible
      (ordinaryPullCell R φ n gIso (U := U) (X := X) f)
      (ordinaryPullCell R φ n gIso (U := U) (X := X) g)
      (congrArg (pull R φ) h) (congrArg (StrictTower.G (R n)) h) M :=
  cell_congr (E := ordinaryRealization R φ n X) (F := ordinaryRealization R φ n U)
    (ordinaryPullCell R φ n gIso (U := U) (X := X) f)
    (ordinaryPullCell R φ n gIso (U := U) (X := X) g)
    (congrArg (ordinaryPullCell R φ n gIso (U := U) (X := X)) h)
    (congrArg (pull R φ) h) (congrArg (StrictTower.G (R n)) h) M

private theorem open_data_comp
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    {EA : A ⥤ A'} {EB : B ⥤ B'} {EC : C ⥤ C'}
    {H : A ⥤ B} {B₀ : B ⥤ C} {j : A' ⥤ B'} {b : B' ⥤ C'}
    (eJ : H ⋙ EB ≅ EA ⋙ j) (eB : B₀ ⋙ EC ≅ EB ⋙ b)
    (D D' : ComparisonCell EA EC) (jc : H ⋙ B₀ ≅ D.source)
    (jc' : j ⋙ b ≅ D.target) (p : D.source = D'.source) (p' : D.target = D'.target)
    (hn : openCompatible
      (EA := EA) (EB := EB) (EC := EC) (H := H) (B₀ := B₀) (K := D.source)
      (j := j) (b := b) (k := D.target) eJ eB D.comparison jc jc')
    (hd : ∀ M, cellCompatible D D' p p' M) :
    openCompatible
      (EA := EA) (EB := EB) (EC := EC) (H := H) (B₀ := B₀) (K := D'.source)
      (j := j) (b := b) (k := D'.target) eJ eB D'.comparison
      (jc ≪≫ eqToIso p) (jc' ≪≫ eqToIso p') := by
  intro M
  simpa only [Iso.trans_hom, NatTrans.comp_app, Category.assoc] using
    comparison_comp EC (jc.hom.app M) ((eqToIso p).hom.app M)
      (jc'.hom.app (EA.obj M)) ((eqToIso p').hom.app (EA.obj M))
      (eB.hom.app (H.obj M) ≫ b.map (eJ.hom.app M))
      (D.comparison.hom.app M) (D'.comparison.hom.app M)
      (by simpa only [Category.assoc] using hn M) (hd M)

private theorem pull_data_comp
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    {EA : A ⥤ A'} {EB : B ⥤ B'} {EC : C ⥤ C'}
    {G : B ⥤ A} {Q : C ⥤ B} {g : B' ⥤ A'} {q : C' ⥤ B'}
    (eG : G ⋙ EA ≅ EB ⋙ g) (eQ : Q ⋙ EB ≅ EC ⋙ q)
    (D D' : ComparisonCell EC EA) (gc : D.source ≅ Q ⋙ G)
    (gc' : D.target ≅ q ⋙ g) (p : D.source = D'.source) (p' : D.target = D'.target)
    (hn : pullCompatible
      (EA := EA) (EB := EB) (ED := EC) (G := G) (Q := Q) (R₀ := D.source)
      (g := g) (q := q) (r := D.target) eG eQ D.comparison gc gc')
    (hd : ∀ M, cellCompatible D D' p p' M) :
    pullCompatible
      (EA := EA) (EB := EB) (ED := EC) (G := G) (Q := Q) (R₀ := D'.source)
      (g := g) (q := q) (r := D'.target) eG eQ D'.comparison
      ((eqToIso p).symm ≪≫ gc)
      ((eqToIso p').symm ≪≫ gc') := by
  intro M
  have hi := comparison_inv EA ((eqToIso p).app M) ((eqToIso p').app (EC.obj M))
    (D.comparison.hom.app M) (D'.comparison.hom.app M) (hd M)
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] using
    comparison_comp EA ((eqToIso p).inv.app M) (gc.hom.app M)
      ((eqToIso p').inv.app (EC.obj M)) (gc'.hom.app (EC.obj M))
      (D'.comparison.hom.app M) (D.comparison.hom.app M)
      (eG.hom.app (Q.obj M) ≫ g.map (eQ.hom.app M)) hi (hn M)

private theorem open_comp_compatible (n : ℕ) (jIso : OrdinaryOpenComparison R φ n)
    (hn : OrdinaryOpenComposition R φ n jIso) {V P W : Scheme.{u}}
    (s : V ⟶ P) (b : P ⟶ W) (k : V ⟶ W)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion k] (hk : s ≫ b = k) :
    openCompatible
      (EA := ordinaryRealization R φ n V) (EB := ordinaryRealization R φ n P)
      (EC := ordinaryRealization R φ n W)
      (H := extension R φ s) (B₀ := extension R φ b) (K := extension R φ k)
      (j := StrictTower.J (R n) s) (b := StrictTower.J (R n) b)
      (k := StrictTower.J (R n) k) (jIso V P s)
      (jIso P W b) (jIso V W k)
      (moduleJComp R φ s b ≪≫ moduleJCongr R φ hk)
      (StrictTower.jComp (R n) s b ≪≫ StrictTower.jCongr (R n) hk) :=
  open_data_comp
    (EA := ordinaryRealization R φ n V) (EB := ordinaryRealization R φ n P)
    (EC := ordinaryRealization R φ n W)
    (H := extension R φ s) (B₀ := extension R φ b)
    (j := StrictTower.J (R n) s) (b := StrictTower.J (R n) b)
    (jIso V P s)
    (jIso P W b)
    (ordinaryOpenCell R φ n jIso (U := V) (X := W) ⟨s ≫ b, inferInstance⟩)
    (ordinaryOpenCell R φ n jIso (U := V) (X := W) ⟨k, inferInstance⟩)
    (moduleJComp R φ s b) (StrictTower.jComp (R n) s b)
    (moduleJ_congr R φ hk) (StrictTower.J_congr (R n) hk)
    (hn s b) (openComparison_congr R φ n jIso hk)

private theorem pull_comp_compatible (n : ℕ) (gIso : OrdinaryPullComparison R φ n)
    (hn : OrdinaryPullComposition R φ n gIso) {V P S : Scheme.{u}}
    (s : V ⟶ P) (q : P ⟶ S) (r : V ⟶ S) (hr : s ≫ q = r) :
    pullCompatible
      (EA := ordinaryRealization R φ n V) (EB := ordinaryRealization R φ n P)
      (ED := ordinaryRealization R φ n S)
      (G := pull R φ s) (Q := pull R φ q) (R₀ := pull R φ r)
      (g := StrictTower.G (R n) s) (q := StrictTower.G (R n) q)
      (r := StrictTower.G (R n) r) (gIso V P s)
      (gIso P S q) (gIso V S r)
      ((eqToIso (congrArg (pull R φ) hr)).symm ≪≫ moduleGComp R φ s q)
      ((eqToIso (congrArg (StrictTower.G (R n)) hr)).symm ≪≫
        StrictTower.gComp (R n) s q) :=
  pull_data_comp
    (EA := ordinaryRealization R φ n V) (EB := ordinaryRealization R φ n P)
    (EC := ordinaryRealization R φ n S)
    (G := pull R φ s) (Q := pull R φ q)
    (g := StrictTower.G (R n) s) (q := StrictTower.G (R n) q)
    (gIso V P s)
    (gIso P S q)
    (ordinaryPullCell R φ n gIso (U := V) (X := S) (s ≫ q))
    (ordinaryPullCell R φ n gIso (U := V) (X := S) r)
    (moduleGComp R φ s q) (StrictTower.gComp (R n) s q)
    (congrArg (pull R φ) hr) (congrArg (StrictTower.G (R n)) hr)
    (hn s q) (pullComparison_congr R φ n gIso hr)

/-- Realization preserves the section factor, after the cartesian comparison.
Source: Stacks 0F7B, open-immersion case; Zheng, Construction 4.1
(blueprint: lem-sp-varying-ring-ordinary-section-evaluation).
Proof: put q = pullback.snd p i, b = pullback.fst p i and
s = squareLift k r p i h. The map s is clopen. The intrinsic projector restricts
to the open-adjunction unit, by the triangle identity for the adjoint triple.
Unit preservation and naturality identify the two projectors after restriction;
the restriction/direct-image adjunction detects their equality because the
clopen extension-to-direct-image comparison is invertible. Apply b_! to that
equation. The open compositor normalization identifies b_! s_! with k_!, and the
pullback compositor normalization identifies s^* q^* with r^*. Naturality moves
the comparisons through the compositors. Equality elimination handles bs=k and
qs=r, giving the displayed equation. The cartesian beta factor is absent from
this calculation. -/
theorem ordinarySectionEvaluation (n : ℕ) {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    OrdinarySquareComparison
      (EA := ordinaryRealization R φ n V) (EB := ordinaryRealization R φ n W)
      (EC := ordinaryRealization R φ n S)
      (ED := ordinaryRealization R φ n (pullback p i))
      (R₀ := pull R φ r) (P₀ := extension R φ (pullback.fst p i))
      (K := extension R φ k) (I := pull R φ (pullback.snd p i))
      (r := StrictTower.G (R n) r) (p := StrictTower.J (R n) (pullback.fst p i))
      (k := StrictTower.J (R n) k) (i := StrictTower.G (R n) (pullback.snd p i))
      (ordinaryPullComparison R φ n V S r)
      (ordinaryOpenComparison R φ n (pullback p i) W (pullback.fst p i))
      (ordinaryOpenComparison R φ n V W k)
      (ordinaryPullComparison R φ n (pullback p i) S (pullback.snd p i))
      (moduleSectionArrow R φ k r p i h) (strictSectionArrow (R n) k r p i h) := by
  let s := StrictTower.squareLift k r p i h
  let b := pullback.fst p i
  let q := pullback.snd p i
  have hs : IsOpenImmersion s := StrictTower.squareLift_open k r p i h
  have hc : IsClosedImmersion s := StrictTower.squareLift_closed k r p i h
  have hk : s ≫ b = k := pullback.lift_fst k r h
  have hr : s ≫ q = r := pullback.lift_snd k r h
  let jc := moduleJComp R φ s b ≪≫ moduleJCongr R φ hk
  let jc' := StrictTower.jComp (R n) s b ≪≫ StrictTower.jCongr (R n) hk
  let d := eqToIso (congrArg (pull R φ) hr)
  let d' := eqToIso (congrArg (StrictTower.G (R n)) hr)
  let gc := d.symm ≪≫ moduleGComp R φ s q
  let gc' := d'.symm ≪≫ StrictTower.gComp (R n) s q
  exact (section_comparison
    (EA := ordinaryRealization R φ n V) (EB := ordinaryRealization R φ n (pullback p i))
    (EC := ordinaryRealization R φ n W) (ED := ordinaryRealization R φ n S)
    (G := pull R φ s) (H := extension R φ s) (B₀ := extension R φ b)
    (Q := pull R φ q) (K := extension R φ k) (R₀ := pull R φ r)
    (g := StrictTower.G (R n) s) (j := StrictTower.J (R n) s)
    (b := StrictTower.J (R n) b) (q := StrictTower.G (R n) q)
    (k := StrictTower.J (R n) k) (r := StrictTower.G (R n) r)
    (ordinaryPullComparison R φ n V _ s) (ordinaryOpenComparison R φ n V _ s)
    (ordinaryOpenComparison R φ n _ W b) (ordinaryPullComparison R φ n _ S q)
    (ordinaryOpenComparison R φ n V W k) (ordinaryPullComparison R φ n V S r)
    jc jc' gc gc' (modulePi R φ s) (StrictTower.pi (R n) s)
    (open_comp_compatible R φ n (ordinaryOpenComparison R φ n)
      (ordinaryComparisonNormalization R φ n).2 s b k hk)
    (pull_comp_compatible R φ n (ordinaryPullComparison R φ n)
      (ordinaryComparisonNormalization R φ n).1 s q r hr)
    (ordinaryClopenProjectorEvaluation R φ n s))

end AlgebraicGeometry.ProEtale.VaryingRing
