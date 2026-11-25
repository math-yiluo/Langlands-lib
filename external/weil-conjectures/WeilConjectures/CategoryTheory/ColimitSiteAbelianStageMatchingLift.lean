/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ColimitSiteAbelianStageImage
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
import WeilConjectures.CategoryTheory.ColimitSiteAbelianCoverSectionLift
import WeilConjectures.CategoryTheory.ColimitSiteAbelianFiniteFamilyStabilization

/-! # Matching lifts of generated abelian sections

Source: Stacks Project, Sites, Tag 0A35; Modules on Sites, Tag 03CO.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

private theorem finite_cover_of_mem
    {C : Type u} [SmallCategory C] (Q : Precoverage C)
    [Q.HasIsos] [Q.IsStableUnderFiniteComposition]
    [Q.IsStableUnderFiniteBaseChange] [Q.HasPullbacks]
    (hfinite : ∀ (X : C) (R : Presieve X), R ∈ Q X → Finite R.uncurry)
    {X : C} (S : Sieve X) (hS : S ∈ Q.toGrothendieck X) :
    ∃ R : Presieve X, R ∈ Q X ∧ R ≤ S.arrows := by
  classical
  have hp {X : C} (R : Presieve X) :
      Presieve.ofArrows (fun a : R.uncurry ↦ a.val.1) (fun a ↦ a.val.2) = R := by
    apply le_antisymm
    · rintro Z f ⟨a⟩
      exact a.property
    · intro Z f hf
      exact Presieve.ofArrows.mk (⟨⟨Z, f⟩, hf⟩ : R.uncurry)
  induction hS with
  | of X R hR => exact ⟨R, hR, Sieve.le_generate R⟩
  | top X =>
    exact ⟨Presieve.singleton (𝟙 X), Precoverage.mem_coverings_of_isIso _, by simp⟩
  | pullback X S hS Y f ih =>
    obtain ⟨R, hR, hle⟩ := ih
    have :=  hfinite X R hR
    have :=  Q.hasPullbacks_of_mem f hR
    let A (a : R.uncurry) := a.val.1
    let g (a : R.uncurry) : A a ⟶ X := a.val.2
    have (a : R.uncurry) : HasPullback (g a) f := R.hasPullback f a.property
    have hcov : Presieve.ofArrows (fun a ↦ pullback (g a) f)
        (fun a ↦ pullback.snd (g a) f) ∈ Q Y := by
      apply Precoverage.IsStableUnderFiniteBaseChange.mem_coverings_of_isPullback
        g (by simpa only [A, g, hp] using hR) f
        (fun a ↦ pullback.snd (g a) f) (fun a ↦ pullback.fst (g a) f)
      intro a
      exact (IsPullback.of_hasPullback _ _).flip
    refine ⟨_, hcov, ?_⟩
    rintro Z k ⟨a⟩
    change S (pullback.snd (g a) f ≫ f)
    rw [← pullback.condition]
    exact S.downward_closed (hle _ _ a.property) _
  | transitive X S T hS hT ihS ihT =>
    obtain ⟨R, hR, hle⟩ := ihS
    have :=  hfinite X R hR
    have hi (a : R.uncurry) :
        ∃ U : Presieve a.val.1, U ∈ Q a.val.1 ∧ U ≤ (T.pullback a.val.2).arrows :=
      ihT (hle _ _ a.property)
    choose U hU hleU using hi
    have (a : R.uncurry) := hfinite a.val.1 (U a) (hU a)
    have hcov : Presieve.ofArrows
        (fun p : Σ a : R.uncurry, (U a).uncurry ↦ p.2.val.1)
        (fun p ↦ p.2.val.2 ≫ p.1.val.2) ∈ Q X := by
      apply Precoverage.IsStableUnderFiniteComposition.comp_mem_coverings
        (fun a : R.uncurry ↦ a.val.2) (by simpa only [hp] using hR)
        (fun a (b : (U a).uncurry) ↦ b.val.2)
      intro a
      simpa only [hp] using hU a
    refine ⟨_, hcov, ?_⟩
    rintro Z f ⟨⟨a, b⟩⟩
    exact hleU a _ _ b.property

private theorem finite_map
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (H : C ⥤ D) {X : C} (R : Presieve X) [Finite R.uncurry] :
    Finite (R.map H).uncurry := by
  apply Finite.of_surjective
    (fun a : R.uncurry ↦
      (⟨⟨H.obj a.val.1, H.map a.val.2⟩, Presieve.map_map a.property⟩ : (R.map H).uncurry))
  rintro ⟨⟨Y, f⟩, hf⟩
  obtain ⟨hf⟩ := hf
  exact ⟨⟨⟨_, _⟩, hf⟩, rfl⟩

/-- A matching family of generated sections admits a matching lift on a stage cover.
Source: Stacks Project, Sites, Tag 0A35, the general-object presentation and finite-cover
paragraphs; Modules on Sites, Tag 03CO, for abelian coefficients.
(blueprint: lem-weil-pbc-colimit-site-abelian-stage-matching-lift).

Proof: Finite base change and composition, together with the finiteness of stage covers,
show that a covering sieve contains the image of a finite stage cover: sieves containing
such a cover form a topology, since base change preserves covers and transitivity
requires only finitely many further finite covers. Present its target
at a stage above i using the object colimit. Each of the finitely many local sections is
a finite additive expression in stage images and restrictions. Lift the objects and
restriction arrows to a common stage using the object and arrow colimits; eventual
object equality aligns their endpoints. Transpose the adjunction units to obtain the
transition maps. Uniqueness of adjuncts gives their composition laws and identifies
their composites with alpha by h-alpha. Thus the finitely many local expressions have
stage section representatives on a common transported cover.

To lift compatibility, compare the restrictions of these representatives to each
pairwise covering pullback. Their alpha images agree by compatibility of x and
naturality. Uniqueness of left adjoints identifies alpha with the cocone inverse-image
unit followed by the canonical composition isomorphism; hence their difference is
killed by that unit. Apply the existing finite source-unit zero-detection theorem to
the stage inverse image as a source sheaf and to each such difference. It gives a
transition whose unit kills the difference. The same composition isomorphism for
transition inverse images identifies this with equality after the canonical stage
transition. There are finitely many pairs of covering arrows; a common refinement
in the filtered under category makes all these equalities hold at once. Transition
functors preserve the covering pullbacks, so the transported family is pullback
compatible, hence compatible. Naturality and the unit equations preserve its alpha
images. An empty cover has no sections or compatibility equations to lift, and its
empty matching family is compatible. This asserts only a matching lift: amalgamation
and uniqueness are not part of the conclusion. No arbitrary witness defines an object.
-/
theorem colimit_site_abelian_stage_matching_lift
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderFiniteComposition]
    [∀ j, (P j).IsStableUnderFiniteBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderFiniteComposition]
    [Q.IsStableUnderFiniteBaseChange] [Q.HasPullbacks]
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R))
    (hVpullback : (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor))
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck AddCommGrpCat.{u})
    (α : ∀ t : Under i,
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶
      ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck Q.toGrothendieck).obj
        ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck
          Q.toGrothendieck).obj G))
    (hα : ∀ (t : Under i) (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫ (α t).hom.app
        (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X)))
    (Y : V.pt) (S : Sieve Y) (hS : S ∈ Q.toGrothendieck Y)
    (x : S.arrows.FamilyOfElements
      (ColimitSiteStageImage.presheaf F P V Q i G α ⋙ forget AddCommGrpCat.{u}))
    (hx : x.Compatible) :
    ∃ (t : Under i) (W : F.obj t.right) (T : Presieve W), T ∈ P t.right W ∧
      ∃ (hY : (V.ι.app t.right).toFunctor.obj W = Y)
        (hTS : ∀ {Z : F.obj t.right} (g : Z ⟶ W), T g →
          S ((V.ι.app t.right).toFunctor.map g ≫ eqToHom hY))
        (y : T.FamilyOfElements
          (((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
            (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⋙
              forget AddCommGrpCat.{u})),
        y.Compatible ∧ ∀ {Z : F.obj t.right} (g : Z ⟶ W) (hg : T g),
          (α t).hom.app (op Z) (y g hg) =
            (x ((V.ι.app t.right).toFunctor.map g ≫ eqToHom hY) (hTS g hg)).val := by
  classical
  have hQfinite (Z : V.pt) (R : Presieve Z) (hR : R ∈ Q Z) : Finite R.uncurry := by
    obtain ⟨j, W, T, h, hT, hR⟩ := (hQ Z R).mp hR
    subst Z
    subst R
    have := hfinite j W T hT
    exact finite_map (V.ι.app j).toFunctor T
  obtain ⟨R, hR, hRS⟩ := finite_cover_of_mem Q hQfinite S hS
  let xR : R.FamilyOfElements
      (ColimitSiteStageImage.presheaf F P V Q i G α ⋙ forget AddCommGrpCat.{u}) :=
    fun {Z} f hf ↦ x f (hRS _ _ hf)
  obtain ⟨t, W, T, hT, hY, hTR, y, hrep⟩ :=
    colimit_site_abelian_cover_section_lift
      J F P hfinite hcover V hobjects harrows Q hQ i G α hα Y R hR xR
  have hTS {Z : F.obj t.right} (g : Z ⟶ W) (hg : T g) :
      S ((V.ι.app t.right).toFunctor.map g ≫ eqToHom hY) := hRS _ _ (hTR g hg)
  let H := ColimitSiteStageImage.target F P V Q i G
  let xH : S.arrows.FamilyOfElements (H.obj ⋙ forget AddCommGrpCat.{u}) :=
    fun {Z} f hf ↦ (x f hf).val
  have xH_congr {Z : V.pt} (a b : Z ⟶ Y) (ha : S a) (hb : S b) (hab : a = b) :
      xH a ha = xH b hb := by
    subst b
    rfl
  have hxH : xH.Compatible := by
    intro Z₁ Z₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ heq
    exact congrArg Subtype.val (hx g₁ g₂ hf₁ hf₂ heq)
  have hrep' {Z : F.obj t.right} (g : Z ⟶ W) (hg : T g) :
      (α t).hom.app (op Z) (y g hg) =
        xH ((V.ι.app t.right).toFunctor.map g ≫ eqToHom hY) (hTS g hg) :=
    hrep g hg
  have hy : (show T.FamilyOfElements
        ((V.ι.app t.right).toFunctor.op ⋙ H.obj ⋙ forget AddCommGrpCat.{u}) from
        fun {Z} g hg ↦ (α t).hom.app (op Z) (y g hg)).Compatible := by
    intro Z₁ Z₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ heq
    change H.obj.map ((V.ι.app t.right).toFunctor.map g₁).op
        ((α t).hom.app (op Z₁) (y f₁ hf₁)) =
      H.obj.map ((V.ι.app t.right).toFunctor.map g₂).op
        ((α t).hom.app (op Z₂) (y f₂ hf₂))
    rw [hrep', hrep']
    exact hxH _ _ (hTS f₁ hf₁) (hTS f₂ hf₂) (by
      simp only [← Category.assoc, ← Functor.map_comp, heq])
  obtain ⟨t', W', T', hT', hW, y', hy', href⟩ :=
    colimit_site_abelian_finite_family_stabilization J F P hfinite hcover hpullback
      V hobjects harrows Q hQ hVpullback i G α hα t W T hT y hy
  let hY' := hW.trans hY
  have hfac {Z' : F.obj t'.right} (g' : Z' ⟶ W')
      {Z : F.obj t.right} (g : Z ⟶ W)
      (r : (V.ι.app t'.right).toFunctor.obj Z' ⟶ (V.ι.app t.right).toFunctor.obj Z)
      (hr : (V.ι.app t'.right).toFunctor.map g' ≫ eqToHom hW =
        r ≫ (V.ι.app t.right).toFunctor.map g) :
      (V.ι.app t'.right).toFunctor.map g' ≫ eqToHom hY' =
        r ≫ ((V.ι.app t.right).toFunctor.map g ≫ eqToHom hY) := by
    rw [← eqToHom_trans hW hY, ← Category.assoc, hr, Category.assoc]
  have hTS' {Z' : F.obj t'.right} (g' : Z' ⟶ W') (hg' : T' g') :
      S ((V.ι.app t'.right).toFunctor.map g' ≫ eqToHom hY') := by
    obtain ⟨Z, g, hg, r, hr, _⟩ := href g' hg'
    rw [hfac g' g r hr]
    exact S.downward_closed (hTS g hg) r
  refine ⟨t', W', T', hT', hY', hTS', y', hy', ?_⟩
  intro Z' g' hg'
  obtain ⟨Z, g, hg, r, hr, hz⟩ := href g' hg'
  rw [hz, hrep']
  have he := ((Presieve.compatible_iff_sieveCompatible xH).mp hxH
    ((V.ι.app t.right).toFunctor.map g ≫ eqToHom hY) r (hTS g hg)).symm
  change H.obj.map r.op (xH _ _) = xH _ _ at he
  change H.obj.map r.op (xH _ _) = xH _ _
  exact he.trans (xH_congr _ _ _ _ (hfac g' g r hr).symm)

end CategoryTheory
