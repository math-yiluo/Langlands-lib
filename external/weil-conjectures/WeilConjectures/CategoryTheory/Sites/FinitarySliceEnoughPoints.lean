/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.AlgebraicGeometry.FinitarySiteEnoughPoints
import all WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Enough points from a cover by finitary slices

Source: Stacks Project, Sites, Lemma 0DW0, `lemma-criterion-points`, in Section 00YN
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem asSmall_map_iff
    {C : Type u} [Category.{v} C] {X : AsSmall.{0} C} (R : Presieve X)
    {Y : C} (f : Y ⟶ (ULift.down X)) :
    R.map AsSmall.down f ↔ R (show AsSmall.up.obj Y ⟶ X from ⟨f⟩) := by
  constructor
  · rintro ⟨h⟩
    exact h
  · intro h
    exact ⟨h⟩

private theorem asSmall_generate_pullback
    {C : Type u} [Category.{v} C] {X : C} (R : Presieve X) :
    (Sieve.generate R).functorPullback AsSmall.down =
      Sieve.generate (R.functorPullback (AsSmall.down : AsSmall.{0} C ⥤ C)) := by
  apply le_antisymm _ (Sieve.generate_functorPullback_le _ _)
  rintro Y f ⟨Z, a, b, hb, hab⟩
  exact ⟨AsSmall.up.obj Z, ⟨a⟩, ⟨b⟩, hb, ULift.ext hab⟩

private theorem asSmall_lift_cover
    {C : Type u} [Category.{v} C] (J : Precoverage C) {X : C} {S : Sieve X}
    (hS : S ∈ J.toGrothendieck X) :
    S.functorPullback AsSmall.down ∈
      (J.comap (AsSmall.down : AsSmall.{0} C ⥤ C)).toGrothendieck
        (AsSmall.up.obj X) := by
  induction hS with
  | of X R hR =>
    rw [asSmall_generate_pullback]
    apply Precoverage.generate_mem_toGrothendieck
    change (R.functorPullback AsSmall.down).map AsSmall.down ∈ J X
    have heq : (R.functorPullback AsSmall.down).map AsSmall.down = R := by
      funext Y f
      exact propext (asSmall_map_iff _ f)
    rwa [heq]
  | top X => exact GrothendieckTopology.top_mem _ _
  | pullback X S hS Y f ih =>
    exact GrothendieckTopology.pullback_stable _ (show AsSmall.up.obj Y ⟶
      AsSmall.up.obj X from ⟨f⟩) ih
  | transitive X S R hS hR ihS ihR =>
    apply GrothendieckTopology.transitive _ ihS
    intro Y f hf
    exact ihR hf

private theorem asSmall_lower_cover
    {C : Type u} [Category.{v} C] (J : Precoverage C)
    {X : AsSmall.{0} C} {S : Sieve X}
    (hS : S ∈ (J.comap (AsSmall.down : AsSmall.{0} C ⥤ C)).toGrothendieck X) :
    S.functorPullback AsSmall.up ∈ J.toGrothendieck (ULift.down X) := by
  induction hS with
  | of X R hR =>
    have heq : (Sieve.generate R).functorPullback AsSmall.up =
        Sieve.generate (R.map AsSmall.down) := by
      ext Y a
      constructor
      · rintro ⟨Z, b, c, hc, hbc⟩
        exact ⟨ULift.down Z, b.down, c.down, ⟨hc⟩, congrArg ULift.down hbc⟩
      · rintro ⟨Z, b, c, hc, hbc⟩
        refine ⟨AsSmall.up.obj Z, ⟨b⟩, ⟨c⟩, (asSmall_map_iff R c).mp hc, ?_⟩
        exact ULift.ext hbc
    rw [heq]
    exact J.generate_mem_toGrothendieck hR
  | top X => exact J.toGrothendieck.top_mem _
  | pullback X S hS Y f ih =>
    exact J.toGrothendieck.pullback_stable f.down ih
  | transitive X S R hS hR ihS ihR =>
    apply J.toGrothendieck.transitive ihS
    intro Y f hf
    exact ihR hf

private theorem asSmall_dense
    {C : Type u} [Category.{v} C] (J : Precoverage C) :
    (AsSmall.down : AsSmall.{0} C ⥤ C).IsDenseSubsite
      (J.comap AsSmall.down).toGrothendieck J.toGrothendieck := by
  have : (AsSmall.down : AsSmall.{0} C ⥤ C).IsEquivalence :=
    (AsSmall.equiv : C ≌ AsSmall.{0} C).isEquivalence_inverse
  refine { functorPushforward_mem_iff := ?_ }
  intro X S
  have heq : S.functorPushforward AsSmall.down = S.functorPullback AsSmall.up := by
    ext Y f
    constructor
    · rintro ⟨Z, a, b, ha, hab⟩
      have hh := S.downward_closed ha (show AsSmall.up.obj Y ⟶ Z from ⟨b⟩)
      change S (show AsSmall.up.obj Y ⟶ X from ⟨f⟩)
      have he : (show AsSmall.up.obj Y ⟶ Z from ⟨b⟩) ≫ a = ⟨f⟩ :=
        ULift.ext hab.symm
      exact he ▸ hh
    · intro hf
      exact ⟨AsSmall.up.obj Y, ⟨f⟩, 𝟙 _, hf, by simp⟩
  rw [heq]
  constructor
  · intro h
    exact asSmall_lift_cover J h
  · exact asSmall_lower_cover J

private theorem asSmall_site
    {C : Type u} [Category.{v} C] (J : Precoverage C) (hJ : J.IsSiteForCoverings) :
    (J.comap (AsSmall.down : AsSmall.{0} C ⥤ C)).IsSiteForCoverings := by
  have : J.HasIsos := hJ.1
  have : (AsSmall.down : AsSmall.{0} C ⥤ C).IsEquivalence :=
    (AsSmall.equiv : C ≌ AsSmall.{0} C).isEquivalence_inverse
  refine ⟨inferInstance, ?_, ?_⟩
  · intro X R T hR hT
    let T' : ∀ ⦃Y : C⦄ (f : Y ⟶ (ULift.down X)), R.map AsSmall.down f → Presieve Y :=
      fun Y f hf ↦ (T (show AsSmall.up.obj Y ⟶ X from ⟨f⟩)
        ((asSmall_map_iff R f).mp hf)).map AsSmall.down
    have ht : ∀ (Y : C) (f : Y ⟶ (ULift.down X)) (hf : R.map AsSmall.down f), T' f hf ∈ J Y :=
      fun Y f hf ↦ hT (AsSmall.up.obj Y) ⟨f⟩ ((asSmall_map_iff R f).mp hf)
    have hh := hJ.2.1 (ULift.down X) (R.map AsSmall.down) T' hR ht
    change ((R.bind (fun _ f hf ↦ T f hf)).map AsSmall.down) ∈ J _
    suffices heq : (R.bind (fun _ f hf ↦ T f hf)).map AsSmall.down =
        (R.map AsSmall.down).bind (fun _ f hf ↦ T' f hf) by rw [heq]; exact hh
    funext Y f
    apply propext
    constructor
    · rintro ⟨⟨Z, a, b, ha, hb, rfl⟩⟩
      exact ⟨(ULift.down Z), a.down, b.down, ⟨ha⟩, ⟨hb⟩, rfl⟩
    · rintro ⟨Z, a, b, ha, hb, hab⟩
      apply (asSmall_map_iff _ f).mpr
      refine ⟨AsSmall.up.obj Z, ⟨a⟩, ⟨b⟩, (asSmall_map_iff R b).mp ha,
        (asSmall_map_iff _ a).mp hb, ?_⟩
      exact ULift.ext hab
  · intro I X U a ha Y b
    obtain ⟨P, p, q, hp, hP⟩ := hJ.2.2 I (ULift.down X) (fun i ↦ ULift.down (U i))
      (fun i ↦ (a i).down) (by simpa only [Precoverage.mem_comap_iff, Presieve.map_ofArrows,
        AsSmall.down] using ha) (ULift.down Y) b.down
    refine ⟨fun i ↦ AsSmall.up.obj (P i), fun i ↦ ⟨p i⟩, fun i ↦ ⟨q i⟩, ?_, ?_⟩
    · intro i
      exact IsPullback.of_map_of_faithful AsSmall.down (hp i)
    · simpa only [Precoverage.mem_comap_iff, Presieve.map_ofArrows,
        AsSmall.down, AsSmall.up] using hP

private theorem exists_cover
    {C : Type u} [Category.{v} C] (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    {X : C} {S : Sieve X} (hS : S ∈ J.toGrothendieck X) :
    ∃ R : Presieve X, R ∈ J X ∧ R ≤ S.arrows := by
  have : J.HasIsos := hJ.1
  induction hS with
  | of X R hR => exact ⟨R, hR, Sieve.le_generate R⟩
  | top X => exact ⟨Presieve.singleton (𝟙 X),
      Precoverage.mem_coverings_of_isIso _, le_top⟩
  | pullback X S hS Y f ih =>
    obtain ⟨R, hR, hle⟩ := ih
    obtain ⟨I, U, a, rfl⟩ := R.exists_eq_ofArrows
    obtain ⟨P, p, q, hp, hP⟩ := hJ.2.2 I X U a hR Y f
    refine ⟨Presieve.ofArrows P p, hP, ?_⟩
    rintro Z b ⟨i⟩
    change S (p i ≫ f)
    rw [(hp i).w]
    exact S.downward_closed (hle _ _ ⟨i⟩) _
  | transitive X S T hS hT ihS ihT =>
    obtain ⟨R, hR, hle⟩ := ihS
    choose A hA hleA using fun (Y : C) (f : Y ⟶ X) (hf : R f) ↦ ihT (hle Y f hf)
    refine ⟨R.bind (fun Y f hf ↦ A Y f hf),
      hJ.2.1 X R (fun Y f hf ↦ A Y f hf) hR hA, ?_⟩
    rintro Z f ⟨Y, a, b, hb, ha, rfl⟩
    exact hleA Y b hb Z a ha

private theorem over_map_iff
    {C : Type u} [Category.{v} C] {B : C} {X : Over B} (R : Presieve X)
    {Y : C} (f : Y ⟶ X.left) :
    R.map (Over.forget B) f ↔
      R (Over.homMk f : Over.mk (f ≫ X.hom) ⟶ X) := by
  rw [Presieve.map_iff]
  constructor
  · rintro ⟨Z, hZ, g, hg, he⟩
    subst hZ
    have he' : g.left = f := by simpa using he
    subst f
    rcases Z with ⟨Z, ⟨⟨⟩⟩, z⟩
    rcases g with ⟨g, r, hg'⟩
    change Z ⟶ X.left at g
    change Z ⟶ B at z
    change (⟨⟨⟩⟩ : Discrete PUnit) ⟶ X.right at r
    have hz : g ≫ X.hom = z := by simpa using hg'
    subst z
    exact hg
  · intro h
    exact ⟨Over.mk (f ≫ X.hom), rfl, Over.homMk f, h, by simp⟩

private theorem over_map_apply
    {C : Type u} [Category.{v} C] {B : C} {X Y : Over B}
    (R : Presieve X) (f : Y ⟶ X) :
    R.map (Over.forget B) f.left ↔ R f := by
  rcases Y with ⟨Y, ⟨⟨⟩⟩, y⟩
  rcases f with ⟨f, r, hf⟩
  change Y ⟶ X.left at f
  change Y ⟶ B at y
  change (⟨⟨⟩⟩ : Discrete PUnit) ⟶ X.right at r
  have hf' : f ≫ X.hom = y := by simpa using hf
  subst y
  exact over_map_iff R f

private theorem over_site
    {C : Type u} [Category.{v} C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings) (B : C) :
    (J.comap (Over.forget B)).IsSiteForCoverings := by
  have : J.HasIsos := hJ.1
  refine ⟨inferInstance, ?_, ?_⟩
  · intro X R T hR hT
    let T' : ∀ ⦃Y : C⦄ (f : Y ⟶ X.left), R.map (Over.forget B) f → Presieve Y :=
      fun Y f hf ↦ (T (Over.homMk f : Over.mk (f ≫ X.hom) ⟶ X)
        ((over_map_iff R f).mp hf)).map (Over.forget B)
    have ht : ∀ (Y : C) (f : Y ⟶ X.left) (hf : R.map (Over.forget B) f),
        T' f hf ∈ J Y :=
      fun Y f hf ↦ hT _ _ ((over_map_iff R f).mp hf)
    have hh := hJ.2.1 X.left (R.map (Over.forget B)) T' hR ht
    change (R.bind (fun _ f hf ↦ T f hf)).map (Over.forget B) ∈ J _
    suffices heq : (R.bind (fun _ f hf ↦ T f hf)).map (Over.forget B) =
        (R.map (Over.forget B)).bind (fun _ f hf ↦ T' f hf) by rw [heq]; exact hh
    funext Y f
    apply propext
    constructor
    · rw [over_map_iff]
      rintro ⟨Z, a, b, ha, hb, hab⟩
      refine ⟨Z.left, a.left, b.left, (over_map_apply R b).mpr ha, ?_,
        congrArg Over.Hom.left hab⟩
      dsimp only [T']
      rcases Z with ⟨Z, ⟨⟨⟩⟩, z⟩
      rcases b with ⟨b, r, hb'⟩
      change Z ⟶ X.left at b
      change Z ⟶ B at z
      change (⟨⟨⟩⟩ : Discrete PUnit) ⟶ X.right at r
      have hz : b ≫ X.hom = z := by simpa using hb'
      subst z
      exact ⟨hb⟩
    · rintro ⟨Z, a, b, ha, hb, hab⟩
      change (T (Over.homMk b : Over.mk (b ≫ X.hom) ⟶ X) _).map
        (Over.forget B) a at hb
      rw [Presieve.map_iff] at hb
      obtain ⟨V, hV, c, hc, he⟩ := hb
      subst hV
      have he' : c.left = a := by simpa using he
      subst a
      rw [← hab]
      exact Presieve.map_map (F := Over.forget B) (f := c ≫ Over.homMk b)
        ⟨Over.mk (b ≫ X.hom), c, Over.homMk b,
          (over_map_iff R b).mp ha, hc, rfl⟩
  · intro I X U a ha Y b
    obtain ⟨P, p, q, hp, hP⟩ := hJ.2.2 I X.left (fun i ↦ (U i).left)
      (fun i ↦ (a i).left) (by simpa using ha) Y.left b.left
    let V := fun i ↦ Over.mk (p i ≫ Y.hom)
    let p' : ∀ i, V i ⟶ Y := fun i ↦ Over.homMk (p i)
    let q' : ∀ i, V i ⟶ U i := fun i ↦ Over.homMk (q i) (by
      rw [← Over.w (a i), ← Category.assoc, ← (hp i).w, Category.assoc, Over.w b]
      rfl)
    refine ⟨V, p', q', ?_, ?_⟩
    · intro i
      exact IsPullback.of_map_of_faithful (Over.forget B)
        (f := p' i) (g := q' i) (h := b) (i := a i) (hp i)
    · simpa [V, p'] using hP

private theorem over_topology
    {C : Type u} [Category.{v} C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings) (B : C) :
    J.toGrothendieck.over B = (J.comap (Over.forget B)).toGrothendieck := by
  apply le_antisymm
  · intro X S hS
    obtain ⟨R, hR, hle⟩ := exists_cover J hJ hS
    let R' := R.functorPullback (Over.forget B) (X := X)
    have heq : R'.map (Over.forget B) = R := by
      funext Y f
      exact propext (over_map_iff R' f)
    have hR' : R' ∈ (J.comap (Over.forget B)) X := by
      change R'.map (Over.forget B) ∈ J X.left
      rwa [heq]
    apply GrothendieckTopology.superset_covering _ _
      ((J.comap (Over.forget B)).generate_mem_toGrothendieck hR')
    rw [Sieve.generate_le_iff]
    intro Y f hf
    have hh := hle Y.left f.left hf
    rw [Sieve.overEquiv_iff] at hh
    exact (over_map_apply S.arrows f).mp
      ((over_map_iff S.arrows f.left).mpr hh)
  · intro X S hS
    obtain ⟨R, hR, hle⟩ := exists_cover _ (over_site J hJ B) hS
    apply (J.toGrothendieck.over B).superset_covering
      ((Sieve.generate_le_iff _ _).mpr hle)
    change Sieve.overEquiv X (Sieve.generate R) ∈ J.toGrothendieck X.left
    rw [Sieve.overEquiv_generate]
    apply J.toGrothendieck.superset_covering _ (J.generate_mem_toGrothendieck hR)
    rw [Sieve.generate_le_iff]
    intro Y f hf
    apply Sieve.le_generate
    exact Presieve.map_le_functorPushforward _ _ _ _ hf

private theorem finitarySite_large_enoughPoints
    {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (hfinite : ∀ (X : C) (I : Type (max u v)) (U : I → C)
      (f : ∀ i, U i ⟶ X), Presieve.ofArrows U f ∈ J X →
        ∃ (K : Type (max u v)) (_ : Finite K) (V : K → C) (g : ∀ k, V k ⟶ X)
          (r : K → I), Presieve.ofArrows V g ∈ J X ∧
            ∀ k, ∃ (q : V k ⟶ U (r k)), q ≫ f (r k) = g k) :
    ∃ (ι : Type (max u v w))
      (p : ι → GeometricMorphism (Type (max u v w))
        (Sheaf J.toGrothendieck (Type (max u v w)))),
      ∀ {F G : Sheaf J.toGrothendieck (Type (max u v w))} (a : F ⟶ G),
        (∀ i, Function.Bijective ((p i).inverse.map a)) → IsIso a := by
  let D := AsSmall.{0} C
  let d : D ⥤ C := AsSmall.down
  have : d.IsEquivalence := (AsSmall.equiv : C ≌ D).isEquivalence_inverse
  have : HasFiniteLimits D := ⟨fun A _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence d⟩
  let K := J.comap d
  have hfin : ∀ (X : D) (I : Type (max u v)) (U : I → D)
      (f : ∀ i, U i ⟶ X), Presieve.ofArrows U f ∈ K X →
        ∃ (A : Type (max u v)) (_ : Finite A) (V : A → D) (g : ∀ a, V a ⟶ X)
          (r : A → I), Presieve.ofArrows V g ∈ K X ∧
            ∀ a, ∃ (q : V a ⟶ U (r a)), q ≫ f (r a) = g a := by
    intro X I U f hf
    obtain ⟨A, hA, V, g, r, hg, hq⟩ := hfinite (d.obj X) I (fun i ↦ d.obj (U i))
      (fun i ↦ d.map (f i)) (by simpa [K] using hf)
    refine ⟨A, hA, fun a ↦ AsSmall.up.obj (V a), fun a ↦ ⟨g a⟩, r, ?_, ?_⟩
    · simpa [K, d, AsSmall.up, AsSmall.down] using hg
    · intro a
      obtain ⟨q, hq⟩ := hq a
      exact ⟨⟨q⟩, ULift.ext hq⟩
  obtain ⟨ι, p, hp⟩ := finitarySite_enoughPoints.{max u v, 0, w} K (asSmall_site J hJ) hfin
  have : (AsSmall.equiv : C ≌ D).inverse.IsDenseSubsite
      K.toGrothendieck J.toGrothendieck := by
    change (AsSmall.down : D ⥤ C).IsDenseSubsite K.toGrothendieck J.toGrothendieck
    exact asSmall_dense J
  let E := (AsSmall.equiv : C ≌ D).sheafCongr J.toGrothendieck K.toGrothendieck
    (Type (max u v w))
  let e : GeometricMorphism (Sheaf K.toGrothendieck (Type (max u v w)))
      (Sheaf J.toGrothendieck (Type (max u v w))) :=
    ⟨E.functor, E.inverse, E.toAdjunction, inferInstance⟩
  refine ⟨ι, fun i ↦ (p i).comp e, ?_⟩
  intro F G a ha
  have : IsIso (E.functor.map a) := hp _ ha
  exact isIso_of_reflects_iso a E.functor

private theorem coversTop_of_epi
    {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
    (I : Type (max u v w)) (U : I → C)
    (hcover : Epi (terminal.from
      (∐ fun i : I => (presheafToSheaf K (Type (max u v w))).obj
        (uliftYoneda.{max u w}.obj (U i))))) : K.CoversTop U := by
  classical
  let S := presheafToSheaf K (Type (max u v w))
  let Y := fun i : I ↦ uliftYoneda.{max u w}.obj (U i)
  let P := ∐ Y
  let T : Cᵒᵖ ⥤ Type (max u v w) := (Functor.const _).obj PUnit
  have hT0 : IsTerminal T := Functor.isTerminal (fun _ ↦ Types.isTerminalPUnit)
  let f : P ⟶ T := hT0.from P
  have hT : IsTerminal (S.obj T) := hT0.isTerminalObj S
  have hST : IsIso (terminal.from (S.obj T)) := isIso_of_isTerminal hT terminalIsTerminal _
  have hepi : Epi (S.map f) := by
    have hfac : sigmaComparison S Y ≫ S.map f ≫ terminal.from (S.obj T) =
        terminal.from (∐ fun i ↦ S.obj (Y i)) := terminal.hom_ext _ _
    have : Epi (S.map f ≫ terminal.from (S.obj T)) := epi_of_epi_fac hfac
    exact (epi_comp_iff_of_isIso _ _).mp this
  have hP : Presheaf.IsLocallySurjective K (toSheafify K P) :=
    unit_locally_surjective K P
  have hTsh : Presheaf.IsSheaf K T :=
    Presheaf.isSheaf_of_isTerminal K Types.isTerminalPUnit
  have : IsIso (toSheafify K T) := isIso_toSheafify K hTsh
  have : Sheaf.IsLocallySurjective (S.map f) :=
    (Sheaf.isLocallySurjective_iff_epi _).mpr hepi
  have hf : Presheaf.IsLocallySurjective K f := by
    rw [← Presheaf.isLocallySurjective_comp_iff K f (toSheafify K T),
      toSheafify_naturality]
    infer_instance
  intro W
  let t : T.obj (Opposite.op W) := PUnit.unit
  apply K.superset_covering _ (Presheaf.imageSieve_mem K f t)
  intro V a ha
  obtain ⟨s, hs⟩ := ha
  obtain ⟨⟨i⟩, b, hb⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj (Opposite.op V))
      (coproductIsCoproduct Y)) s
  exact ⟨i, ⟨b.down⟩⟩

/-- A cover of the terminal sheaf by sheafified representables whose slices have finite
limits and finite covering refinements gives a conservative set of points.
Source: Stacks Project, Sites, Lemma 0DW0, `lemma-criterion-points`, Section 00YN
(auxiliary; not a blueprint node).

The localized covering families are exactly `J.comap (Over.forget (U i))`: membership
means that the underlying family covers in `C`, and its generated topology is
`J.toGrothendieck.over (U i)` (def-pur-localized-ringed-site). The representables
are explicitly sheafified; subcanonicity is not assumed. The value and point-index
universe `max u v w` contains both site universes (prose-01-10).
Every covering presieve has a presentation indexed in `Type (max u v)`, so the
finite-refinement condition covers arbitrary presentations, including repetitions.

Proof, following Stacks 0DW0:
1. The site axioms pass to each slice. A covering sieve contains an actual covering
   presieve, by induction on the generated topology using bind composition and the
   chosen covering pullbacks. This identifies the slice's generated topology with
   `J.toGrothendieck.over (U i)`. Transport each slice to `AsSmall`, apply
   `finitarySite_enoughPoints`, and transport its conservative family back through
   the sheaf equivalence. All transports preserve the displayed universes.
2. Mathlib's continuous and cocontinuous `Over.forget` gives the restriction
   adjunction; restriction preserves finite limits. Compose its geometric morphism
   with the slice points and index the result by the dependent sum of their indices.
3. Sheafification preserves coproducts and the terminal object. Consequently the
   terminal map from the presheaf coproduct becomes epic after sheafification.
   Epimorphisms of sheaves are locally surjective, and the sheafification unit is
   locally surjective (the proved `unit_locally_surjective` helper in the source's
   local-sections module). Naturality of the unit and its being an isomorphism on
   the terminal presheaf give local surjectivity before sheafification. Every local
   section of the coproduct belongs to a representable summand, hence gives a map
   to some `U i`. This proves `CoversTop U`.
4. Conservativity on every slice gives an isomorphism after every restriction.
   Mathlib's `Sheaf.isIso_of_coversTop` descends these to an isomorphism globally.
   The dependent sum and the descent theorem also handle an empty covering family. -/
theorem finitarySlice_enoughPoints
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (I : Type (max u v w)) (U : I → C)
    (hcover : Epi (terminal.from
      (∐ fun i : I => (presheafToSheaf J.toGrothendieck (Type (max u v w))).obj
        (uliftYoneda.{max u w}.obj (U i)))))
    (hlimits : ∀ i : I, HasFiniteLimits (Over (U i)))
    (hfinite : ∀ (i : I) (X : Over (U i)) (A : Type (max u v))
      (V : A → Over (U i)) (f : ∀ a, V a ⟶ X),
      Presieve.ofArrows V f ∈ (J.comap (Over.forget (U i))) X →
        ∃ (K : Type (max u v)) (_ : Finite K) (W : K → Over (U i))
          (g : ∀ k, W k ⟶ X) (r : K → A),
          Presieve.ofArrows W g ∈ (J.comap (Over.forget (U i))) X ∧
            ∀ k, ∃ (q : W k ⟶ V (r k)), q ≫ f (r k) = g k) :
    ∃ (ι : Type (max u v w))
      (p : ι → GeometricMorphism (Type (max u v w))
        (Sheaf J.toGrothendieck (Type (max u v w)))),
      ∀ {F G : Sheaf J.toGrothendieck (Type (max u v w))} (a : F ⟶ G),
        (∀ j, Function.Bijective ((p j).inverse.map a)) → IsIso a := by
  classical
  have hpoints (i : I) :
      ∃ (ι : Type (max u v w))
        (p : ι → GeometricMorphism (Type (max u v w))
          (Sheaf (J.toGrothendieck.over (U i)) (Type (max u v w)))),
        ∀ {F G : Sheaf (J.toGrothendieck.over (U i)) (Type (max u v w))}
          (a : F ⟶ G), (∀ j, Function.Bijective ((p j).inverse.map a)) → IsIso a := by
    have : HasFiniteLimits (Over (U i)) := hlimits i
    have h := finitarySite_large_enoughPoints.{max u v, v, w}
      (J.comap (Over.forget (U i))) (over_site J hJ (U i)) (hfinite i)
    rwa [← over_topology J hJ (U i)] at h
  choose Q p hp using hpoints
  let r (i : I) : GeometricMorphism
      (Sheaf (J.toGrothendieck.over (U i)) (Type (max u v w)))
      (Sheaf J.toGrothendieck (Type (max u v w))) :=
    { inverse := J.toGrothendieck.overPullback (Type (max u v w)) (U i)
      direct := (Over.forget (U i)).sheafPushforwardCocontinuous _ _ _
      adj := (Over.forget (U i)).sheafAdjunctionCocontinuous _ _ _
      leftExact := inferInstance }
  refine ⟨(i : I) × Q i, fun j ↦ (p j.1 j.2).comp (r j.1), ?_⟩
  intro F G a ha
  apply Sheaf.isIso_of_coversTop (coversTop_of_epi J.toGrothendieck I U hcover)
  intro i
  exact hp i _ (fun q ↦ ha ⟨i, q⟩)

end CategoryTheory
