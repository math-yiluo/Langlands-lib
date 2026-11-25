/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening

/-!
# Globalization of affine lifting for universal first order thickenings

The affine-test lifting property globalizes by affine covers and morphism gluing.
(blueprint: lem-weil-pbc-universal-first-order-thickening-globalization)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Open base change preserves a first order thickening: its kernel ideals are
transported by the isomorphism on sections of the open immersion. -/
private theorem firstOrderThickening_pullback_open
    {T T' U' : Scheme.{u}} (j : T ⟶ T') (g : U' ⟶ T')
    [IsOpenImmersion g] (hj : IsFirstOrderThickening j) :
    IsFirstOrderThickening (Limits.pullback.snd j g) := by
  let jU := Limits.pullback.snd j g
  let f := Limits.pullback.fst j g
  have H : IsPullback jU f g j := (IsPullback.of_hasPullback j g).flip
  have : IsClosedImmersion j := hj.1
  have : IsClosedImmersion jU := MorphismProperty.of_isPullback H.flip inferInstance
  refine ⟨inferInstance, ?_⟩
  apply Scheme.IdealSheafData.ext
  funext V
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion j jU f g H]
  apply le_bot_iff.mp
  apply (Ideal.le_comap_pow _ _).trans
  have hz := congrArg (fun J => J.ideal
    ⟨g ''ᵁ V, V.2.image_of_isOpenImmersion g⟩) hj.2
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] at hz
  rw [hz]
  exact (Ideal.comap_bot_of_injective _
    (ConcreteCategory.bijective_of_isIso (g.appIso V).inv).1).le

/-- Uniqueness on affine test schemes gives uniqueness on any test scheme, by
restricting both solutions to an affine cover of the thickened test scheme. -/
private theorem unique_lifts_of_affine_tests
    {Z Z' X : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (H : ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (j : T ⟶ T')
      (b : T' ⟶ X) (a : T ⟶ Z), IsFirstOrderThickening j → j ≫ b = a ≫ h →
        ∃! c : T' ⟶ Z', c ≫ h' = b ∧ j ≫ c = a ≫ i)
    {T T' : Scheme.{u}} (j : T ⟶ T') (b : T' ⟶ X) (a : T ⟶ Z)
    (hj : IsFirstOrderThickening j) (hab : j ≫ b = a ≫ h)
    {c d : T' ⟶ Z'} (hc : c ≫ h' = b ∧ j ≫ c = a ≫ i)
    (hd : d ≫ h' = b ∧ j ≫ d = a ≫ i) : c = d := by
  let C := T'.affineCover
  apply C.hom_ext
  intro k
  have hlocal : IsFirstOrderThickening (C.pullbackHom j k) :=
    firstOrderThickening_pullback_open j (C.f k) hj
  have : IsClosedImmersion (C.pullbackHom j k) := hlocal.1
  have : IsAffine ((C.pullback₁ j).X k) :=
    isAffine_of_isAffineHom (C.pullbackHom j k)
  have hablocal : C.pullbackHom j k ≫ (C.f k ≫ b) =
      ((C.pullback₁ j).f k ≫ a) ≫ h := by
    rw [← Category.assoc, C.pullbackHom_map, Category.assoc, hab, Category.assoc]
  apply (H (C.pullbackHom j k) (C.f k ≫ b) ((C.pullback₁ j).f k ≫ a)
    hlocal hablocal).unique
  · constructor
    · rw [Category.assoc, hc.1]
    · rw [← Category.assoc, C.pullbackHom_map, Category.assoc, hc.2, Category.assoc]
  · constructor
    · rw [Category.assoc, hd.1]
    · rw [← Category.assoc, C.pullbackHom_map, Category.assoc, hd.2, Category.assoc]

/-- Unique solutions on affine tests glue. First establish uniqueness on arbitrary
schemes; use it on overlaps, glue the local lifts, and check both triangles locally. -/
private theorem lifts_of_affine_tests
    {Z Z' X : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (H : ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (j : T ⟶ T')
      (b : T' ⟶ X) (a : T ⟶ Z), IsFirstOrderThickening j → j ≫ b = a ≫ h →
        ∃! c : T' ⟶ Z', c ≫ h' = b ∧ j ≫ c = a ≫ i)
    {T T' : Scheme.{u}} (j : T ⟶ T') (b : T' ⟶ X) (a : T ⟶ Z)
    (hj : IsFirstOrderThickening j) (hab : j ≫ b = a ≫ h) :
    ∃! c : T' ⟶ Z', c ≫ h' = b ∧ j ≫ c = a ≫ i := by
  classical
  let C := T'.affineCover
  have local_lift (k : C.I₀) : ∃! c : C.X k ⟶ Z',
      c ≫ h' = C.f k ≫ b ∧ C.pullbackHom j k ≫ c = ((C.pullback₁ j).f k ≫ a) ≫ i := by
    have hlocal := firstOrderThickening_pullback_open j (C.f k) hj
    have : IsClosedImmersion (C.pullbackHom j k) := hlocal.1
    have : IsAffine ((C.pullback₁ j).X k) :=
      isAffine_of_isAffineHom (C.pullbackHom j k)
    apply H
    · exact hlocal
    · rw [← Category.assoc, C.pullbackHom_map, Category.assoc, hab, Category.assoc]
  choose c hc using fun k => (local_lift k).exists
  have compat (k l : C.I₀) :
      Limits.pullback.fst (C.f k) (C.f l) ≫ c k =
      Limits.pullback.snd (C.f k) (C.f l) ≫ c l := by
    let p₁ := Limits.pullback.fst (C.f k) (C.f l)
    let p₂ := Limits.pullback.snd (C.f k) (C.f l)
    let e := p₁ ≫ C.f k
    let jP := Limits.pullback.snd j e
    let tP := Limits.pullback.fst j e
    have he : p₁ ≫ C.f k = p₂ ≫ C.f l := Limits.pullback.condition
    have hP : IsFirstOrderThickening jP :=
      firstOrderThickening_pullback_open j e hj
    have w₁ : tP ≫ j = (jP ≫ p₁) ≫ C.f k := by
      simpa only [Category.assoc] using (Limits.pullback.condition (f := j) (g := e))
    have w₂ : tP ≫ j = (jP ≫ p₂) ≫ C.f l := by
      rw [Category.assoc, ← he]
      exact Limits.pullback.condition
    let u₁ := Limits.pullback.lift tP (jP ≫ p₁) w₁
    let u₂ := Limits.pullback.lift tP (jP ≫ p₂) w₂
    have fac₁ : jP ≫ (p₁ ≫ c k) = (tP ≫ a) ≫ i := by
      calc
        _ = u₁ ≫ (C.pullbackHom j k ≫ c k) := by
          simp only [u₁, Scheme.Cover.pullbackHom, Limits.pullback.lift_snd_assoc,
            Category.assoc]
        _ = u₁ ≫ (((C.pullback₁ j).f k ≫ a) ≫ i) := by rw [(hc k).2]
        _ = (tP ≫ a) ≫ i := by
          change u₁ ≫ ((Limits.pullback.fst j (C.f k) ≫ a) ≫ i) = (tP ≫ a) ≫ i
          simp only [Category.assoc, u₁, Limits.pullback.lift_fst_assoc]
    have fac₂ : jP ≫ (p₂ ≫ c l) = (tP ≫ a) ≫ i := by
      calc
        _ = u₂ ≫ (C.pullbackHom j l ≫ c l) := by
          simp only [u₂, Scheme.Cover.pullbackHom, Limits.pullback.lift_snd_assoc,
            Category.assoc]
        _ = u₂ ≫ (((C.pullback₁ j).f l ≫ a) ≫ i) := by rw [(hc l).2]
        _ = (tP ≫ a) ≫ i := by
          change u₂ ≫ ((Limits.pullback.fst j (C.f l) ≫ a) ≫ i) = (tP ≫ a) ≫ i
          simp only [Category.assoc, u₂, Limits.pullback.lift_fst_assoc]
    apply unique_lifts_of_affine_tests h i h' H jP (e ≫ b) (tP ≫ a) hP
    · rw [← Category.assoc, ← Limits.pullback.condition (f := j) (g := e),
        Category.assoc, hab,
        Category.assoc]
    · exact ⟨by rw [Category.assoc, (hc k).1, ← Category.assoc], fac₁⟩
    · exact ⟨by rw [Category.assoc, (hc l).1, ← Category.assoc, ← he], fac₂⟩
  let c' := C.glueMorphisms c compat
  have hc' : c' ≫ h' = b ∧ j ≫ c' = a ≫ i := by
    constructor
    · apply C.hom_ext
      intro k
      simpa only [c', C.ι_glueMorphisms_assoc] using (hc k).1
    · apply Scheme.Cover.hom_ext (C.pullback₁ j)
      intro k
      change C.I₀ at k
      rw [← C.pullbackHom_map_assoc,
        show C.f k ≫ c' = c k from C.ι_glueMorphisms c compat k]
      simpa only [Category.assoc] using (hc k).2
  exact ⟨c', hc', fun d hd => unique_lifts_of_affine_tests h i h' H j b a hj hab hd hc'⟩

/-- Affine-test universality of a first-order thickening implies universality for all
test schemes. Source: Stacks, More on Morphisms, Lemma 37.7.1 (Tag 04F3), gluing step.
(blueprint: lem-weil-pbc-universal-first-order-thickening-globalization)
Proof: cover the test target by affine opens, apply affine-test uniqueness and existence,
then glue the local lifts; equality on overlaps follows from affine-test uniqueness. -/
theorem isUniversalFirstOrderThickening_of_affine_local
    {Z X Z' : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (hi : IsFirstOrderThickening i) (hcomp : i ≫ h' = h)
    (haffine : ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
      (j : T ⟶ T') (b : T' ⟶ X) (a : T ⟶ Z),
      IsFirstOrderThickening j → j ≫ b = a ≫ h →
        ∃! a' : T' ⟶ Z', a' ≫ h' = b ∧ j ≫ a' = a ≫ i) :
    IsUniversalFirstOrderThickening h i h' := by
  refine ⟨hi, hcomp, ?_⟩
  exact lifts_of_affine_tests h i h' haffine

end AlgebraicGeometry
