/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.UniversalThickeningOpenPieces
import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickeningGluedAtlas

/-!
# Gluing universal first order thickenings on an open cover

Source: Stacks Project, More on Morphisms, Lemma 37.7.1 (Tag 04F3),
last two paragraphs. This gluing assertion does not assume formal unramifiedness.
(blueprint: lem-weil-pbc-universal-first-order-thickening-cover-gluing)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The open-pieces theorem gives an injective preimage map on opens; for a
closed immersion this forces its image to be the whole target. -/
private theorem firstOrder_homeomorph {T T' : Scheme.{u}} (i : T ⟶ T')
    (hi : IsFirstOrderThickening i) : IsHomeomorph i := by
  have : IsClosedImmersion i := hi.1
  apply isHomeomorph_iff_isEmbedding_surjective.mpr
  refine ⟨i.isClosedEmbedding.isEmbedding, ?_⟩
  have hopen := ((universalFirstOrderThickening_open_pieces (𝟙 T')).1
    i (𝟙 T') hi).2
  let V : T'.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hV : i ⁻¹ᵁ V = ⊥ := by
    ext x
    simp [V]
  have hb : i ⁻¹ᵁ (⊥ : T'.Opens) = ⊥ := by
    ext x
    simp
  have he : V = ⊥ := (hopen ⊥).unique hV hb
  intro y
  by_contra hy
  have hyV : y ∈ V := hy
  rw [he] at hyV
  exact hyV

/-- A lifting problem whose source lands in one universal chart has a unique lift
into the whole thickening. Every competing lift also lands in that chart on points. -/
private theorem lift_in_chart
    {Z W X : Scheme.{u}} (h : Z ⟶ X) (j : Z ⟶ W) (p : W ⟶ X)
    (D : W.OpenCover.{u})
    (H : ∀ k, IsUniversalFirstOrderThickening ((D.pullback₁ j).f k ≫ h)
      (D.pullbackHom j k) (D.f k ≫ p))
    {T T' : Scheme.{u}} (t : T ⟶ T') (b : T' ⟶ X) (a : T ⟶ Z)
    (ht : IsFirstOrderThickening t) (hab : t ≫ b = a ≫ h)
    (k : D.I₀) (ha : Set.range (a ≫ j) ⊆ Set.range (D.f k)) :
    ∃! c : T' ⟶ W, c ≫ p = b ∧ t ≫ c = a ≫ j := by
  let α := IsOpenImmersion.lift (D.f k) (a ≫ j) ha
  have hα : α ≫ D.f k = a ≫ j := IsOpenImmersion.lift_fac _ _ _
  let aD := Limits.pullback.lift a α hα.symm
  have haD : aD ≫ (D.pullback₁ j).f k = a := by
    exact Limits.pullback.lift_fst _ _ _
  have haDj : aD ≫ D.pullbackHom j k = α := by
    exact Limits.pullback.lift_snd _ _ _
  obtain ⟨c, hc, huniq⟩ := (H k).2.2 t b aD ht (by
    rw [← Category.assoc, haD, hab])
  refine ⟨c ≫ D.f k, ⟨?_, ?_⟩, ?_⟩
  · simpa only [Category.assoc] using hc.1
  · rw [← Category.assoc, hc.2, haDj, hα]
  · intro c' hc'
    have hr : Set.range c' ⊆ Set.range (D.f k) := by
      rintro _ ⟨t', rfl⟩
      obtain ⟨x, rfl⟩ := (firstOrder_homeomorph t ht).surjective t'
      have hx := congrArg (fun f : T ⟶ W ↦ f x) hc'.2
      rw [Scheme.Hom.comp_apply] at hx
      rw [hx]
      exact ha ⟨x, rfl⟩
    let cD := IsOpenImmersion.lift (D.f k) c' hr
    have hcD : cD ≫ D.f k = c' := IsOpenImmersion.lift_fac _ _ _
    have heq : cD = c := by
      apply huniq cD
      refine ⟨?_, ?_⟩
      · rw [← Category.assoc, hcD, hc'.1]
      · apply (cancel_mono (D.f k)).mp
        rw [Category.assoc, hcD, hc'.2, haDj, hα]
    rw [← hcD, heq]

/-- Chartwise uniqueness descends to arbitrary test schemes. -/
private theorem unique_lifts_on_charts
    {Z W X : Scheme.{u}} (h : Z ⟶ X) (j : Z ⟶ W) (p : W ⟶ X)
    (D : W.OpenCover.{u})
    (H : ∀ k, IsUniversalFirstOrderThickening ((D.pullback₁ j).f k ≫ h)
      (D.pullbackHom j k) (D.f k ≫ p))
    {T T' : Scheme.{u}} (t : T ⟶ T') (b : T' ⟶ X) (a : T ⟶ Z)
    (ht : IsFirstOrderThickening t) (hab : t ≫ b = a ≫ h)
    {c d : T' ⟶ W} (hc : c ≫ p = b ∧ t ≫ c = a ≫ j)
    (hd : d ≫ p = b ∧ t ≫ d = a ≫ j) : c = d := by
  have : IsClosedImmersion t := ht.1
  let e := (isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨t.isClosedEmbedding.isEmbedding, (firstOrder_homeomorph t ht).surjective⟩).homeomorph
  apply Scheme.hom_ext_of_forall
  intro x'
  obtain ⟨x, rfl⟩ := (firstOrder_homeomorph t ht).surjective x'
  obtain ⟨k, y, hy⟩ := D.exists_eq ((a ≫ j) x)
  let U : T'.Opens := e.opensCongr ((a ≫ j) ⁻¹ᵁ (D.f k).opensRange)
  have hU : t ⁻¹ᵁ U = (a ≫ j) ⁻¹ᵁ (D.f k).opensRange :=
    e.opensCongr.symm_apply_apply _
  refine ⟨U, ?_, ?_⟩
  · change x ∈ t ⁻¹ᵁ U
    rw [hU]
    exact ⟨y, hy⟩
  · have htU := ((universalFirstOrderThickening_open_pieces h).1 t b ht).1 U |>.1
    have habU : (t ∣_ U) ≫ (U.ι ≫ b) = ((t ⁻¹ᵁ U).ι ≫ a) ≫ h := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hab, Category.assoc]
    have haU : Set.range (((t ⁻¹ᵁ U).ι ≫ a) ≫ j) ⊆ Set.range (D.f k) := by
      rintro _ ⟨z, rfl⟩
      exact hU.le z.2
    apply (lift_in_chart h j p D H (t ∣_ U) (U.ι ≫ b)
      ((t ⁻¹ᵁ U).ι ≫ a) htU habU k haU).unique
    · constructor
      · rw [Category.assoc, hc.1]
      · rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hc.2, Category.assoc]
    · constructor
      · rw [Category.assoc, hd.1]
      · rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hd.2, Category.assoc]

/-- Open pullback preserves the square-zero kernel condition. -/
private theorem firstOrder_pullback_open
    {T T' U U' : Scheme.{u}} (t : T ⟶ T') (tU : U ⟶ U')
    (f : U ⟶ T) (g : U' ⟶ T') [IsOpenImmersion g]
    (H : IsPullback tU f g t) (ht : IsFirstOrderThickening t) :
    IsFirstOrderThickening tU := by
  have : IsClosedImmersion t := ht.1
  have : IsClosedImmersion tU := MorphismProperty.of_isPullback H.flip inferInstance
  refine ⟨inferInstance, ?_⟩
  apply Scheme.IdealSheafData.ext
  funext V
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion t tU f g H]
  apply le_bot_iff.mp
  apply (Ideal.le_comap_pow _ _).trans
  have hz := congrArg (fun J ↦ J.ideal
    ⟨g ''ᵁ V, V.2.image_of_isOpenImmersion g⟩) ht.2
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] at hz
  rw [hz]
  exact (Ideal.comap_bot_of_injective _
    (ConcreteCategory.bijective_of_isIso (g.appIso V).inv).1).le

/-- Local solutions on the transferred test cover agree by chartwise uniqueness,
and therefore glue to the unique global solution. -/
private theorem lifts_on_charts
    {Z W X : Scheme.{u}} (h : Z ⟶ X) (j : Z ⟶ W) (p : W ⟶ X)
    (D : W.OpenCover.{u})
    (H : ∀ k, IsUniversalFirstOrderThickening ((D.pullback₁ j).f k ≫ h)
      (D.pullbackHom j k) (D.f k ≫ p))
    {T T' : Scheme.{u}} (t : T ⟶ T') (b : T' ⟶ X) (a : T ⟶ Z)
    (ht : IsFirstOrderThickening t) (hab : t ≫ b = a ≫ h) :
    ∃! c : T' ⟶ W, c ≫ p = b ∧ t ≫ c = a ≫ j := by
  classical
  have : IsClosedImmersion t := ht.1
  let e := (isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨t.isClosedEmbedding.isEmbedding, (firstOrder_homeomorph t ht).surjective⟩).homeomorph
  let U (k : D.I₀) : T'.Opens := e.opensCongr ((a ≫ j) ⁻¹ᵁ (D.f k).opensRange)
  have hU (k : D.I₀) : t ⁻¹ᵁ U k = (a ≫ j) ⁻¹ᵁ (D.f k).opensRange :=
    e.opensCongr.symm_apply_apply _
  let E : T'.OpenCover.{u} := Scheme.Cover.mkOfCovers D.I₀
    (fun k ↦ (U k).toScheme) (fun k ↦ (U k).ι) (by
      intro x'
      obtain ⟨x, rfl⟩ := (firstOrder_homeomorph t ht).surjective x'
      obtain ⟨k, y, hy⟩ := D.exists_eq ((a ≫ j) x)
      exact ⟨k, ⟨t x, (hU k).ge ⟨y, hy⟩⟩, rfl⟩)
  have local_lift (k : E.I₀) : ∃! c : E.X k ⟶ W,
      c ≫ p = E.f k ≫ b ∧
        E.pullbackHom t k ≫ c = ((E.pullback₁ t).f k ≫ a) ≫ j := by
    refine lift_in_chart h j p D H _ _ _ ?_ ?_ k ?_
    · exact firstOrder_pullback_open t (E.pullbackHom t k)
        ((E.pullback₁ t).f k) (E.f k)
        (IsPullback.of_hasPullback t (E.f k)).flip ht
    · rw [← Category.assoc, E.pullbackHom_map, Category.assoc, hab, Category.assoc]
    · rintro _ ⟨z, rfl⟩
      have hz : ((E.pullback₁ t).f k) z ∈ t ⁻¹ᵁ U k := by
        change t (((E.pullback₁ t).f k) z) ∈ U k
        rw [← Scheme.Hom.comp_apply, ← E.pullbackHom_map, Scheme.Hom.comp_apply]
        exact (E.pullbackHom t k z).2
      exact (hU k).le hz
  choose c hc using fun k ↦ (local_lift k).exists
  have compat (k l : E.I₀) :
      Limits.pullback.fst (E.f k) (E.f l) ≫ c k =
      Limits.pullback.snd (E.f k) (E.f l) ≫ c l := by
    let p₁ := Limits.pullback.fst (E.f k) (E.f l)
    let p₂ := Limits.pullback.snd (E.f k) (E.f l)
    let q := p₁ ≫ E.f k
    let tP := Limits.pullback.snd t q
    let aP := Limits.pullback.fst t q
    have he : p₁ ≫ E.f k = p₂ ≫ E.f l := Limits.pullback.condition
    have htP : IsFirstOrderThickening tP :=
      firstOrder_pullback_open t tP aP q (IsPullback.of_hasPullback t q).flip ht
    have w₁ : aP ≫ t = (tP ≫ p₁) ≫ E.f k := by
      simpa only [Category.assoc] using (Limits.pullback.condition (f := t) (g := q))
    have w₂ : aP ≫ t = (tP ≫ p₂) ≫ E.f l := by
      rw [Category.assoc, ← he]
      exact Limits.pullback.condition
    let u₁ := Limits.pullback.lift aP (tP ≫ p₁) w₁
    let u₂ := Limits.pullback.lift aP (tP ≫ p₂) w₂
    have fac₁ : tP ≫ (p₁ ≫ c k) = (aP ≫ a) ≫ j := by
      calc
        _ = u₁ ≫ (E.pullbackHom t k ≫ c k) := by
          simp only [u₁, Scheme.Cover.pullbackHom, Limits.pullback.lift_snd_assoc,
            Category.assoc]
        _ = u₁ ≫ (((E.pullback₁ t).f k ≫ a) ≫ j) := by rw [(hc k).2]
        _ = (aP ≫ a) ≫ j := by
          change u₁ ≫ ((Limits.pullback.fst t (E.f k) ≫ a) ≫ j) = (aP ≫ a) ≫ j
          simp only [Category.assoc, u₁, Limits.pullback.lift_fst_assoc]
    have fac₂ : tP ≫ (p₂ ≫ c l) = (aP ≫ a) ≫ j := by
      calc
        _ = u₂ ≫ (E.pullbackHom t l ≫ c l) := by
          simp only [u₂, Scheme.Cover.pullbackHom, Limits.pullback.lift_snd_assoc,
            Category.assoc]
        _ = u₂ ≫ (((E.pullback₁ t).f l ≫ a) ≫ j) := by rw [(hc l).2]
        _ = (aP ≫ a) ≫ j := by
          change u₂ ≫ ((Limits.pullback.fst t (E.f l) ≫ a) ≫ j) = (aP ≫ a) ≫ j
          simp only [Category.assoc, u₂, Limits.pullback.lift_fst_assoc]
    apply unique_lifts_on_charts h j p D H tP (q ≫ b) (aP ≫ a) htP
    · rw [← Category.assoc, ← Limits.pullback.condition (f := t) (g := q),
        Category.assoc, hab, Category.assoc]
    · exact ⟨by rw [Category.assoc, (hc k).1, ← Category.assoc], fac₁⟩
    · exact ⟨by rw [Category.assoc, (hc l).1, ← Category.assoc, ← he], fac₂⟩
  let c' := E.glueMorphisms c compat
  have hc' : c' ≫ p = b ∧ t ≫ c' = a ≫ j := by
    constructor
    · apply E.hom_ext
      intro k
      simpa only [c', E.ι_glueMorphisms_assoc] using (hc k).1
    · apply Scheme.Cover.hom_ext (E.pullback₁ t)
      intro k
      change E.I₀ at k
      rw [← E.pullbackHom_map_assoc,
        show E.f k ≫ c' = c k from E.ι_glueMorphisms c compat k]
      simpa only [Category.assoc] using (hc k).2
  exact ⟨c', hc', fun d hd ↦ unique_lifts_on_charts h j p D H t b a ht hab hd hc'⟩

/-- Universal first order thickenings given on an open cover glue to a universal
first order thickening of the whole source. The local thickenings are explicit
input data; no existence or formal unramifiedness assumption on `h` is used.

Source: Stacks Project, More on Morphisms, proof of Lemma 37.7.1 (Tag 04F3),
paragraphs beginning "Choose an affine open covering" and "It turns out".
(blueprint: lem-weil-pbc-universal-first-order-thickening-cover-gluing)

Proof:
1. For each pair of charts of `C`, their fibre product is their open intersection.
   The first clause of `universalFirstOrderThickening_open_pieces` transfers this
   open to each local thickening. Its second clause says the restricted thickenings
   are universal over `X` (take the whole base as the base open).
2. Apply `IsUniversalFirstOrderThickening.unique` to identify the two thickenings
   of each intersection by their unique isomorphism over `X` fixing the intersection.
   On triple intersections both composites have these properties, so uniqueness
   proves the cocycle identity, including the identity on repeated indices.
3. Glue these schemes along the resulting open isomorphisms using scheme gluing.
   The local maps from `C.X k` and to `X` commute on intersections, hence glue to
   `i : Z ⟶ W` and `p : W ⟶ X` with `i ≫ p = h`. The local immersions are the
   restrictions of `i` along the glued open cover. Closed immersion is local on
   the target, and its kernel ideals restrict to those of the given immersions.
   Consequently `i` is a closed immersion and its ideal has square zero.
4. For a test thickening `j : T ⟶ T'` with a map `a : T ⟶ Z`, pull `C` back along
   `a` to cover `T`. The underlying homeomorphism of `j` gives the corresponding
   open cover of `T'`. Restricting `j` to these opens preserves square zero by
   the first clause of the open-pieces theorem. On each chart local universality
   produces a lift into the corresponding open of `W`.
5. On overlaps both lifts land in the thickening of the intersection: this follows
   on points from surjectivity of `j`. Universality on the intersection identifies
   them. Glue these morphisms into `W`, and verify both triangle identities locally.
   Any other lift has the same restrictions by local uniqueness, hence equals it.
   Together with step 3 these are precisely the three defining clauses. -/
theorem universalFirstOrderThickening_glue
    {Z X : Scheme.{u}} (h : Z ⟶ X) (C : Z.OpenCover.{u})
    (Z' : C.I₀ → Scheme.{u}) (i : ∀ k, C.X k ⟶ Z' k)
    (h' : ∀ k, Z' k ⟶ X)
    (H : ∀ k, IsUniversalFirstOrderThickening (C.f k ≫ h) (i k) (h' k)) :
    ∃ (W : Scheme.{u}) (j : Z ⟶ W) (p : W ⟶ X),
      IsUniversalFirstOrderThickening h j p := by
  obtain ⟨W, j, p, D, hj, hcomp, Hlocal⟩ :=
    universalFirstOrderThickening_gluedAtlas h C Z' i h' H
  refine ⟨W, j, p, hj, hcomp, ?_⟩
  intro T T' t b a ht hab
  exact lifts_on_charts h j p D Hlocal t b a ht hab

end AlgebraicGeometry
