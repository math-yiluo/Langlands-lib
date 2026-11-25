/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FpqcRefinementFullyFaithful

/-! Auxiliary step of effective fpqc descent, following the Stacks Project. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Canonical transport keeps the coordinate in the effective object fixed.
-- Source: Stacks Project, Tag 023V; same construction as the private helper in
-- Sheaf.AlgebraicGeometry.FiniteEtaleDescentDataExistence.
private noncomputable def pullbackDatum {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (P : Over Y) : Over.DescentDatum g (Over.mk (pullback.snd P.hom g)) where
  transport f₁ f₂ h z :=
    Over.homMk (pullback.lift (z.left ≫ pullback.fst P.hom g) f₂ (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact (congrArg (fun k ↦ k ≫ g) (Over.w z)).trans h))
      (by simp)
  transport_homMk_comp := by
    intros
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [Category.assoc]
  transport_self := by
    intro T f a
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp
    · simpa using (Over.w a).symm
  transport_transport := by
    intros
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp

/-- Effectivity descends through a refinement of singleton fpqc coverings.
Source: Stacks Project, Descent, Tag 02W3, affine-base proof, using Tag 02W0.
(blueprint: lem-galois-fpqc-refinement-reflects-effectivity)

Choose an effective object W over S for E. The canonical datum on W ×_S X has
pullback to X' canonically identified with E through the effective pullback square.
Full faithfulness of refinement descends this identification and its inverse to
maps between the canonical datum and D. Faithfulness makes their composites the
identities. The resulting isomorphism identifies V with W ×_S X and preserves
transport; hence its projection to W witnesses effectivity of D. No assumption
that h itself is fpqc is needed: both composite covers f and g are fpqc. The
identity refinement and empty base cases are included. -/
theorem fpqc_refinement_reflects_effectivity {S X X' : Scheme.{u}}
    (f : X ⟶ S) (g : X' ⟶ S) (h : X' ⟶ X)
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    (hg : Presieve.singleton g ∈ Scheme.fpqcPrecoverage S) (hc : h ≫ f = g)
    {V : Over X} {V' : Over X'} (q : V'.left ⟶ V.left)
    (hq : q ≫ V.hom = V'.hom ≫ h)
    (D : Over.DescentDatum f V) (E : Over.DescentDatum g V')
    (hp : IsPullback q V'.hom V.hom h)
    (hD : Over.DescentDatum.IsBaseChange hc hq D E) (hE : E.IsEffective) :
    D.IsEffective := by
  -- Realize E as the base change of the canonical datum on W ×_S X.
  obtain ⟨W, e, pe, he⟩ := hE
  let A : Over X := Over.mk (pullback.snd W.hom f)
  let C := pullbackDatum f W
  let r : V'.left ⟶ A.left := pullback.lift e (V'.hom ≫ h) (by
    rw [pe.w, Category.assoc, hc])
  have hr : r ≫ A.hom = V'.hom ≫ h := by simp [r, A]
  have pr : IsPullback r V'.hom A.hom h := by
    have outer : IsPullback (r ≫ pullback.fst W.hom f) V'.hom W.hom (h ≫ f) := by
      simpa [r, hc] using pe
    exact outer.of_right hr (IsPullback.of_hasPullback W.hom f)
  have bc : Over.DescentDatum.IsBaseChange hc hr C E := by
    intro T a b hab z
    apply pullback.hom_ext
    · simpa [C, pullbackDatum, r, Category.assoc] using (he a b hab z).symm
    · simp [C, pullbackDatum, r, Category.assoc]
  -- Descend the identity of the common realization in both directions.
  have ff := (fpqcRefinementFullyFaithful f g h hf hg hc).2
  have compat : ∀ {T : Scheme.{u}} (a b : T ⟶ X') (hab : a ≫ g = b ≫ g)
      (z : Over.mk a ⟶ V'),
      E.transport a b hab z ≫ 𝟙 V' = E.transport a b hab (z ≫ 𝟙 V') := by
    intros
    simp
  obtain ⟨m, hm, _⟩ := ff V A D C V' V' q r hq hr E E hp pr hD bc
    (𝟙 V') compat
  obtain ⟨n, hn, _⟩ := ff A V C D V' V' r q hr hq E E pr hp bc hD
    (𝟙 V') compat
  -- Uniqueness of descent identifies each composite with the identity.
  have mn : m ≫ n = 𝟙 V := by
    obtain ⟨l, hl, unique⟩ := ff V V D D V' V' q q hq hq E E hp hp hD hD
      (𝟙 V') compat
    apply (unique _ ?_).trans (unique _ ?_).symm
    · constructor
      · intro T a b hab z
        rw [← Category.assoc, hm.1 a b hab z, hn.1, Category.assoc]
      · simp only [Over.comp_left, Over.id_left, Category.id_comp] at hm hn ⊢
        rw [← Category.assoc, ← hm.2, ← hn.2]
    · constructor
      · intros; simp
      · simp
  have nm : n ≫ m = 𝟙 A := by
    obtain ⟨l, hl, unique⟩ := ff A A C C V' V' r r hr hr E E pr pr bc bc
      (𝟙 V') compat
    apply (unique _ ?_).trans (unique _ ?_).symm
    · constructor
      · intro T a b hab z
        rw [← Category.assoc, hn.1 a b hab z, hm.1, Category.assoc]
      · simp only [Over.comp_left, Over.id_left, Category.id_comp] at hm hn ⊢
        rw [← Category.assoc, ← hn.2, ← hm.2]
    · constructor
      · intros; simp
      · simp
  -- Transfer the canonical pullback square and its invariant projection along m.
  let i : V.left ≅ A.left :=
    ⟨m.left, n.left, congrArg (fun t ↦ t.left) mn, congrArg (fun t ↦ t.left) nm⟩
  refine ⟨W, m.left ≫ pullback.fst W.hom f, ?_, ?_⟩
  · exact (IsPullback.of_hasPullback W.hom f).of_iso' i
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [i])
      (by simpa [i, A] using Over.w m) (by simp) (by simp)
  · intro T a b hab z
    have eq := congrArg (fun t : Over.mk b ⟶ A ↦ t.left ≫ pullback.fst W.hom f)
      (hm.1 a b hab z)
    simpa [C, pullbackDatum, Category.assoc] using eq

end AlgebraicGeometry
