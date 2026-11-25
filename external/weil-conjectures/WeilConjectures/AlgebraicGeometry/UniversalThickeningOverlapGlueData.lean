/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
public import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.AlgebraicGeometry.UniversalThickeningPairwiseOverlaps
import WeilConjectures.AlgebraicGeometry.UniversalThickeningOverlapCocycle

/-!
# Overlap glue data for universal first order thickenings

Source: Stacks Project, More on Morphisms, Tag 04F3, the overlap construction
in the proof of Lemma 37.7.1.
(blueprint: lem-weil-pbc-universal-thickening-overlap-glue-data)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Universal thickenings of open charts admit compatible overlap glue data.
This only constructs local overlaps and transitions, not a glued scheme.

Source: Stacks Project, More on Morphisms, Tag 04F3, proof of Lemma 37.7.1,
paragraphs beginning "Choose an affine open covering" and "By the general remarks".
(blueprint: lem-weil-pbc-universal-thickening-overlap-glue-data)

Proof: The square-zero kernel of each thickening has full support, so the
closed immersion is a homeomorphism. For each ordered pair of charts, take the
unique open in the first thickened chart whose inverse image is the source
intersection. Apply the open-pieces theorem over the whole base to obtain a
universal thickening of this intersection. Identify the sources of the two
restricted thickenings by the pullback symmetry. Universal uniqueness gives
an isomorphism between them, over the base and fixing the source intersection.
Its base compatibility is the first displayed equality, and its compatibility
with the source supplies the morphisms s and both displayed factorizations.
For three charts, restrict to the common intersection. The composites of the
transition maps and the direct transition extend the same source map over X;
universal uniqueness equates them. This gives the maps t prime, their
factorization identity, and the cocycle required by Scheme.GlueData. On repeated
indices uniqueness gives identity transitions and isomorphic diagonal opens.
Use these opens and maps as V, f, t, and t prime of the glue datum, with U equal
to the given thickened charts. The equivalence a and isomorphisms b can therefore
be identities; allowing them permits any equivalent presentation of the data.
The last equivalence is exactly the inverse-image identity defining the overlap
open. If the index type is empty, take empty glue data; every condition is
vacuous. Repeated charts use the same uniqueness argument and need no exclusion. -/
theorem universalFirstOrderThickening_overlapGlueData
    {Z X : Scheme.{u}} (h : Z ⟶ X) (C : Z.OpenCover.{u})
    (Z' : C.I₀ → Scheme.{u}) (i : ∀ k, C.X k ⟶ Z' k)
    (h' : ∀ k, Z' k ⟶ X)
    (H : ∀ k, IsUniversalFirstOrderThickening (C.f k ≫ h) (i k) (h' k)) :
    ∃ (D : Scheme.GlueData.{u}) (a : C.I₀ ≃ D.J)
      (b : ∀ k, Z' k ≅ D.U (a k)),
      (∀ k l, D.f (a k) (a l) ≫ (b k).inv ≫ h' k =
        D.t (a k) (a l) ≫ D.f (a l) (a k) ≫ (b l).inv ≫ h' l) ∧
      (∀ k l, ∃ s : pullback (C.f k) (C.f l) ⟶ D.V (a k, a l),
        s ≫ D.f (a k) (a l) = pullback.fst _ _ ≫ i k ≫ (b k).hom ∧
        s ≫ D.t (a k) (a l) ≫ D.f (a l) (a k) =
          pullback.snd _ _ ≫ i l ≫ (b l).hom) ∧
      ∀ k l (z : C.X l),
        (b l).hom (i l z) ∈ Set.range (D.f (a l) (a k)) ↔
          C.f l z ∈ Set.range (C.f k) := by
  classical
  obtain ⟨V, f, s, hf, hfdiag, Hs, hsf, hrange⟩ :=
    universalFirstOrderThickening_pairwiseOverlaps h C Z' i h' H
  have lift (k l : C.I₀) : ∃! t : V (k, l) ⟶ V (l, k),
      t ≫ (f l k ≫ h' l) = f k l ≫ h' k ∧
        s k l ≫ t = (pullbackSymmetry (C.f k) (C.f l)).hom ≫ s l k := by
    apply (Hs l k).2.2 (s k l) (f k l ≫ h' k)
      (pullbackSymmetry (C.f k) (C.f l)).hom (Hs k l).1
    rw [(Hs k l).2.1]
    simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst]
    rw [pullback.condition]
  let t : ∀ k l, V (k, l) ⟶ V (l, k) := fun k l ↦ (lift k l).exists.choose
  have ht (k l : C.I₀) := (lift k l).exists.choose_spec
  have htbase (k l : C.I₀) : t k l ≫ f l k ≫ h' l = f k l ≫ h' k := (ht k l).1
  have htsource (k l : C.I₀) :
      s k l ≫ t k l = (pullbackSymmetry (C.f k) (C.f l)).hom ≫ s l k := (ht k l).2
  have ht_id (k : C.I₀) : t k k = 𝟙 _ := by
    apply (lift k k).unique
    · exact ht k k
    · simp only [Category.id_comp, Category.comp_id,
        pullbackSymmetry_hom_of_mono_eq, and_self]
  obtain ⟨t', ht_fac, ht_cocycle⟩ :=
    universalFirstOrderThickening_overlapCocycle h C Z' i h' V f s hf Hs hsf hrange
      t htbase htsource
  have (k l : C.I₀) : IsOpenImmersion (f k l) := hf k l
  let D : Scheme.GlueData.{u} :=
    { J := C.I₀
      U := Z'
      V := V
      f := f
      f_id := hfdiag
      t := t
      t_id := ht_id
      t' := t'
      t_fac := ht_fac
      cocycle := ht_cocycle
      f_open := hf }
  refine ⟨D, Equiv.refl _, fun k ↦ Iso.refl _, ?_, ?_, ?_⟩
  · intro k l
    change f k l ≫ 𝟙 _ ≫ h' k = t k l ≫ f l k ≫ 𝟙 _ ≫ h' l
    simpa only [Category.id_comp] using (htbase k l).symm
  · intro k l
    refine ⟨s k l, ?_, ?_⟩
    · change s k l ≫ f k l = pullback.fst _ _ ≫ i k ≫ 𝟙 _
      simpa only [Category.comp_id] using hsf k l
    · change s k l ≫ t k l ≫ f l k ≫ 𝟙 _ = pullback.snd _ _ ≫ i l ≫ 𝟙 _
      simp only [Category.comp_id, ← Category.assoc, htsource]
      rw [Category.assoc, hsf]
      simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst]
  · intro k l z
    exact hrange l k z

end AlgebraicGeometry
