/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 60, 13 November 2026 UTC:
Extract only the proof of M077.033 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean
at fbd320cd8b1b06487c58227e92eb135794267709 (lines 707–750). Add the
Langlands.NYLL namespace prefix and import only the published DiagramChase
Statements module. State the theorem as the published Statement applied to
the source parameters, and insert a `show` step exposing
`Function.Bijective r` before the original proof. The source's call to the
unpublished M077.032 theorem is replaced by a call to the private local
lemma `surjective_of_exact_diagram_aux`, whose statement and proof are the
original M077.032 type and proof (lines 670–702) under that non-conflicting
name. Omit the source imports, opens, noncomputable section, universe,
section variables and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction.DiagramChase.Statements

/-!
# Bijectivity of the middle reciprocity arrow from an exact diagram

The diagram chase in the third reduction of the abstract reciprocity theorem:
with both rows exact, the top-right arrow surjective and the bottom-left arrow
injective, the middle vertical arrow is bijective when both outside vertical
arrows are.
-/

namespace Langlands.NYLL.ClassFormation

/-- Local copy of the M077.032 diagram chase (original lines 670–702), kept
private under a non-conflicting name: the middle vertical arrow is surjective
when the two outside vertical arrows are surjective, the top-right arrow is
surjective, and the bottom row is exact. -/
private theorem surjective_of_exact_diagram_aux
    {Q₀ Q Q₁ B₀ B B₁ : Type*}
    [AddGroup Q₀] [AddGroup Q] [AddGroup Q₁]
    [AddGroup B₀] [AddGroup B] [AddGroup B₁]
    (iQ : Q₀ →+ Q) (pQ : Q →+ Q₁)
    (iB : B₀ →+ B) (pB : B →+ B₁)
    (r₀ : Q₀ →+ B₀) (r : Q →+ B) (r₁ : Q₁ →+ B₁)
    (hexact : Function.Exact iB pB)
    (hpQ : Function.Surjective pQ)
    (hleft : ∀ q, r (iQ q) = iB (r₀ q))
    (hright : ∀ q, pB (r q) = r₁ (pQ q))
    (hr₀ : Function.Surjective r₀)
    (hr₁ : Function.Surjective r₁) :
    Function.Surjective r := by
  intro b
  obtain ⟨q₁, hq₁⟩ := hr₁ (pB b)
  obtain ⟨q, hq⟩ := hpQ q₁
  have hzero : pB (b - r q) = 0 := by
    calc
      pB (b - r q) = pB b - pB (r q) := map_sub pB b (r q)
      _ = pB b - r₁ (pQ q) := by rw [hright q]
      _ = pB b - r₁ q₁ := by rw [hq]
      _ = pB b - pB b := by rw [hq₁]
      _ = 0 := sub_self _
  obtain ⟨b₀, hb₀⟩ := (hexact (b - r q)).mp hzero
  obtain ⟨q₀, hq₀⟩ := hr₀ b₀
  refine ⟨iQ q₀ + q, ?_⟩
  calc
    r (iQ q₀ + q) = r (iQ q₀) + r q := map_add r _ _
    _ = iB (r₀ q₀) + r q := by rw [hleft q₀]
    _ = iB b₀ + r q := by rw [hq₀]
    _ = (b - r q) + r q := by rw [hb₀]
    _ = b := sub_add_cancel b (r q)

/-- The diagram chase in the third reduction.  If both outside
reciprocity arrows are bijective and the first lower arrow is injective,
then the middle reciprocity arrow is bijective. -/
theorem abstractReciprocity_bijective_of_exact_diagram
    {Q₀ Q Q₁ B₀ B B₁ : Type*}
    [AddGroup Q₀] [AddGroup Q] [AddGroup Q₁]
    [AddGroup B₀] [AddGroup B] [AddGroup B₁]
    (iQ : Q₀ →+ Q) (pQ : Q →+ Q₁)
    (iB : B₀ →+ B) (pB : B →+ B₁)
    (r₀ : Q₀ →+ B₀) (r : Q →+ B) (r₁ : Q₁ →+ B₁)
    (hexactQ : Function.Exact iQ pQ)
    (hexactB : Function.Exact iB pB)
    (hpQ : Function.Surjective pQ)
    (hiB : Function.Injective iB)
    (hleft : ∀ q, r (iQ q) = iB (r₀ q))
    (hright : ∀ q, pB (r q) = r₁ (pQ q))
    (hr₀ : Function.Bijective r₀)
    (hr₁ : Function.Bijective r₁) :
    abstractReciprocity_bijective_of_exact_diagramStatement
      iQ pQ iB pB r₀ r r₁ hexactQ hexactB hpQ hiB hleft hright hr₀ hr₁ := by
  show Function.Bijective r
  refine ⟨?_, surjective_of_exact_diagram_aux
    iQ pQ iB pB r₀ r r₁ hexactB hpQ hleft hright hr₀.2 hr₁.2⟩
  rw [injective_iff_map_eq_zero]
  intro q hq
  have hpzero : pB (r q) = 0 := by rw [hq, map_zero]
  have hr₁zero : r₁ (pQ q) = 0 := by
    rw [← hright q]
    exact hpzero
  have hpQzero : pQ q = 0 := by
    apply hr₁.1
    simpa using hr₁zero
  obtain ⟨q₀, hq₀⟩ := (hexactQ q).mp hpQzero
  have hiBzero : iB (r₀ q₀) = 0 := by
    calc
      iB (r₀ q₀) = r (iQ q₀) := (hleft q₀).symm
      _ = r q := by rw [hq₀]
      _ = 0 := hq
  have hr₀zero : r₀ q₀ = 0 := by
    apply hiB
    simpa using hiBzero
  have hq₀zero : q₀ = 0 := by
    apply hr₀.1
    simpa using hr₀zero
  rw [← hq₀, hq₀zero, map_zero]

end Langlands.NYLL.ClassFormation
