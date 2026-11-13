/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 60, 13 November 2026 UTC:
Extract only the proof of M077.032 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean
at fbd320cd8b1b06487c58227e92eb135794267709 (lines 670–706). Add the
Langlands.NYLL namespace prefix and import only the published DiagramChase
Statements module. State the theorem as the published Statement applied to
the source parameters, and insert a `show` step exposing
`Function.Surjective r` before the original proof, which is otherwise
unchanged. Omit the source imports, opens, noncomputable section, universe,
section variables and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction.DiagramChase.Statements

/-!
# Surjectivity of the middle reciprocity arrow from an exact diagram

The diagram chase used twice in the first reduction of the abstract reciprocity
theorem: the middle vertical arrow of a commutative diagram with exact bottom row
is surjective when both outside vertical arrows and the top-right arrow are.
-/

namespace Langlands.NYLL.ClassFormation

/-- The diagram chase used twice in the first reduction.  The
middle vertical arrow is surjective when the two outside vertical arrows
are surjective, the top-right arrow is surjective, and the bottom row is
exact. -/
theorem abstractReciprocity_surjective_of_exact_diagram
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
    abstractReciprocity_surjective_of_exact_diagramStatement
      iQ pQ iB pB r₀ r r₁ hexact hpQ hleft hright hr₀ hr₁ := by
  show Function.Surjective r
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

end Langlands.NYLL.ClassFormation
