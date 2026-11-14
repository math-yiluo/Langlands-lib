/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 466, 14 November 2026 UTC:
Extract only the proof of M296.011 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean
at fbd320cd8b1b06487c58227e92eb135794267709 (lines 110–117). Add the
Langlands.NYLL namespace prefix and import only the published
FiniteAbelianSubextension.Statements module. State the theorem as the
published Statement applied to the source parameters. Replace the source
proof term L.toFiniteGaloisExtension.extensionQuotientMk_apply k, which
names the finite Galois lemma M040.012, by that lemma's own source proof
rfl (FiniteGaloisSubextension.lean, line 116). Omit the @[simp] attribute.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Statements

/-!
# NYLL M296.011: the named abelian quotient projection

The named projection of a finite abelian subextension, read through its
comparison equivalence, is the ordinary quotient map.
-/

namespace Langlands.NYLL.ClassFormation

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- The named abelian quotient projection agrees with the underlying quotient map. -/
theorem extensionQuotientMk_apply (L : FiniteAbelianSubextension K)
    (k : K.toSubgroup) :
    extensionQuotientMk_applyStatement L k :=
  rfl

end FiniteAbelianSubextension

end GroupOnly

end Langlands.NYLL.ClassFormation
