/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Definitions
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration.Definitions

/-!
# Targets for the NYLL profinite-integer core

Modified by Worker 120: extract M008.019–024 signatures from the pinned
NYLL source as Prop-valued Statement definitions. Preserve the source parameter
order, binder kinds and Type-zero model. Reuse the source model and the published
topological-generation predicate. Omit theorem-only simp/ext attributes.
The extensionality hypothesis is retained with its original name; only its
unused-variable lint check is disabled for that declaration.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

/-- Target for reduction of an ordinary integer cast. -/
def zHatReduction_intCastStatement (n : ℕ) (hn : 0 < n) (a : ℤ) : Prop :=
  zHatReduction n hn (a : ZHat) = (a : ZMod n)

/-- Target for reduction of the ring element one at any positive modulus. -/
def zHatReduction_oneStatement (n : ℕ) (hn : 0 < n) : Prop :=
  zHatReduction n hn (1 : ZHat) = 1

namespace ZHat

set_option linter.unusedVariables false in
/-- Target for determination by all positive-modulus reductions. -/
def extStatement {x y : ZHat}
    (h : ∀ n (hn : 0 < n), zHatReduction n hn x = zHatReduction n hn y) : Prop :=
  x = y

end ZHat

/-- Target for compatibility of reduction along divisibility. -/
def zHatReduction_transitionStatement {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n) (x : ZHat) : Prop :=
  ZMod.castHom hmn (ZMod m) (zHatReduction n hn x) =
    zHatReduction m hm x

/-- Target for density of the ordinary integer cast. -/
def denseRange_intCast_zHatStatement : Prop :=
  DenseRange (Int.castRingHom ZHat)

/-- Target for topological generation of the additive group by one. -/
def zHatOne_topologicallyGeneratesStatement : Prop :=
  TopologicallyGenerates
    (G := Multiplicative ZHat)
    ({Multiplicative.ofAdd (1 : ZHat)} : Set (Multiplicative ZHat))

end Langlands.NYLL.ClassFormation
