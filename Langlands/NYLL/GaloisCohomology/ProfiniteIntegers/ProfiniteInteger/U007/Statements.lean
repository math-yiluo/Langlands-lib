/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Statements

/-!
# Target for the reduction of an integer cast in the NYLL profinite integers

Modified by Worker 5454: the M009.007 theorem `ClassFormation.zHatReduction_int`
of the pinned NYLL
`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean` (lines 110–116)
asserts, for every `n`, `hn`, `a`, a proposition definitionally equal to the
published M008.019 target
`Langlands.NYLL.ClassFormation.zHatReduction_intCastStatement n hn a`
(`Int.castRingHom ZHat a` unfolds to the cast `(a : ZHat)`). The unit is
therefore discharged by reusing that published target. The required name
`zHatReduction_intStatement` is kept only as a reducible alias of it, with the
source parameters `n`, `hn`, `a` in source order. The proof `rfl` and the
`@[simp]` attribute are omitted. The import is the published M008 Statements
module. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

/-- Target for the identity
`zHatReduction n hn ((Int.castRingHom ZHat) a) = (a : ZMod n)`. This is the
published target `zHatReduction_intCastStatement n hn a`, reused by name: the two
casts of `a` into `ZHat` are definitionally equal. -/
abbrev zHatReduction_intStatement (n : ℕ) (hn : 0 < n) (a : ℤ) : Prop :=
  zHatReduction_intCastStatement n hn a

end Langlands.NYLL.ClassFormation
