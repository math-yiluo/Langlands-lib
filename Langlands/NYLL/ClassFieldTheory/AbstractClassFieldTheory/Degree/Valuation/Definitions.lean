/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Definitions
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Natural-multiple images and value-group reduction

Modified by Worker 192: extract M025.002–004 and M025.007–008 from the
pinned NYLL source, prefix the namespace with `Langlands.NYLL`, and replace
the unused full degree/norm imports by the published profinite-integer data
and Mathlib quotient infrastructure. The five construction bodies are retained.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- Multiplication by `n` on an additive subgroup. -/
def nsmulOnAddSubgroup (Z : AddSubgroup ZHat) (n : ℕ) : Z →+ Z where
  toFun z := ⟨n • z.1, Z.nsmul_mem z.2 n⟩
  map_zero' := Subtype.ext (nsmul_zero n)
  map_add' x y := Subtype.ext (smul_add n x.1 y.1)

/-- The subgroup `nZ` inside a value group `Z`. -/
def nsmulWithin (Z : AddSubgroup ZHat) (n : ℕ) : AddSubgroup Z :=
  (nsmulOnAddSubgroup Z n).range

/-- The ambient subgroup `nZ ⊆ ℤ̂`. -/
def nsmulImage (Z : AddSubgroup ZHat) (n : ℕ) : AddSubgroup ZHat :=
  Z.map
    { toFun := fun z : ZHat => n • z
      map_zero' := nsmul_zero n
      map_add' := fun x y => nsmul_add x y n }

/-- Restriction of reduction modulo `n` along the inclusion `Z ≤ ℤ̂`. -/
def valueGroupReduction (Z : AddSubgroup ZHat) (n : ℕ) (hn : 0 < n) :
    Z →+ ZMod n :=
  (zHatReduction n hn).toAddMonoidHom.comp Z.subtype

/-- The canonical map `Z/nZ → ℤ/nℤ` induced by the inclusion `Z ≤ ℤ̂`
and reduction modulo `n`.

This is the specific map required in the valuation-quotient axiom, rather than an
arbitrarily chosen abstract equivalence between the two quotients. -/
def canonicalValueQuotientMap (Z : AddSubgroup ZHat)
    (n : ℕ) (hn : 0 < n) : (Z ⧸ nsmulWithin Z n) →+ ZMod n :=
  QuotientAddGroup.lift (nsmulWithin Z n) (valueGroupReduction Z n hn) (by
    rintro _ ⟨z, rfl⟩
    change zHatReduction n hn (n • (z : ZHat)) = 0
    rw [map_nsmul]
    simp [nsmul_eq_mul])

end

end Langlands.NYLL.ClassFormation
