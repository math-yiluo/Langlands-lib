/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 172, 13 November 2026 UTC:
Extract only M237.002, the definition valuationSubringComapMap, from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean
(lines 81-93) at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the
namespace by Langlands.NYLL. Replace the four source imports by the single
Mathlib module the definition needs. Keep the section PurelyInseparableComap,
its binders {F Omega : Type u} [Field F] [Field Omega] [Algebra F Omega],
universe u, the noncomputable section and the definition body unchanged.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# The ring map from a pulled-back valuation subring

The inclusion of the pullback `A.comap (algebraMap F Omega)` of a valuation
subring `A` of `Omega` into `A` itself, as a ring homomorphism. See the paired
Markdown for the source map and the modification record.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

/-! ## Residues under a purely inseparable ambient extension -/

section PurelyInseparableComap

variable {F Omega : Type u} [Field F] [Field Omega] [Algebra F Omega]

/-- The inclusion from the pullback of a valuation ring to the ambient
valuation ring. -/
def valuationSubringComapMap (A : ValuationSubring Omega) :
    A.comap (algebraMap F Omega) →+* A where
  toFun x := ⟨algebraMap F Omega x, x.property⟩
  map_one' := Subtype.ext (map_one (algebraMap F Omega))
  map_mul' x y := Subtype.ext (map_mul (algebraMap F Omega) (x : F) (y : F))
  map_zero' := Subtype.ext (map_zero (algebraMap F Omega))
  map_add' x y := Subtype.ext (map_add (algebraMap F Omega) (x : F) (y : F))

end PurelyInseparableComap

end
end Langlands.NYLL.LocalClassFieldTheory
