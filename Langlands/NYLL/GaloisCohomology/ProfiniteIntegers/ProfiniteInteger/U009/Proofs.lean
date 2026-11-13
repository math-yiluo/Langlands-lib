/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 105, 13 November 2026:
Extract the theorem of M009.009 from
Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and give the theorem the published statement
zHatMulNat_intStatement n a as its type, keeping the explicit n : ℕ and
a : ℤ. Replace the original proof, which uses ZHat.ext and modular
arithmetic, by a direct proof from the body of zHatMulNat and the
ring-homomorphism laws of Int.castRingHom. Omit the simp attribute, the
noncomputable section and all other source declarations. Import only
the published ProfiniteInteger Statements module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements

/-!
# Natural multiplication of integer casts in the profinite integers

Multiplication by a natural number `n` sends the image of an integer `a`
in `ZHat` to the image of `n * a`.
-/

namespace Langlands.NYLL.ClassFormation

/--
Establishes the identity `zHatMulNat n ((Int.castRingHom ZHat) a) = (Int.castRingHom ZHat) ((n :
ℤ) * a)`.
-/
theorem zHatMulNat_int (n : ℕ) (a : ℤ) : zHatMulNat_intStatement n a := by
  change n • (Int.castRingHom ZHat) a = (Int.castRingHom ZHat) ((n : ℤ) * a)
  rw [map_mul, map_natCast, nsmul_eq_mul]

end Langlands.NYLL.ClassFormation
