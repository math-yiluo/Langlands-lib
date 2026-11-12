/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U002.Definitions
import Mathlib.GroupTheory.Index

/-!
# Targets for natural multiplication on the NYLL profinite integers

Modified by Worker 120: extract eleven public theorem signatures from the pinned
NYLL ProfiniteInteger source as Prop-valued Statement definitions. Reuse the
source closure model and multiplication map; preserve all source parameters,
binder kinds and hypotheses. The source private helper and the separate
integer-reduction computation and division units are omitted. The unused-variable
lint check is disabled locally where needed to retain source premise names.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- Target for uniqueness of natural exponents of the additive generator. -/
def proCIntegerOne_pow_nat_injectiveStatement : Prop :=
  Function.Injective (fun n : ℕ =>
    (Multiplicative.ofAdd (1 : ZHat)) ^ n)

/-- Target for the evaluation of natural multiplication. -/
def zHatMulNat_applyStatement (n : ℕ) (x : ZHat) : Prop :=
  zHatMulNat n x = n • x

set_option linter.unusedVariables false in
/-- Target for injectivity of multiplication by a positive natural number. -/
def zHatMulNat_injectiveStatement {n : ℕ} (hn : 0 < n) : Prop :=
  Function.Injective (zHatMulNat n)

/-- Target for closedness of the multiplication image at any natural number. -/
def isClosed_zHatMulNat_rangeStatement (n : ℕ) : Prop :=
  IsClosed ((zHatMulNat n).toAddMonoidHom.range : Set ZHat)

/-- Target for surjectivity of every positive-modulus reduction. -/
def zHatReduction_surjectiveStatement (n : ℕ) (hn : 0 < n) : Prop :=
  Function.Surjective (zHatReduction n hn)

/-- Target for multiplication of an ordinary integer cast. -/
def zHatMulNat_intStatement (n : ℕ) (a : ℤ) : Prop :=
  zHatMulNat n ((Int.castRingHom ZHat) a) =
    (Int.castRingHom ZHat) ((n : ℤ) * a)

/-- Target identifying the multiplication image with the reduction kernel. -/
def zHatMulNat_range_eq_ker_reductionStatement (n : ℕ) (hn : 0 < n) : Prop :=
  (zHatMulNat n).toAddMonoidHom.range =
    (zHatReduction n hn).toAddMonoidHom.ker

set_option linter.unusedVariables false in
/-- Target for the additive index of a positive multiplication image. -/
def zHatMulNat_range_indexStatement (n : ℕ) (hn : 0 < n) : Prop :=
  (zHatMulNat n).toAddMonoidHom.range.index = n

set_option linter.unusedVariables false in
/-- Target classifying every additive subgroup of nonzero finite index. -/
def zHatAddSubgroup_eq_mulNat_range_of_index_ne_zeroStatement
    (H : AddSubgroup ZHat) (hH : H.index ≠ 0) : Prop :=
  H = (zHatMulNat H.index).toAddMonoidHom.range

set_option linter.unusedVariables false in
/-- Target for the classification with a specified positive index. -/
def zHatAddSubgroup_eq_mulNat_range_of_index_eqStatement
    (H : AddSubgroup ZHat) {n : ℕ} (hn : 0 < n) (hindex : H.index = n) : Prop :=
  H = (zHatMulNat n).toAddMonoidHom.range

/-- Target for the classification at a finite-quotient boundary. -/
def zHatAddSubgroup_eq_mulNat_range_of_finite_quotientStatement
    (H : AddSubgroup ZHat) [Finite (ZHat ⧸ H)] : Prop :=
  H = (zHatMulNat H.index).toAddMonoidHom.range

end
end Langlands.NYLL.ClassFormation
