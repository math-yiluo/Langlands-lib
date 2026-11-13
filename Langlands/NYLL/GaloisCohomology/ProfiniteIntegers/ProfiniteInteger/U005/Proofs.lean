/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 79, 13 November 2026 UTC:
Extract the proof of M009.005 and the private helper M009.004 from
Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published ProfiniteInteger
Statements module. The helper keeps its source telescope and body under
the stable port-internal name Langlands.NYLL.PortInternal.M009.d004.
The main theorem proves the published proposition
zHatMulNat_injectiveStatement and keeps the source body, except that
ZHat.ext (M008.021) and zHatReduction_transition (M008.022), whose proofs
are not yet in the Library, are replaced by two private lemmas proved here
from the published closure model, and the simp step using
zHatMulNat_apply (M009.003) is replaced by rewriting with map_nsmul and
the definitional evaluation of zHatMulNat. The original LICENSE and
NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements

/-!
# Injectivity of multiplication by a positive natural number on `ℤ̂`

The exact proof of the published proposition M009.005: for `0 < n`, the
continuous additive map `zHatMulNat n : x ↦ n • x` on the NYLL closure model
`ZHat` is injective. See the paired Markdown.
-/

namespace Langlands.NYLL.PortInternal.M009

/-- Source M009.004 (private `zmod_cast_eq_of_nsmul_eq`): if `n • a = n • b`
in `ZMod (n * m)` with `0 < n`, then `a` and `b` have equal images in
`ZMod m`. -/
theorem d004
    {n m : ℕ} (hn : 0 < n) {a b : ZMod (n * m)}
    (h : n • a = n • b) :
    ZMod.castHom (show m ∣ n * m from ⟨n, by simp [Nat.mul_comm]⟩) (ZMod m) a =
      ZMod.castHom (show m ∣ n * m from ⟨n, by simp [Nat.mul_comm]⟩) (ZMod m) b := by
  rcases ZMod.intCast_surjective a with ⟨a, rfl⟩
  rcases ZMod.intCast_surjective b with ⟨b, rfl⟩
  rw [ZMod.castHom_apply, ZMod.castHom_apply]
  rw [ZMod.cast_intCast
      (R := ZMod m) (n := n * m) (m := m)
      (show m ∣ n * m from ⟨n, by simp [Nat.mul_comm]⟩) a,
    ZMod.cast_intCast
      (R := ZMod m) (n := n * m) (m := m)
      (show m ∣ n * m from ⟨n, by simp [Nat.mul_comm]⟩) b]
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hzero : (n • ((a - b : ℤ) : ZMod (n * m))) = 0 := by
    rw [Int.cast_sub, nsmul_sub, h, sub_self]
  have hdiv : ((n * m : ℕ) : ℤ) ∣ (n : ℤ) * (a - b) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa [nsmul_eq_mul, Int.cast_natCast, Int.cast_mul] using hzero
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  apply (mul_dvd_mul_iff_left hn0).mp
  simpa [Nat.cast_mul] using hdiv

end Langlands.NYLL.PortInternal.M009

namespace Langlands.NYLL.ClassFormation

open PortInternal.M008

noncomputable section

/-- Local replacement for the unpublished M008.021 `ZHat.ext`: an element of
the closure model is determined by its reductions at all positive moduli. -/
private theorem zHat_ext_of_reductions {x y : ZHat}
    (h : ∀ n (hn : 0 < n), zHatReduction n hn x = zHatReduction n hn y) :
    x = y := by
  change (show d007 from x) = (show d007 from y)
  apply Subtype.ext
  funext i
  exact h i.modulus i.positive

/-- Local replacement for the unpublished M008.022 `zHatReduction_transition`:
reductions of a closure-model element are compatible along divisibility. -/
private theorem zHatReduction_transition_of_closure {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n) (x : ZHat) :
    ZMod.castHom hmn (ZMod m) (zHatReduction n hn x) =
      zHatReduction m hm x := by
  let S : Set d004 :=
    {f | ZMod.castHom hmn (ZMod m) (f (d003 n hn)) = f (d003 m hm)}
  have hclosed : IsClosed S :=
    isClosed_eq
      ((continuous_of_discreteTopology (f := ZMod.castHom hmn (ZMod m))).comp
        (continuous_apply (d003 n hn)))
      (continuous_apply (d003 m hm))
  have hsub : (d006 : Set d004) ⊆ S := by
    rintro f ⟨a, rfl⟩
    exact map_intCast (ZMod.castHom hmn (ZMod m)) a
  exact closure_minimal hsub hclosed (show d007 from x).2

/-- Multiplication by a positive integer is injective on `ℤ̂`. -/
theorem zHatMulNat_injective {n : ℕ} (hn : 0 < n) :
    zHatMulNat_injectiveStatement hn := by
  show Function.Injective (zHatMulNat n)
  intro x y hxy
  apply zHat_ext_of_reductions
  intro m hm
  have hnm : 0 < n * m := Nat.mul_pos hn hm
  have hdiv : m ∣ n * m := ⟨n, by simp [Nat.mul_comm]⟩
  have hj : n • zHatReduction (n * m) hnm x =
      n • zHatReduction (n * m) hnm y := by
    rw [← map_nsmul, ← map_nsmul]
    exact congrArg (fun z : ZHat => zHatReduction (n * m) hnm z) hxy
  rw [← zHatReduction_transition_of_closure hm hnm hdiv x,
    ← zHatReduction_transition_of_closure hm hnm hdiv y]
  exact PortInternal.M009.d004 hn hj

end
end Langlands.NYLL.ClassFormation
