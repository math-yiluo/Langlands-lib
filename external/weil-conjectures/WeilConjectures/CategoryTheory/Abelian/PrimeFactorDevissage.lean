/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Prime-factor dévissage in an abelian category

Let `F` be an object of an abelian category killed by a positive integer `n`, and let `r` be a
prime dividing `n`. Multiplication by `r` gives the short exact sequence

`0 ⟶ F[r] ⟶ F ⟶ rF ⟶ 0`,

where `F[r] = ker (r : F ⟶ F)` is killed by `r` and `rF = im (r : F ⟶ F)` is killed by `n / r`.
By induction on `n`, a property of objects which is stable under extensions and holds for
all objects killed by a prime holds for all objects killed by a positive integer.

## Main definitions

- `CategoryTheory.Abelian.nsmulShortComplex`: the short complex `F[r] ⟶ F ⟶ rF`.

## Main statements

- `CategoryTheory.Abelian.shortExact_nsmulShortComplex`: it is short exact.
- `CategoryTheory.Abelian.nsmul_id_kernel_eq_zero`,
  `CategoryTheory.Abelian.nsmul_id_image_eq_zero`: the orders of its outer terms.
- `CategoryTheory.ObjectProperty.prop_of_nsmul_id_eq_zero`: the dévissage.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C]

namespace Abelian

/-- The short complex `F[r] ⟶ F ⟶ rF` of multiplication by `r` on `F`: the kernel of
`r • 𝟙 F`, followed by the factorisation of `r • 𝟙 F` through its image.
(blueprint: `theorem-proper-base-change-classical-pro`) -/
noncomputable def nsmulShortComplex (F : C) (r : ℕ) : ShortComplex C :=
  ShortComplex.mk (kernel.ι (r • 𝟙 F)) (Limits.factorThruImage (r • 𝟙 F))
    (by rw [← cancel_mono (Limits.image.ι (r • 𝟙 F))]; simp)

/-- The short complex `0 ⟶ F[r] ⟶ F ⟶ rF ⟶ 0` is short exact. -/
lemma shortExact_nsmulShortComplex (F : C) (r : ℕ) : (nsmulShortComplex F r).ShortExact := by
  have hS : (ShortComplex.mk (kernel.ι (r • 𝟙 F)) (r • 𝟙 F) (kernel.condition _)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  have : Mono (nsmulShortComplex F r).f := by dsimp [nsmulShortComplex]; infer_instance
  have : Epi (nsmulShortComplex F r).g := by dsimp [nsmulShortComplex]; infer_instance
  refine ⟨?_⟩
  let φ : nsmulShortComplex F r ⟶
        ShortComplex.mk (kernel.ι (r • 𝟙 F)) (r • 𝟙 F) (kernel.condition _) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Limits.image.ι (r • 𝟙 F)
      comm₂₃ := by simp [nsmulShortComplex] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS

/-- The kernel `F[r]` of multiplication by `r` is killed by `r`. -/
lemma nsmul_id_kernel_eq_zero (F : C) (r : ℕ) : r • 𝟙 (kernel (r • 𝟙 F)) = 0 :=
  (cancel_mono (kernel.ι (r • 𝟙 F))).1 (by
    rw [Preadditive.nsmul_comp, Category.id_comp, zero_comp, ← Category.comp_id (kernel.ι _),
      ← Preadditive.comp_nsmul, kernel.condition])

/-- If `F` is killed by `n` and `r ∣ n`, the image `rF` of multiplication by `r` is killed by
`n / r`. -/
lemma nsmul_id_image_eq_zero (F : C) {n r : ℕ} (hn : n • 𝟙 F = 0) (hr : r ∣ n) :
    (n / r) • 𝟙 (Limits.image (r • 𝟙 F)) = 0 := by
  refine (cancel_mono (Limits.image.ι (r • 𝟙 F))).1
    ((cancel_epi (Limits.factorThruImage (r • 𝟙 F))).1 ?_)
  rw [zero_comp, comp_zero, Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul,
    Limits.image.fac, smul_smul, Nat.div_mul_cancel hr, hn]

end Abelian

/-- **Prime-factor dévissage.** Let `P` be a property of objects of an abelian category which
is stable under extensions and holds for every object killed by a prime. Then `P` holds for
every object killed by a positive integer `n`: choosing a prime `r ∣ n`, the short exact
sequence `0 ⟶ F[r] ⟶ F ⟶ rF ⟶ 0` has `F[r]` killed by `r` and `rF` killed by `n / r < n`,
and one inducts on `n`.
(blueprint: `theorem-proper-base-change-classical-pro`) -/
theorem ObjectProperty.prop_of_nsmul_id_eq_zero (P : ObjectProperty C)
    (hext : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (hprime : ∀ r : ℕ, r.Prime → ∀ F : C, r • 𝟙 F = 0 → P F) :
    ∀ (n : ℕ), 0 < n → ∀ F : C, n • 𝟙 F = 0 → P F := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn F hF
    by_cases h1 : n = 1
    · subst h1
      exact hprime 2 Nat.prime_two F (by rw [two_nsmul, ← one_nsmul (𝟙 F), hF, add_zero])
    obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd h1
    refine hext _ (Abelian.shortExact_nsmulShortComplex F r)
      (hprime r hr _ (Abelian.nsmul_id_kernel_eq_zero F r))
      (ih (n / r) (Nat.div_lt_self hn hr.one_lt) (Nat.div_pos (Nat.le_of_dvd hn hrn) hr.pos) _
        (Abelian.nsmul_id_image_eq_zero F hF hrn))

end CategoryTheory
