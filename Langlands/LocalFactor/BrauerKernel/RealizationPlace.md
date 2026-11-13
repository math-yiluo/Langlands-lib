# The distinguished place of a global realization

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. Deligne's global argument
(1973, proof of Lemma 4.12) realizes a finite Galois extension `K / F` of p-adic fields as the
completion at a place `w` over `v` of a Galois extension `K' / k` of number fields. The published
realization statement `Langlands.Global.TotallyRealGaloisRealizationStatement` supplies `v`, `w`,
a ring isomorphism `φ : k_v ≃ F` and its continuity, but it does not say that `v` lies over the
prime `p` of `F`, and `φ` is not stated to be `ℚ_p`-linear. This unit derives both facts. They are
elementary and have no separate literature source.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`. The canonical p-adic package of a finite
place `v` of a number field (`Langlands.Global.CompletionPadic`) has residue prime
`residuePrime v` (the generator of the rational prime under `v`).

## Results

- `residuePrime_eq_of_ringEquiv`: let `K` be a number field (in any universe), `v` a finite place
  of `K`, `F : PadicField p` and `φ : K_v ≃+* F` a ring isomorphism whose inverse is continuous for
  the canonical topology of `F`. Then `residuePrime v = p`.

  Proof: in `F` the powers `p^n` tend to `0`, because the canonical norm of `p` is `p⁻¹ < 1`
  (`PadicField.canonicalNorm_prime`). Applying the continuous `φ⁻¹`, the powers of `p` tend to `0`
  in `K_v`, so the valuation of `p` in `K_v` is `< 1`. This valuation is the `v`-adic valuation of
  `p ∈ 𝓞 K` (Mathlib's `valuedAdicCompletion_eq_valuation'`; the cast of `p` into `K_v` is
  computed by induction from `adicCompletion.coe_add` and `coe_one`), so `p ∈ v`. Then `p` lies in
  the rational prime under `v`, and `natGenerator_dvd_iff` gives `residuePrime v ∣ p`. Both are
  primes, so they are equal.
- `ringHom_algebraMap_of_continuous`: let `A`, `B` be division rings that are topological
  `ℚ_p`-algebras with continuous structure maps, `B` Hausdorff. A continuous ring homomorphism
  `g : A → B` satisfies `g (algebraMap a) = algebraMap a` for all `a ∈ ℚ_p`.

  Proof: both sides are continuous in `a` and agree on rationals (ring homomorphisms between
  division rings preserve rational casts). The rationals are dense in `ℚ_p`
  (`Padic.denseRange_ratCast`), and `B` is Hausdorff.
- `algHomOfContinuous`: such a `g` as a `ℚ_p`-algebra homomorphism `A →ₐ[ℚ_p] B`, with the same
  underlying function (`algHomOfContinuous_apply`).
