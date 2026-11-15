# Greenberg ring schemes of a mixed-characteristic DVR

This file supplies the coefficient ring schemes for the mixed-characteristic case of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, Theorem A.4.19. Let `R` be a
discrete valuation ring with algebraically closed residue field `k`, with
`ringChar R ≠ ringChar k`. For every positive level `n`, it constructs a
`GreenbergMixed.GreenbergRingScheme R n` (interface in `GreenbergMixed/RingScheme.lean`)
from the Greenberg rings of `GreenbergRing.lean` attached to the congruence ring
`A = congruenceRing R n = R ⧸ 𝔪ⁿ`. As in Greenberg's construction (Greenberg, *Schemata
over local rings*, 1961; KP §A.4), the ring scheme is built from truncated Witt vectors
over `k`. The Lean presentation through cyclic Witt coordinates is internal to this
proof.

## Digit expansion

`eq_sum_iterate f d π h j a`: suppose `a - d a = π * f a` for all `a`. Then
`a = Σ_{i < j} d (f^[i] a) * π ^ i + π ^ j * f^[j] a`. The proof is by induction on `j`.

## The congruence ring

Fix a DVR `R`.

- `levelResidue R n : congruenceRing R n →+* ResidueField R`, induced by `residue R`
  (`levelResidue_mk`, `levelResidue_surjective`).
- `ker_levelResidue_pow`: `(ker levelResidue) ^ (n - 1 + 1) = ⊥`. The kernel is the image
  of `𝔪`, and `𝔪 ^ n` maps to zero.
- `exists_eq_mul_of_levelResidue_eq_zero`: for a uniformizer `ϖ` (an irreducible
  element), an element of the kernel is `[ϖ] * y`.
- `mk_pow_eq_zero`: `[a] ^ n = 0` for `a ∈ 𝔪`.
- `natCast_pow_eq_zero`: if `k` has characteristic `p`, then `p ^ n = 0` in `R ⧸ 𝔪ⁿ`.
- `exists_eq_sum_witt`: let `ψ : W(k) →+* R ⧸ 𝔪ⁿ` satisfy
  `levelResidue (ψ c) = c.coeff 0`. Every element is then `Σ_{i < n} ψ (c i) * [ϖ] ^ i`.
  Proof: apply `eq_sum_iterate` with digits `d b = ψ [levelResidue b]` (Teichmüller
  lifts) and `π = [ϖ]`. The remainder `[ϖ]^n * …` vanishes.
- `nonempty_wittDecomposition_congruenceRing`: such a `ψ` admits cyclic Witt coordinates
  (`nonempty_wittDecomposition` with the generators `[ϖ] ^ i`, `i < n`, and `p ^ n = 0`).

## The ring scheme

`greenbergRingScheme n D hψ : GreenbergMixed.GreenbergRingScheme R n`, for cyclic Witt
coordinates `D` of `R ⧸ 𝔪ⁿ` over `ψ` with `levelResidue ∘ ψ = coeff 0`, has these fields:

- `functor`: `B ↦ CommAlgCat.of R (GreenbergRing D B)`, `f ↦ gmap D R f.hom`, with functor
  laws `gmap_id`, `gmap_comp`.
- `dim`: the cardinality of `Σ i, Fin (m i)`; `coord`: `coordEquiv` composed with
  `Fintype.equivFin`; `coord_map`: `coordEquiv_gmap`.
- `levelEquiv`: `levelEquiv D R : GreenbergRing D k ≃ₐ[R] R ⧸ 𝔪ⁿ`.
- `red`: `red D B levelResidue hψ`. `red_coord` holds with coefficients
  `if j = 0 then levelResidue (e i) else 0`, from `red_eq_sum`. `red_algebraMap` comes from
  `red_algebraMap` and `levelResidue_mk`.
- `ker_red_nilpotent`: `ker_red_pow` with `N = n - 1`.
- `ker_map_nilpotent`: for `I ^ 2 = ⊥`, the quotient map `B → B ⧸ I` has square-zero
  kernel, and `ker_gmap_pow` applies.

## Main theorem

`nonempty_greenbergRingScheme (R) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
[IsAlgClosed (ResidueField R)] (hchar : ringChar R ≠ ringChar (ResidueField R)) (n : ℕ+) :
Nonempty (GreenbergMixed.GreenbergRingScheme R n)`.

This is exactly the body of `GreenbergMixed.GreenbergRingSchemeExistence`.

Proof:

1. Let `p = ringChar k`. If `p = 0`, then `k` has characteristic zero, so `R` does too
   (`RingHom.charZero` along `residue R`). Then `ringChar R = 0 = p`, which contradicts
   `hchar`. Hence `p` is prime.
2. `k` is perfect, since it is algebraically closed.
3. `ψ := wittToLocal p levelResidue … (ker_levelResidue_pow R n)`, with
   `levelResidue ∘ ψ = coeff 0` (`residue_wittToLocal`).
4. Cyclic Witt coordinates come from `nonempty_wittDecomposition_congruenceRing`, and the
   ring scheme is `greenbergRingScheme`.

The hypothesis `hchar` is used only to make `ringChar k` positive.
