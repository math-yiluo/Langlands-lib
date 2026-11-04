# A height inequality for special fibres of flat families

Worker 1382.

This helper module is pure commutative algebra. It feeds the specialization step in the
maximality part of the proof of `Langlands.GroupScheme.BorelAlgClosedFieldExtensionStatement`
(module `BorelFieldExtensionDescent`, lemma `exists_isPrime_lt_specMap`). All declarations
are in the namespace `Langlands.GroupScheme.BorelFieldExtension`.

Provenance: these are internal helper lemmas. They are not transcriptions of a literature
result. The argument is the standard combination of the dimension inequality for fibres
with going down for flat extensions. Both inputs are taken from Mathlib.

## Declarations

- `height_add_one_le_of_strictMono`: let `α` and `β` be preorders, where `β` has a bottom
  element. Let `f : α → β` be strictly monotone with `⊥ < f y` for every `y`. Then
  `Order.height x + 1 ≤ Order.height (f x)` for every `x`.
- `height_map_quotient_add_one_le`: let `Q < P ≤ M` be ideals of a commutative ring `D`,
  where `Q` and `M` are prime. Then the height of the image of `M` in `D ⧸ P`, plus one,
  is at most the height of the image of `M` in `D ⧸ Q`. The primality of both images is
  a hypothesis given as instance arguments.
- `exists_isPrime_lt_of_flat`: let `A` be a Noetherian ring and `D` a Noetherian
  `A`-algebra. Let `𝔪` be a prime of `A`, and let `Q < P ≤ M` be ideals of `D`, where `Q`
  and `M` are prime. Assume `M` lies over `𝔪` (`M.comap (algebraMap A D) = 𝔪`) and
  `D ⧸ P` is flat over `A`. Then there is a prime `q` of `D` with
  `Q ⊔ 𝔪.map (algebraMap A D) ≤ q` and `q < M`. In other words, `M` is not a minimal
  prime over `Q + 𝔪D`.

## Proofs

`height_add_one_le_of_strictMono`. Extend `f` to `g : WithBot α → β` by sending `⊥` to `⊥`.
The hypothesis `⊥ < f y` makes `g` strictly monotone. Then
`Order.height_le_height_apply_of_strictMono` gives
`Order.height (x : WithBot α) ≤ Order.height (f x)`. Finally,
`Order.height_coe_withBot` identifies the left side with `Order.height x + 1`.

`height_map_quotient_add_one_le`. The factor map `D ⧸ Q → D ⧸ P` is surjective, so
pulling back primes is strictly monotone on prime spectra
(`RingHom.strictMono_comap_of_surjective`). It sends the image of `M` in `D ⧸ P` to the
image of `M` in `D ⧸ Q`; this is checked elementwise using `P ≤ M`. Every pulled-back prime
strictly contains the zero ideal of `D ⧸ Q`. Indeed, it contains the class of an element
`p ∈ P \ Q`, and that class is nonzero. The previous lemma, together with
`PrimeSpectrum.height_eq_orderHeight`, gives the claim.

`exists_isPrime_lt_of_flat`. Suppose, for a contradiction, that no such `q` exists. Let
`M̄` be the image of `M` in `D ⧸ Q`. It is prime and lies over `𝔪`.

1. Mathlib's relative form of Krull's height theorem,
   `Ideal.height_le_height_add_of_liesOver`, bounds `ht M̄` by `ht 𝔪` plus the height of
   the image of `M̄` in the fibre `(D ⧸ Q) ⧸ 𝔪 (D ⧸ Q)`.
2. That fibre height is zero. A prime `J` of the fibre below the image of `M̄` pulls back
   to a prime `q` of `D` with `Q ⊔ 𝔪D ≤ q ≤ M`. By assumption `q = M`, so `J` contains
   the image of `M̄`. Hence that image is a minimal prime (`Ideal.height_eq_zero_iff`),
   and `ht M̄ ≤ ht 𝔪`.
3. The image of `M` in `D ⧸ P` lies over `𝔪`, and `D ⧸ P` is flat over `A`, hence has
   going down. So `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` gives
   `ht 𝔪 ≤ ht (M ⧸ P)`.
4. `height_map_quotient_add_one_le` gives `ht (M ⧸ P) + 1 ≤ ht M̄`.

Together these give `ht 𝔪 + 1 ≤ ht 𝔪`. This is impossible because `ht 𝔪` is finite: `A` is
Noetherian (`Ideal.height_ne_top_of_isPrime`).
