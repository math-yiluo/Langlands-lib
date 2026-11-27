# Proof of `InversePoleJetSqueezeStatement`

Module: `Langlands.Representation.Archimedean.InversePoleJetSqueezeProof`.

Main theorem: `Langlands.Archimedean.inversePoleJetSqueeze :
Langlands.Archimedean.InversePoleJetSqueezeStatement.{uR, uA, uU, uW}`. It keeps the four
independent universes of the statement, an arbitrary commutative ring `R` and `R`-algebra
`𝔄`, and the hypotheses exactly as stated: `1 ≤ k`, `IsSMulRegular U s`,
`IsSMulRegular W s`, an `𝔄`-linear `I : U → W`, an `R`-linear `J : W → U`,
`J (I u) = s ^ k • u` and `I (J w) = s ^ k • w`. The helper lemmas are in the namespace
`Langlands.Archimedean.JetSqueeze`; each takes only the hypotheses it uses.

## What is proved

The statement, its definitions and their relation to Bernstein–Krötz are described on the
page of `Langlands.Representation.Archimedean.InversePoleJetSqueeze`. Write `[u]_j` for the
class of `u : U` in `U_j = U ⧸ s ^ j U`, `I_j = jetMap s j I` and
`A = squeezeDomain s k I`. The theorem proves all twelve conjuncts of the statement:

1. `A` is the preimage of `ker I_k` under `jetProj : U_(2k) → U_k`
   (`squeezeDomain_eq_comap`);
2. `squeezeMap s k I` is surjective (`squeezeMap_surjective`);
3. its kernel, mapped into `U_(2k)`, is `squeezeKernel s k I` (`map_ker_squeezeMap`);
4. `squeezeKernel s k I ≤ s ^ k U / s ^ (2k) U` (`squeezeKernel_le_jetSub`) and
   `s ^ k U / s ^ (2k) U ≤ A` (`jetSub_le_squeezeDomain`);
5. `jetMulToSub 𝔄 U s k` is bijective (`jetMulToSub_bijective`);
6. `rangeToSubquotient s k I` is bijective (`rangeToSubquotient_bijective`);
7. `squeezeQuotientMap s k I` is bijective (`squeezeQuotientMap_bijective`), and so is
   `jetMulToSub 𝔄 W s k` (`jetMulToSub_bijective` for `W`);
8. `jetRaise 𝔄 W s k` is injective (`jetRaise_injective`), hence so is its restriction
   `rangeRaise s k I`, and the image of `range I_1` under `jetRaise 𝔄 W s k` is
   `I_k (s ^ (k - 1) U / s ^ k U)` (`map_range_jetRaise`).

## Basic lemmas

- `mem_powerImage`: `u ∈ s ^ j U` if and only if `u = s ^ j • v` for some `v`.
- `powerImage_antitone`: `s ^ l U ≤ s ^ j U` for `j ≤ l`.
- `mk_mem_jetSub`: for `j ≤ l`, `[u]_l ∈ s ^ j U / s ^ l U` if and only if `u ∈ s ^ j U`.
  If `[u]_l = [v]_l` with `v ∈ s ^ j U`, then `v - u ∈ s ^ l U ≤ s ^ j U`, so `u ∈ s ^ j U`.
- `eq_smul_of_pow_smul_eq`: if `s` is regular on `U` and `s ^ m • u = s ^ (m + n) • v`, then
  `u = s ^ n • v`, by injectivity of multiplication by `s ^ m` (`IsSMulRegular.pow`).
- `jetMul_injective`: if `s` is regular on `U`, multiplication by `s ^ m` from `U_j` to
  `U_(m + j)` is injective. If `s ^ m • u = s ^ (m + j) • v`, then `u = s ^ j • v` by the
  previous lemma, so `[u]_j = 0`.

## Clauses that do not use `J`

- **Clause 1.** `mk_mem_squeezeDomain`: `[u]_(2k) ∈ A` if and only if `I u ∈ s ^ k W`, by
  `mk_mem_jetSub` for `W` applied to `I_(2k) [u]_(2k) = [I u]_(2k)`. On the other side,
  `I_k (jetProj [u]_(2k)) = [I u]_k`, which vanishes if and only if `I u ∈ s ^ k W`. The two
  submodules therefore have the same elements. This clause does not use `J` or regularity.
- **Clause 4.** An element of `squeezeKernel s k I` is `[s ^ k • u]_(2k)`, which lies in
  `s ^ k U / s ^ (2k) U` (the Library lemma `jetMul_mem_jetSub`). For `[s ^ k • v]_(2k)`,
  `I (s ^ k • v) = s ^ k • I v ∈ s ^ k W`, so it lies in `A` by `mk_mem_squeezeDomain`.
- **Clause 5 and the second half of clause 7.** `jetMulToSub` is `jetMul` with its codomain
  restricted. It is injective by `jetMul_injective` with `m = j = k`, and surjective because
  every element of `s ^ k U / s ^ (2k) U` has the form `[s ^ k • v]_(2k)`, the image of
  `[v]_k`. Regularity of `s` on `W` gives the same for `W`.
- **Clause 8.** `jetRaise_injective` is `jetMul_injective` with `m = k - 1`, `j = 1`, where
  `k - 1 + 1 = k` because `1 ≤ k`; it uses regularity on `W`. The restriction `rangeRaise`
  of an injective map is injective. For the image, `jetMap_jetMul` gives
  `jetRaise_W (I_1 [u]_1) = I_k [s ^ (k - 1) • u]_k`, and both submodules consist of exactly
  these elements.
- **Clause 6.** `rangeToSubquotient` is the map
  `Submodule.mapQ (jetMulToSub 𝔄 U s k) : U_k ⧸ ker I_k → (s ^ k U / s ^ (2k) U) / squeezeKernel`
  composed with the inverse of the linear equivalence `LinearMap.quotKerEquivRange`, so it
  suffices that this `mapQ` is bijective. It is surjective because `jetMulToSub` is (clause
  5). For injectivity, suppose `jetMulToSub x` lies in `squeezeKernel s k I`, i.e. it equals
  `jetMul z` for some `z ∈ ker I_k`. Then `z = x` by `jetMul_injective`, so `x ∈ ker I_k`.
  This clause uses only regularity on `U`.

## Clauses that use `J`

- **Clause 2.** An element of `s ^ k W / s ^ (2k) W` is `[s ^ k • v]_(2k)`. Since
  `I (J v) = s ^ k • v ∈ s ^ k W`, the class `[J v]_(2k)` lies in `A`, and
  `I_(2k) [J v]_(2k) = [s ^ k • v]_(2k)`.
- **Clause 3.** If `[u]_(2k) ∈ A` is in the kernel of `squeezeMap`, then
  `I u = s ^ (2k) • w` for some `w`. Applying the `R`-linear map `J` gives
  `s ^ k • u = J (I u) = s ^ (2k) • J w`, and `eq_smul_of_pow_smul_eq` (regularity on `U`)
  gives `u = s ^ k • J w`. Hence `[u]_(2k)` is the image under `jetMul` of `[J w]_k`, and
  `I_k [J w]_k = [s ^ k • w]_k = 0`, so `[u]_(2k) ∈ squeezeKernel s k I`. Conversely,
  `squeezeKernel s k I ≤ A` by clause 4, and the Library lemma `squeezeKernel_comap_le_ker`
  puts it in the kernel.
- **First half of clause 7.** `squeezeQuotientMap` is `Submodule.liftQ` of `squeezeMap`. It is
  injective by `Submodule.ker_liftQ_eq_bot`: by clause 3, the kernel of `squeezeMap` is
  contained in the preimage of `squeezeKernel` in `A`. It is surjective because `squeezeMap`
  is (clause 2).

## Relation to the source

The source is Bernstein–Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
arXiv:0812.1684v3, registered as
`bernstein-kroetz-2014-smooth-frechet-globalizations-arxiv-v3`, §10.1, Lemma 10.3 and the
discussion after it, up to Proposition 10.4 (PDF pp. 41–43).

- **Surjectivity.** The proof of clause 2 follows the source, which lifts a representative
  `w ∈ s^k𝒲` to `I^(-1)(w)`; here this lift is `J v` for `w = s ^ k • v`.
- **Kernel.** The Lean proof of clause 3 computes the kernel directly. It uses
  `J (I u) = s ^ k • u` and cancellation of `s ^ k` on `U` to write a kernel element as
  `[s ^ k • J w]_(2k)`, and `I (J w) = s ^ k • w` to see that `[J w]_k ∈ ker I_k`. It does
  not use the minimality of `k`. The printed proof of Lemma 10.3 ends instead with the claim
  that `p_(2k,k) ∘ I_(2k)^(-1) : s^k𝒲/s^(2k)𝒲 → H_k` is an injection. That claim is not
  used here, and it does not hold as stated. Take the trivial Harish-Chandra module `ℂ²` with
  its constant deformation, `I_s = diag(s^k, 1)` with `k ≥ 1`, so that
  `J(s) = s^k I_s^(-1) = diag(1, s^k)` is holomorphic and `k` is minimal. Then `I_s^(-1)`
  fixes `s^k e₂`, and `p_(2k,k)` sends its class to `0`, although the class of `s^k e₂` in
  `s^k𝒲/s^(2k)𝒲` is not zero. In this example the kernel of the restricted map is
  `s^k H_k = s^k O(D) e₁` modulo `s^(2k)`, as clause 3 asserts.
- **Comparisons.** The source sets `V₁ = s^k H_k`, `V₂ = s^k𝒰/s^(2k)𝒰` and
  `V₃ = H_k + s^k𝒰/s^(2k)𝒰` and states `V₂/V₁ ≃ 𝒰_k/H_k`, `V₂ ≃ 𝒰_k` and
  `V₃/V₁ ≃ 𝒲_k` as consequences of the lemma. Clauses 4–7 prove these, with `V₃` replaced by
  the intrinsic preimage `A` (see the page of the statement).
- **The sequence before Proposition 10.4.** The source displays the sequence
  `0 → U/H ≃ s^(k-1)U/s^(k-1)H → 𝒰_k/H_k → U/H_(k,1) → 0` and calls it exact. The Lean
  result covers only its first map: clause 8 proves that multiplication by `s ^ (k - 1)` on
  `W` gives an injection `range I_1 → range I_k` and identifies its image with
  `I_k (s ^ (k - 1) U / s ^ k U)`. The whole sequence is not exact in general. In the
  diagonal example above with `k = 3`, `H = H_(3,1) = ℂe₁`, so each outer term has
  dimension 1, while `𝒰₃/H₃ ≅ O(D)/s³O(D)` has dimension 3; exactness would force
  dimension 2.
