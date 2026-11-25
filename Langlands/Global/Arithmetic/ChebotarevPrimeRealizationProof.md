# Chebotarev's theorem in existence form: proof of the prime realization statement

`Langlands.Global.chebotarevPrimeRealizationStatement` proves `Langlands.Global.ChebotarevPrimeRealizationStatement.{u, v}` exactly. Let L/K be a Galois extension of number fields with `K : Type u` and `L : Type v`, let σ ∈ Gal(L/K), and let S be a finite set of height-one primes of 𝓞_K. Then there are
- a height-one prime p of 𝓞_K with p ∉ S, and
- a height-one prime q of 𝓞_L lying over p, unramified over 𝓞_K (`Algebra.IsUnramifiedAt (𝓞 K) q`),

such that `RingOfIntegers.mapAlgHom σ` is an arithmetic Frobenius at q (`AlgHom.IsArithFrobAt`). That is, σ(x) − x^#(𝓞_K/p) ∈ q for every x ∈ 𝓞_L. No hypothesis is added to the statement.

## Input

The main input is the ported theorem `NumberField.exists_prime_isArithFrobAt_of_isGalois` from `Langlands/AnthropicFLT/Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean`. That file is part of the port of the Anthropic FLT Chebotarev closure under `Langlands/AnthropicFLT/`; its Markdown lists the provenance and the edits. Its statement: for a Galois extension L/K of number fields in arbitrary universes, σ ∈ Gal(L/K) and a finite set T of naturals, there are a rational prime p ∉ T and a maximal ideal Q of 𝓞_L with p ∈ Q and `IsArithFrobAt ℤ σ Q`, that is, σ(x) ≡ x^#(ℤ/(Q ∩ ℤ)) modulo Q.

One further port lemma is used: `P2MW.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.P2mCycloSplit.card_le_of_forall_pow_eq`. It states that a finite field in which every element satisfies y^p = y has at most p elements.

## Proof

The adapter applies the ported theorem with

T = {#(ℤ/(w ∩ ℤ)) : w ∈ S} ∪ {rational primes dividing the discriminant d_L},

a finite set because d_L ≠ 0. This gives a prime p ∉ T and a maximal ideal Q of 𝓞_L containing p at which σ is an arithmetic Frobenius over ℤ. Five lemmas in the namespace `Langlands.Global.ChebotarevRealization` turn this into the Library conclusion.

1. `liesOver_of_prime_mem`: since Q is maximal and contains p, Q lies over pℤ (`Ideal.liesOver_span_iff`).
2. Q is nonzero, because 𝓞_L is not a field. It is therefore a height-one prime q. Its contraction v = Q ∩ 𝓞_K is nonzero (`Ideal.IsIntegral.under_ne_bot`), so it is a height-one prime of 𝓞_K, and q lies over v.
3. `outside_finite_set`: v lies over pℤ, so #(ℤ/(v ∩ ℤ)) = p. Since p is not among the norms #(ℤ/(w ∩ ℤ)) of the members w of S, v ∉ S.
4. `unramified_of_not_dvd_discr`: p does not divide d_L. By `NumberField.not_dvd_discr_iff_forall_mem`, Q is unramified over ℤ. Then `Algebra.IsUnramifiedAt.of_restrictScalars` shows that Q is unramified over 𝓞_K.
5. `base_card_eq_prime` and `relative_frobenius`: σ fixes 𝓞_K, so the Frobenius congruence gives y^p = y for every y in the residue field 𝓞_K/v. The lemma of the port bounds its cardinality by p. The residue field also contains ℤ/(v ∩ ℤ), which has p elements, so #(𝓞_K/v) = p = #(ℤ/(Q ∩ ℤ)). The action of σ on 𝓞_L used by `IsArithFrobAt ℤ σ Q` agrees definitionally with `RingOfIntegers.mapAlgHom σ`. Hence the congruence over ℤ is exactly the relative congruence `(RingOfIntegers.mapAlgHom σ).IsArithFrobAt q`. The same arithmetic convention is used on both sides, and no inverse is introduced.

## Provenance

The adapter follows the private bridges of the audit `notes/reuse/anthropic-chebotarev-audit.md`, section "The first endpoint", whose source text is in `notes/reuse/anthropic-chebotarev-evidence/bridges.md`. The audit's lemmas `ChebotarevAudit.liesOver_of_prime_mem`, `outside_finite_set`, `unramified_of_not_dvd_discr`, `base_card_eq_prime` and `relative_frobenius` become the declarations of the same names in the namespace `Langlands.Global.ChebotarevRealization`, and its `realization` becomes the final theorem `Langlands.Global.chebotarevPrimeRealizationStatement`. The audit's secondary lemma `localDegree_ne_one` is not included; it concerns `Langlands.Global.CyclicNonsplitPrimeStatement`, which is proved separately as `Langlands.Global.cyclicNonsplitPrimeStatement` in `Langlands/Global/Arithmetic/CyclicNonsplitPrimeProof.lean`.
