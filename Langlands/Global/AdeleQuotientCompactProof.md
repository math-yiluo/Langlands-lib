# Compactness of the additive adele quotient `𝔸_K / K`

Author: Worker 232. Proof contribution to task
`f717a350-539d-4629-93de-33784c2d96ec`, revision 2.

The theorem `Langlands.Global.adeleQuotientCompact K` proves the published
`Langlands.Global.AdeleQuotientCompactStatement K`, that is,
`CompactSpace (AdeleQuotient K)`. It holds for every `K : Type u` with
`[Field K] [NumberField K]`, and uses no other hypotheses. `AdeleQuotient K` is
`Adeles K ⧸ principalAdeles K`: Mathlib's number-field adele ring modulo the
range of the diagonal embedding `algebraMap K (Adeles K)`, with the quotient
topology. The proof does not change these definitions or their topologies.

## Implemented proof

The proof constructs a compact set `C ⊆ 𝔸_K` with `𝔸_K = K + C`. Then the
image of `C` under the continuous quotient map is the whole quotient, so the
quotient is compact. `C` is the product
`archimedeanFundamentalSet K ×ˢ integralFiniteAdeles K`.

### Finite adeles: `𝔸_K^f = K + ∏_v 𝒪_v`

Here `v` ranges over the finite places `FinitePlace K`, `K_v` is
`FiniteCompletion K v`, `𝒪_v` is `v.adicCompletionIntegers K`, and `Valued.v`
is the valuation of `K_v`. All five lemmas are public.

1. `exists_integer_sub_valued_le`. Let `c ∈ 𝒪_v` and let `δ` be a nonzero
   element of `𝓞 K`. Then some `r : 𝓞 K` satisfies `Valued.v (c - r) ≤ Valued.v δ`
   in `K_v`. The set `U` of `y ∈ 𝒪_v` with `(y - c) δ⁻¹ ∈ 𝒪_v` is open and
   contains `c`. Since `K` is dense in `K_v` (Mathlib's `denseRange_algebraMap`),
   `U` contains the image of some `k ∈ K`, and this `k` is `v`-integral.
   Mathlib's `exists_valuation_sub_lt_of_integer` gives `r : 𝓞 K` with
   `v(r - k) < v(δ)`. Both `c - k` and `k - r` then have valuation at most
   `Valued.v δ`, so `c - r` does too, by the ultrametric inequality.
2. `valued_algebraMap_integer` identifies `Valued.v` on the image of `r : 𝓞 K`
   with `v.intValuation r`.
3. `exists_integer_forall_sub_valued_le` is the Chinese remainder step. Fix a
   finite set `s` of finite places, elements `c v ∈ 𝒪_v` for `v ∈ s`, and a
   nonzero `δ : 𝓞 K`. Then one `r : 𝓞 K` satisfies
   `Valued.v (c v - r) ≤ Valued.v δ` for every `v ∈ s`. Lemma 1 gives a separate
   integer `ρ v` for each `v`. Choose `n v` with `exp(-n v) < v.intValuation δ`
   (`WithZero.exists_exp_neg_natCast_lt`). Mathlib's
   `IsDedekindDomain.exists_forall_sub_mem_ideal` gives `r` with
   `r - ρ v ∈ v^{n v}` for each `v ∈ s`. Then `ρ v - r` has valuation at most
   `exp(-n v)`, which is less than `v(δ)`. Combining this with Lemma 1 by the
   ultrametric inequality gives the bound.
4. `exists_integer_mul_mem_adicCompletionIntegers` clears denominators: for every
   finite adele `a` there is a nonzero `d : 𝓞 K` with `d · a_v ∈ 𝒪_v` for all
   `v`. Let `S` be the finite set of places where `a_v ∉ 𝒪_v`. Mathlib's
   `adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers` gives a nonzero
   `b_v` with `b_v a_v ∈ 𝒪_v`. Then take `d = ∏_{v ∈ S} b_v`.
5. `exists_sub_mem_integralFiniteAdeles`: every finite adele `a` has some `x ∈ K`
   with `a - x ∈ integralFiniteAdeles K`. Take `d` from Lemma 4 and let `T` be the
   finite set of places dividing `d` (`Ideal.finite_factors`). Lemma 3, applied
   to `c v = d · a_v` and `δ = d` on `T`, gives `r : 𝓞 K`, and we put
   `x = r / d`. At every place, `a_v - x = (d a_v - r) d⁻¹`. This lies in `𝒪_v`
   exactly when `Valued.v (d a_v - r) ≤ Valued.v d`. For `v ∈ T` this is
   Lemma 3. For `v ∉ T`, `Valued.v d = 1`, and both `d a_v` and `r` lie in `𝒪_v`.

Membership in `integralFiniteAdeles K` is checked coordinatewise with the
published `mem_integralFiniteAdeles`.

### Infinite adeles

The proof uses the published module `Langlands.Global.ArchimedeanFundamentalSet`.
`archimedeanFundamentalSet K` is compact (`isCompact_archimedeanFundamentalSet`).
By `exists_sub_integer_mem_archimedeanFundamentalSet`, every infinite adele `b`
has some `y : 𝓞 K` with `b - y ∈ archimedeanFundamentalSet K`. This module adds
no archimedean lemmas.

### Assembly

`adeleQuotientCompact` combines the two halves. `C` is compact as a product of
the compact sets `archimedeanFundamentalSet K` and `integralFiniteAdeles K`
(`isCompact_integralFiniteAdeles`). Let `a = (a_∞, a_f)` be an adele. Lemma 5
gives `x ∈ K` with `a_f - x` integral. The archimedean lemma, applied to
`a_∞ - x`, gives `y : 𝓞 K` with `a_∞ - x - y ∈ archimedeanFundamentalSet K`.
Since `y` is integral at every finite place (`coe_mem_adicCompletionIntegers`),
`a_f - x - y` is also integral. So `a - (x + y)` lies in `C`. It has the same
class as `a` modulo the principal adeles, because the difference is the
diagonal image of `x + y`. Hence `QuotientAddGroup.mk '' C` is the whole
quotient. It is compact because `QuotientAddGroup.mk` is continuous, so the
quotient is a compact space.

## Scope and provenance

The target statement and how it matches Cassels (*Global fields*, §14,
Theorem, p.64) and Weil (*Basic Number Theory*, IV §2, Theorem 2) are documented
in the published `Langlands/Global/AdeleQuotientStatement.md`. The
implemented proof follows the idea of Cassels §14, Corollary 1, p.65: every adele
is an element of `K` plus an element of a fixed compact set. It does not reduce
to `ℚ` as Cassels does. Instead it argues directly over `K`, using
density, the Chinese remainder theorem in `𝓞 K`, and Mathlib's integer lattice
in the mixed space. Its lemmas are derived and internal. This module introduces
no definitions and changes no published statement.

## Reusable API

- `exists_sub_mem_integralFiniteAdeles`: `𝔸_K^f = K + ∏_v 𝒪_v`.
- `exists_integer_forall_sub_valued_le`: simultaneous approximation of local
  integers by one global integer at finitely many places.
- `exists_integer_mul_mem_adicCompletionIntegers`: clearing denominators of a
  finite adele.
- `adeleQuotientCompact K`: the target theorem, of type
  `AdeleQuotientCompactStatement K`.
- `compactSpace_adeleQuotient K`: the same fact with its type written as
  `CompactSpace (AdeleQuotient K)`, so downstream proofs can install it locally
  with `haveI := compactSpace_adeleQuotient K`.
