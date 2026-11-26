# Ascent of a cuspidal exponent through a simple root

Module `Langlands.Global.AdelicCuspidalExponentAscentStatement`.

This module states, for the actual adelic objects of the Library, the corollary in §6.4 of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), journal p. 204 (`bernstein-lapid-2024-meromorphic-continuation-eisenstein`). In the
published paper it is the corollary following the lemma of §6.4, cited in §6.5 as
"Corollary 6.4". In the arXiv TeX file `1911.02342.tex` of the same folder it carries the label
`cor: uniquemax`. It is the analytic input of the proof of Theorem 6.3 (§6.5, pp. 204–205). The
module states the corollary and does not prove it.

## Definitions

All definitions live in the namespace `Langlands.Global.StandardParabolicFamily` and use the
objects of `Langlands.Global.AdelicLeadingCuspidalComponents`: a compatible family
`𝓕 : StandardParabolicFamily F G` of standard parabolics `P_J = M_J U_J` of a connected reductive
group `G` over a number field `F`, indexed by the sets `J` of simple relative roots of their
Levi subgroups.

- `IsCuspidalExponentFamily hsmooth Kinf rho φ φc s c`: for every standard index `Q`, `φc Q` is
  a cuspidal projection of the constant term `C_Q φ` along `Q` (`IsCuspidalProjection`, the
  characterization (6.8) of BL by the norm-one Levi pairings) and `(s Q, c Q)` is an
  unnormalized exponent decomposition of `φc Q` (`IsExponentDecomposition`, the decomposition
  (6.10)): `φc Q = ∑_{λ ∈ s Q} c Q λ` with cuspidal automorphic components `c Q λ` on
  `U_Q(𝔸) M_Q(F) \ G(𝔸)` of unnormalized exponent `λ`.
- `realExponent Q λ`: the image of `Re λ` in `𝔞_0^* = X^*(T) ⊗ ℝ` under `chamberEmbedding Q`,
  restriction of characters of `P_Q` to the maximal split torus `T`. This is the embedding
  `𝔞_Q^* ⊂ 𝔞_0^*` used by BL (§6.1) and by the Library's `IsLeadingExponent`.
- `rootSpanReal R`: the real span of the simple roots in `R` inside `𝔞_0^*`. For `R` the
  simple roots of a standard Levi `M_R` this is BL's `(𝔞_0^{R})^*` (§6.1: "`Δ_0^P` is a basis
  for `(𝔞_0^P)^*`").

## The statement

`CuspidalExponentAscentStatement.{u}` carries the hypotheses of the published
`LeadingCuspidalInjectivityStatement`: a number field `F`, a group scheme `G` with a compatible
standard family `fam`, a maximal compact subgroup `K` of `G(𝔸)` with `P_∅(𝔸) K = G(𝔸)` and with
maximal compact intersections with the standard Levis, a matrix representation `rho` that is a
closed immersion, a smooth structure `hsmooth`, and `Kinf = K ∩ G(F_∞)`. For

- an automorphic function `φ` on `G(F) \ G(𝔸)` (`IsAutomorphicFunctionOn` for the rational
  subgroup),
- a family `(φc, s, c)` with `IsCuspidalExponentFamily`,
- a standard index `P` and `λ ∈ s P` with `c P λ ≠ 0`,
- such that `c Q μ = 0` for every `μ ∈ s Q` whenever `Q.1.ncard < P.1.ncard`,
- and a simple relative root `α ∉ P` with `⟨realExponent P λ, α^∨⟩ < 0`,

there are a standard index `Q`, a relative root `β` and `μ ∈ s Q` such that

- `β ∉ Q` and `insert β Q = insert α P` (as sets of simple roots),
- `c Q μ ≠ 0`,
- `⟨realExponent Q μ, β^∨⟩ ≥ 0`,
- `realExponent P λ - realExponent Q μ ∈ rootSpanReal (insert α P)`.

The coroots `α^∨`, `β^∨` are the supplied integral coroots `fam.coroots.coroot`, paired with
`𝔞_0^*` by `RealTorusSpace.pair`.

## Correspondence with the source

BL define `E^{cusp,un}(φ)` as the set of pairs `(Q, μ)` such that the cuspidal component
`C^{cusp}_{G,Q} φ` has a nonzero `μ`-coordinate in (6.10). With a family `(φc, s, c)` as above
these are the pairs with `μ ∈ s Q` and `c Q μ ≠ 0`.

- *Minimality.* "`P` is minimal with respect to `φ`" means `E^{cusp}_P(φ) ≠ ∅` and
  `E^{cusp}_Q(φ) = ∅` for every standard `Q` of smaller semisimple rank (p. 204). The
  semisimple rank of `P_J` is the number `J.ncard` of simple roots of its Levi.
- *The root `α`.* BL take `α ∈ Δ_P`, the projection to `𝔞_P^*` of the unique simple root
  `β ∈ Δ_0 \ Δ_0^P` above it, and `P_α` with `Δ_0^{P_α} = Δ_0^P ∪ {β}`. In the Lean statement the
  simple root of `Δ_0 \ Δ_0^P` itself is called `α`, and `P_α` is the index `insert α P`. Since
  `Re λ ∈ 𝔞_P^* ⊂ 𝔞_0^*` vanishes on `𝔞_0^P`, its pairing with the coroot of `α ∈ Δ_P` (a
  projection of the simple coroot) equals its pairing with the simple coroot, which is the Lean
  hypothesis.
- *The parabolic `Q`.* "`Q` is a maximal parabolic subgroup of `P_α`" with
  `Δ_Q^{P_α} = {β}` is expressed by `β ∉ Q` and `insert β Q = insert α P`; the `β` of the Lean
  statement is the simple root of `Δ_0^{P_α} \ Δ_0^Q`. The pairing `⟨Re μ, β^∨⟩` is again the
  pairing with the simple coroot. BL also record that `Q` is minimal with respect to `φ`; this
  follows from `Q.ncard = P.ncard` and is not part of the Lean conclusion.
- *Central parameters.* BL assert `μ_{P_α} = λ_{P_α}`, the equality of the restrictions to
  `𝔄_{P_α}`. Taking real parts gives `(Re μ)_{P_α} = (Re λ)_{P_α}` ("`Re λ_P = (Re λ)_P`",
  §6.2), the equality of the `𝔞_{P_α}^*`-components in `𝔞_0^* = (𝔞_0^{P_α})^* ⊕ 𝔞_{P_α}^*`
  (§6.1). It says that `Re λ - Re μ ∈ (𝔞_0^{P_α})^*`, the real span of `Δ_0^{P_α}`, which is
  the last clause. Only this real-part consequence is asserted.
- *Choice of data.* BL's cuspidal projection and exponent decomposition are unique (MW I.3.5
  and the directness of (6.10)), so `E^{cusp,un}(φ)` does not depend on choices. The Library
  defines both by relations (`IsCuspidalProjection`, `IsExponentDecomposition`); the statement
  quantifies over every family satisfying them. Directness of (6.10) for the Library's orbit
  condition is the published theorem
  `StandardParabolicFamily.eq_zero_of_sum_eq_zero_of_hasUnnormalizedExponent`.

The source data of `AdelicLeadingCuspidalComponents` (a faithful closed embedding `rho` and
`K_∞` in good position) are those of the statement; no positivity of the size `N` of `rho` is
assumed.

## The source proof

BL prove the corollary from the lemma of §6.4: if every cuspidal exponent `(P, λ)` of `φ` has
`P` maximal with `⟨Re λ, α^∨⟩ < 0` for `Δ_P = {α}`, then `φ = 0`. That lemma uses the growth
bound of Mœglin–Waldspurger I.4.1 in terms of cuspidal exponents (each right translate of `φ` is
bounded on `G(𝔸)^1`), Proposition 6.2 (an automorphic form without cuspidal exponents vanishes,
MW I.3.4), and the fact that a bounded polynomial exponential function on `ℝ` has purely
imaginary exponents. The corollary is deduced by passing to `φ'_k = C_{G,P_α} φ(· k)` on
`M_{P_α}`, subtracting the cuspidal projection along `P_α`, and decomposing according to the
action of `𝔄_{P_α}`.

## Use

The proof of Theorem 6.3 in §6.5 chooses a cuspidal exponent `(P, λ)` with `P` minimal and
`⟨Re λ, ϖ^∨⟩` maximal for some `ϖ^∨` positive on the simple roots, and uses the corollary to
show that `λ` is leading.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), 187–234: §6.1 (decompositions of `𝔞_0^*`), §6.2 (cuspidal exponents,
  pp. 200–202), §6.3 (Theorem 6.3, p. 203), §6.4 (the lemma and the corollary, pp. 203–204),
  §6.5 (proof of Theorem 6.3, pp. 204–205).
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995):
  I.3.4, I.3.5 and I.4.1, cited by BL in the proof.
