# Nonexistence of a nonzero form with only negative maximal cuspidal exponents

Module `Langlands.Global.AdelicCuspidalExponentNonexistenceStatement`.

This module states, for the actual adelic objects of the Library, the lemma of §6.4 of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37
(2024), journal pp. 203–204 (`bernstein-lapid-2024-meromorphic-continuation-eisenstein`; in the
arXiv TeX file `1911.02342.tex` of the same folder it carries the label `lem: nonexist`). The
statement is formulated for automorphic functions on `U_R(𝔸) M_R(F) \ G(𝔸)` for an arbitrary
standard parabolic `R`; the source states it for `R = G`. The module states the lemma and does
not prove it.

## Definitions

The definition lives in the namespace `Langlands.Global.StandardParabolicFamily` and uses the
objects of `Langlands.Global.AdelicLeadingCuspidalComponents` for a compatible family
`𝓕 : StandardParabolicFamily F G` of standard parabolics `P_J = M_J U_J`, indexed by the sets
`J` of simple relative roots of their Levi subgroups.

- `IsRelativeCuspidalExponentFamily hsmooth Kinf rho R f φc s c`: for every standard index
  `Q ≤ R`, `φc Q` is a cuspidal projection of the constant term `C_Q f`
  (`IsCuspidalProjection`, the characterization (6.8) of the source by the norm-one Levi
  pairings) and `(s Q, c Q)` is an unnormalized exponent decomposition of `φc Q`
  (`IsExponentDecomposition`, the decomposition (6.10)). Nothing is required along indices
  `Q ⊄ R`. For `R` the index of all simple roots this is
  `IsCuspidalExponentFamily` of `Langlands.Global.AdelicCuspidalExponentAscentStatement`.

The statement also uses `realExponent Q μ`, the image of `Re μ` in `𝔞_0^* = X^*(T) ⊗ ℝ`, from
that module.

## The statement

`CuspidalExponentNonexistenceStatement.{u}` carries the hypotheses of
`CuspidalExponentAscentStatement`: a number field `F`, a group scheme `G` with a compatible
standard family `fam`, a maximal compact subgroup `K` of `G(𝔸)` with `P_∅(𝔸) K = G(𝔸)` and
with maximal compact intersections with the standard Levis, a matrix representation `rho` that
is a closed immersion, a smooth structure `hsmooth`, and `Kinf = K ∩ G(F_∞)`. For

- a standard index `R` and a function `f` with `fam.IsAutomorphicOn hsmooth Kinf rho R f`
  (an automorphic function on `U_R(𝔸) M_R(F) \ G(𝔸)`),
- a family `(φc, s, c)` with `IsRelativeCuspidalExponentFamily` for `R` and `f`,
- such that for every `Q ≤ R` and every `μ ∈ s Q` with `c Q μ ≠ 0` there is a relative root
  `β` with `β ∉ Q`, `insert β Q = R` and `⟨realExponent Q μ, β^∨⟩ < 0`,

the conclusion is `f = 0`. The coroot `β^∨` is the supplied integral coroot
`fam.coroots.coroot β`, paired with `𝔞_0^*` by `RealTorusSpace.pair`. No positivity of the
size `N` of `rho` is assumed.

## Correspondence with the source

The source lemma (p. 203) reads: let `φ ∈ 𝒜_G`, and assume that every
`(P, λ) ∈ E^{cusp,un}(φ)` has `P` a maximal proper parabolic subgroup, `Δ_P = {α}`, with
`⟨Re λ, α^∨⟩ < 0`; then `φ = 0`.

- *Cuspidal exponents.* For `φ ∈ 𝒜_P` the source defines `E^{cusp}(φ)` as the pairs `(Q, λ)`
  with `Q ⊂ P` and `λ` a nonzero coordinate of the cuspidal component `C^{cusp}_{P,Q} φ` in the
  decomposition (6.6), and `E^{cusp,un}(φ)` by the unnormalized action ((6.10) and the following
  definition, pp. 202–203). With a family `(φc, s, c)` as above these are the pairs with
  `Q ≤ R`, `μ ∈ s Q` and `c Q μ ≠ 0`. As in `CuspidalExponentAscentStatement`, the source's
  cuspidal projection and exponent decomposition are unique (Mœglin–Waldspurger I.3.5 and the
  directness of (6.10)), and the statement quantifies over every family satisfying the
  Library's relations.
- *Maximality.* "`Q` is a maximal parabolic subgroup of `R`" means that the simple roots of `R`
  are those of `Q` together with one further simple root `β`; this is `β ∉ Q` and
  `insert β Q = R`. Such a `β` is a simple root, and `Q ≠ R`; in particular a nonzero component
  along `R` itself is excluded, as in the source, where `P` is a proper parabolic subgroup.
- *The sign condition.* In the source `α ∈ Δ_Q` is the projection to `𝔞_Q^*` of `β`. Since
  `Re μ ∈ 𝔞_Q^* ⊂ 𝔞_0^*` vanishes on `𝔞_0^Q`, its pairing with the coroot of `α` (a projection
  of the simple coroot `β^∨`) equals its pairing with `β^∨`, which is the Lean condition. The
  same convention is used in `CuspidalExponentAscentStatement`.
- *The parabolic `R`.* For `R` the index of all simple roots, `IsAutomorphicOn` is automorphy
  on `G(F) \ G(𝔸)` (the parabolic quotient subgroup of the full index is the rational subgroup,
  `parabolicQuotientSubgroup_top` in `Langlands.Global.AdelicStandardTopAutomorphy`), the
  constant term along the full index is the identity, and the statement is the source lemma.
  For general `R` it follows from the lemma for the Levi `M_R`, applied to the slices
  `m ↦ f(m k)`, `k ∈ K`, which are automorphic forms on `M_R(F) \ M_R(𝔸)`. Under the
  identification of the standard parabolics of `M_R` with the indices `Q ⊆ R`, the component of
  a slice at `μ` along `Q` is `m ↦ c Q μ (m k)`: constant terms are transitive, and the norm-one
  pairing characterizes the restricted cuspidal projection. So the cuspidal exponents of each
  slice form a subset of those of `f`; a nonzero component of `f` may vanish on a particular
  slice. The hypotheses of the lemma (maximality and negativity) therefore hold for every slice,
  and the lemma for `M_R` makes every slice vanish. Since `f` is left invariant under `U_R(𝔸)`
  and `G(𝔸) = U_R(𝔸) M_R(𝔸) K`, it follows that `f = 0`. The source applies the lemma to such
  slices in the proof of the corollary of §6.4 (p. 204), passing from `φ` to
  `φ'_k = C_{G,P_α} φ(· k)`, choosing `k` on which the given exponent survives, and replacing `G`
  by `M_{P_α}`. Mœglin–Waldspurger pass from Levi subgroups to `M(k) U(𝔸) \ G` in the proof of
  I.4.1, part (a) (p. 49).

## The source proof

The source deduces from Mœglin–Waldspurger I.4.1 (the growth of an automorphic form on a Siegel
set controlled by its cuspidal exponents, p. 49) that every right translate of `φ` is bounded
on `G(𝔸)^1`, hence so is every right translate of every constant term `C_{G,P} φ`. By
Proposition 6.2 (Mœglin–Waldspurger I.3.4) the constant terms along non-maximal proper `P`
vanish. Along a maximal `P` the constant term is then cuspidal, and on `𝔄_P^G` it is a
polynomial exponential function of `H_P(a)` whose exponents have nonzero real part; a bounded
function of this form vanishes (the difference-operator argument on p. 204). Hence `φ` is
cuspidal without cuspidal exponent along `G`, so `φ = 0`.

## Use

The corollary of §6.4 (`CuspidalExponentAscentStatement`) is deduced from the lemma for the
Levi of `P_α`, after subtracting the cuspidal projection along `P_α` and decomposing according
to the action of `𝔄_{P_α}` (p. 204).

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), 187–234: §6.2 (cuspidal exponents, pp. 200–202), §6.3 ((6.10),
  p. 203), §6.4 (the lemma, statement p. 203, proof p. 204, and the corollary with its proof,
  p. 204).
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995):
  I.3.4, I.3.5 and I.4.1 (pp. 45–51), cited by the source in the proof.
