# Boundedness of a form with only negative maximal cuspidal exponents

Module `Langlands.Global.AdelicCuspidalExponentBoundednessStatement`.

This module states, for the actual adelic objects of the Library, the first step of the proof of
the lemma of §6.4 of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), p. 204 (`bernstein-lapid-2024-meromorphic-continuation-eisenstein`):

> it easily follows from [MW, I.4.1] and the assumptions on `φ` that any right translate of `φ`
> is bounded on `G(𝔸)^1` (cf. the argument in [MW, I.4.11]). This implies that for any
> `P ∈ 𝒫`, any right translate of the constant term `C_{G,P} φ` is also bounded on `G(𝔸)^1`.

As for `CuspidalExponentNonexistenceStatement` (the lemma itself, in
`Langlands.Global.AdelicCuspidalExponentNonexistenceStatement`), the statement is formulated for
automorphic functions on `U_R(𝔸) M_R(F) \ G(𝔸)` for an arbitrary standard parabolic `R`; the
source states it for `R = G`. The module states the proposition and does not prove it.

## The statement

`CuspidalExponentBoundednessStatement.{u}` has exactly the hypotheses of
`CuspidalExponentNonexistenceStatement`: the number field `F`, the group scheme `G` with a
compatible standard family `fam`, the maximal compact `K` with minimal-parabolic Iwasawa coverage
and maximal compact Levi intersections, a closed matrix embedding `rho`, a smooth structure
`hsmooth`, `Kinf = K ∩ G(F_∞)`, a standard index `R`, an automorphic function `f` on
`U_R(𝔸) M_R(F) \ G(𝔸)`, a family `(φc, s, c)` of cuspidal projections and exponent
decompositions of its constant terms along the standard `Q ⊆ R`
(`IsRelativeCuspidalExponentFamily`), and the assumption that every nonzero component
`c Q μ` has `R = Q ∪ {β}` with `β ∉ Q` and `⟨realExponent Q μ, β^∨⟩ < 0`. The conclusion: for
every `Q ⊆ R` and every `g ∈ G(𝔸)` there is a constant `C` with

`‖C_Q f (m g)‖ ≤ C` for every `m` in the norm-one subgroup `M_R(𝔸)^1`
(`normOneSubgroup F (fam.M R)`, embedded in `G(𝔸)` through `fam.l R ≫ fam.p R`).

For `Q = R` the constant term is `f` itself (it is invariant under `U_R(𝔸)`), so the statement
contains the boundedness of every right translate of `f` on `M_R(𝔸)^1`.

## Correspondence with the source

- *The case `R = G`.* For the full index, `IsAutomorphicOn` is automorphy on `G(F) \ G(𝔸)`,
  `M_R = G` and the norm-one subgroup is `G(𝔸)^1`; the hypotheses are those of the lemma
  (every cuspidal exponent `(P, λ)` has `P` maximal and `⟨Re λ, α^∨⟩ < 0`), and the conclusion
  is the boundedness of every right translate of every constant term `C_{G,P} φ` on `G(𝔸)^1`
  quoted above.
- *General `R`.* For `k ∈ K` the slice `m ↦ f(m k)` is an automorphic form on
  `M_R(F) \ M_R(𝔸)`. Its component at `μ` along the standard parabolic of `M_R` attached to
  `Q ⊆ R` is `m ↦ c Q μ (m k)` (transitivity of constant terms and the norm-one pairing
  characterization of the cuspidal projection), so its cuspidal exponents form a subset of those
  of `f` and satisfy the same hypotheses; a nonzero component of `f` may vanish on a particular
  slice. The case `R = G` for `M_R` gives the boundedness of the right translates of every slice
  on `M_R(𝔸)^1`. A general `g ∈ G(𝔸) = U_R(𝔸) M_R(𝔸) K` reduces to this: writing
  `g = u m₀ k`, left invariance under `U_R(𝔸)` gives `f(m g) = f(m m₀ k)` for `m ∈ M_R(𝔸)`, a
  right translate of the slice at `k`. For `m ∈ M_R(𝔸)^1` the constant term
  `C_Q f(m g)` is an average over `U_Q(F) \ U_Q(𝔸)`, `U_Q = U_R (U_Q ∩ M_R)`, of values of `f` at
  points of `U_R(𝔸) M_R(𝔸)^1 m g`, so it is bounded as well. This is the passage of the source's
  corollary (p. 204) and of Mœglin–Waldspurger I.4.1, part (a) (p. 49), from Levi subgroups to
  `M(k) U(𝔸) \ G`.
- *The source of the bound.* Mœglin–Waldspurger I.4.1 (p. 49) bounds an automorphic form on a
  Siegel set by `∑ m_{P_0}(g)^{Re π + ρ_P} (1 + ‖log_M m_P(g)‖)^{deg}` over its cuspidal data;
  `Re π + ρ_P` is the unnormalized cuspidal exponent of (6.10). When every exponent is attached
  to a maximal parabolic and has negative pairing with the coroot, each term is bounded on the
  part of the Siegel set in `G(𝔸)^1`, and reduction theory covers `G(𝔸)^1`.
- *Choice of data.* As in `CuspidalExponentAscentStatement`, the statement quantifies over every
  family of cuspidal projections and exponent decompositions satisfying the Library's relations;
  the source's are unique. No positivity of the size of `rho` is assumed.

## Use

`Langlands.Global.AdelicCuspidalExponentNonexistenceReduction` proves
`CuspidalExponentNonexistenceStatement` from this statement, the vanishing criterion (8.1)
(`ParabolicCuspidalVanishingStatement`) and the automorphy of constant terms
(`ConstantTermAutomorphyStatement`), following the rest of the source proof.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024): the proof of the lemma of §6.4, p. 204; the proof of the corollary,
  p. 204.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995):
  I.4.1 (p. 49), cited by the source, and I.4.11 (exponents of square-integrable forms,
  p. 74), whose argument the source refers to.
