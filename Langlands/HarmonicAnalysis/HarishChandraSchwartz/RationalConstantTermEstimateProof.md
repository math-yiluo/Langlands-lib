# Waldspurger II.4.5 on actual rational points

`Langlands.HarishChandraSchwartz.rationalConstantTermEstimate` proves
`RationalConstantTermEstimateStatement.{u}` (module `RationalConstantTerm`) at
an arbitrary universe `u`, with no hypothesis beyond those of the statement.
[Target](RationalConstantTerm.md) ·
[Reduction](RationalConstantTermAnalyticReduction.md)

## The statement

Let F be a nonarchimedean local field, G a connected reductive group over F,
`i : S → G` a maximal split torus, ν a generic cocharacter and J a set of
simple relative roots, with standard parabolic `P_J = M_J U_J`. Let K0 be a
compact open subgroup of G(F) carrying the three structural premises
`SimultaneousStandardBasisAt i ν K0`, `FiniteCartanCovering F i ν K0` and
`StandardLeviCartanCovering F i ν J K0`. Then for every compact open K with
G(F) = P₀(F) K and M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F)), every closed matrix
representation ρ (height σ = `rationalHeight ρ`) and every Haar measure ν_U on
U_J(F), the estimate `ConstantTermEstimate` holds: for every real d there are a
real d' and c ≥ 0 with

```
δ_{U_J}(m)^{1/2} ∫⁻_{U_J(F)} Ξ(m u) (1 + σ(m u))^(-d') dν_U(u)
  ≤ c Ξ^{M_J}(m) (1 + σ(m))^(-d)
```

for all m in M_J(F). Here Ξ = `rationalXi hKc hPK` and
Ξ^{M_J} = `rationalLeviXi hKc hM` are the Harish-Chandra functions of G(F) and
M_J(F) built from K, and δ_{U_J} = `standardUnipotentModulus i ν J`.

## The proof

The proof is one application of
`rationalConstantTermEstimate_of_analyticInputs` (module
`RationalConstantTermAnalyticReduction`), which derives the statement from
three analytic statements. Each is supplied by a theorem of the Library:

- `RationalXiGlobalUpperBoundStatement`, by `rationalXiGlobalUpperBound`
  (module `RationalXiGlobalUpperBoundProof`): there are D ∈ ℕ and C > 0 with
  Ξ(g) ≤ C φ_K(g) (1 + σ(g))^D for all g in G(F), where φ_K is the Iwasawa
  weight, φ_K(p k) = δ₀(p)^{1/2}. This is a global form of the estimate in the
  proof of Lemma II.4.4.
- `RationalUnipotentWeightIntegrabilityStatement`, by
  `rationalUnipotentWeightIntegrability` (module
  `RationalUnipotentWeightIntegrabilityProof`): on an opposite standard
  unipotent radical, the Iwasawa weight times a sufficiently negative power of
  1 + σ is integrable for every Haar measure (Lemma II.4.2).
- `RationalLeviXiLowerBoundStatement`, by `rationalLeviXiLowerBound` (module
  `RationalLeviXiLowerBoundProof`): for every finite set F0 of points of the
  torus centralizer there is C > 0 with φ_K^{M_J}(m) ≤ C Ξ^{M_J}(m) for all
  m = f i(a), f ∈ F0, a in the chamber `CAplus F S J` (dominant for the roots
  in J). Here φ_K^{M_J} is the Iwasawa weight of `M_J`, equal to
  δ₀^{M_J}(m)^{1/2} at these points (Lemma II.1.1 for `M_J`).

The reduction itself is described in its Markdown. In short, it reverses
the generic cocharacter, so that the integrated radical U_J is the opposite
radical of a standard cocharacter for the reversed chamber. It then applies the
three estimates to the reversed minimal data on a set T of representatives
with M_J(F) = (K0 ∩ M_J(F)) T (K0 ∩ M_J(F)): the finitely many centralizer
translates of the reversed chamber supplied by the Levi Cartan covering. It
assembles them by the abstract scalar argument `constantTermRepresentativeEstimate_of_bounds`
together with the product-height bound of Lemma II.3.1. Finally it extends
the estimate from the representatives to all of M_J(F) by
`rationalConstantTermEstimate_of_compact_doubleCosetCover`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333,
Proposition II.4.5 and its proof, printed pp. 262–263. The remark following
it on p. 263 allows the change of minimal parabolic used for the opposite
parabolic P̄_J. Registered source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`;
PDF page = printed page minus 234.
