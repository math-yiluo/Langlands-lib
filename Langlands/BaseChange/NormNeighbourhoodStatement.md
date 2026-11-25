# Statement: norms and regular elliptic elements near `1`

The module `Langlands.BaseChange.NormNeighbourhoodStatement` (namespace
`Langlands.BaseChange`) states, as the proposition `NormNeighbourhoodStatement.{u, v}`, three
local facts about `GL_n(F)` near the identity that the choice of a global regular elliptic
norm in Henniart–Lemaire II.6.7 uses: regular elliptic elements accumulate at `1`, every
element near `1` is a norm, and the regular semisimple norms form an open set. The statement is
**not proved** here.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, file
  `/home/taskhub/central-library/Henniart-Lemaire--Changement de base et induction automorphe pour GLn en caracteristique non nulle--2011.pdf`
  (PDF page = printed page + 8). Cited as HL.
  - II.2.10 (printed p. 71): for a maximal torus `T` of `G` defined over `F`, the exact
    sequence `1 → T(E)^{σ-1} → T(E) → T(F)` of the norm, and, `T` being quasi-trivial, the
    norm `T(E) → T(F)` is submersive, hence an open map.
  - II.6.7 (printed pp. 123–124): at `v₀`, "la norme … est continue et submersive (donc
    ouverte) au voisinage de 1", which gives a regular elliptic norm `γ_{v₀}` where the
    orbital integral of the pseudo-coefficient is nonzero; then a global
    `γ ∈ G(F)'' ∩ N(G(E))` close to `γ_{v₀}` and `γ_{v₁}` is chosen.
  - II.6.8 (printed p. 124): at the places `v ∈ S ∖ {v₀, v₁}`, a function supported in
    `G(F_v)_r ∩ N_v(G(E_v))` with positive orbital integral at `γ`, built from a small
    neighbourhood of `γ` in the regular norms.

## The statement

Let `F : Type u` be a nonarchimedean local field of characteristic zero (`[Field F]
[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`) and
`n : ℕ`; `GL_n(F)` has its topology as the units of the matrix ring. Then:

- **(b)** if `0 < n`, every neighbourhood `U` of `1` in `GL_n(F)` (`U ∈ nhds 1`) contains an
  element `γ` with `JacquetLanglands.IsRegularElliptic γ` (characteristic polynomial
  separable and irreducible);
- and for every commutative `F`-algebra `E : Type v` with `[TopologicalSpace E]
  [IsTopologicalRing E] [IsModuleTopology F E]`, every `σ : E ≃ₐ[F] E` and every `l : ℕ` with
  `IsCyclicAlgebra σ l` (module `Langlands.BaseChange.Norm`):
  - **(a)** there is a neighbourhood `V` of `1` in `GL_n(F)` such that every `γ ∈ V` satisfies
    `IsNorm σ l γ` (`γ` is associated with some `δ ∈ GL_n(E)`, that is,
    `N(δ) = δ δ^σ ⋯ δ^{σ^{l-1}}` is conjugate in `GL_n(E)` to `γ`);
  - **(c)** the set `{γ : GL_n(F) | JacquetLanglands.IsRegularSemisimple γ ∧ IsNorm σ l γ}`
    of regular semisimple norms is open in `GL_n(F)`.

In Lean, clause (b) comes first, before the quantifier over `E`, since it does not involve `E`.

## Use

In the global comparison of HL II.6.7–II.6.10 (printed pp. 123–126), the global regular
elliptic norm `γ` is chosen close, at the places `v₀` and `v₁`, to local regular elliptic
elements where the orbital integrals of the chosen test functions are nonzero;
`CuspidalPseudoCoefficientExistenceStatement` (clause (d)) and `SupercuspidalCuspFormStatement`
give these nonzero orbital integrals near `1`. Clauses (a) and (b) provide, near `1`,
regular elliptic elements that are norms. At the other places of `S`, the test function is the
indicator of a small neighbourhood of `γ` inside the open set of regular semisimple norms
(clause (c)), and outside `S` the unit of the spherical Hecke algebra; both have positive
orbital integral at `γ` (statement 13, `OrbitalIntegralPositivityStatement`).

## Proof ideas (not formalized)

- **(a)** In characteristic zero, an element `γ` close enough to `1` has an `l`-th root
  `γ^{1/l} ∈ GL_n(F)` given by the binomial series `∑ binom(1/l, k) (γ - 1)^k`, which converges
  for `γ - 1` small. Then `δ = baseChange F E n (γ^{1/l})` is σ-fixed, so
  `N(δ) = δ^l` is `γ` viewed in `GL_n(E)`, and `γ` is a norm.
- **(b)** Take the unramified extension `K/F` of degree `n` and `α` in its ring of integers
  with `K = F(α)`. Multiplication by `1 + ϖ^k α` on `K ≅ F^n` (`ϖ` a uniformizer of `F`) is an
  element of `GL_n(F)` whose characteristic polynomial is the minimal polynomial of
  `1 + ϖ^k α`, which generates `K` and is separable of degree `n`, hence irreducible; these
  elements are regular elliptic and tend to `1` as `k → ∞`.
- **(c)** HL II.2.10: for each maximal torus `T`, the norm `T(E) → T(F)` is open, and the map
  `G(F) × T(F)_r → G(F)_r`, `(g, t) ↦ g t g⁻¹`, is submersive; the regular semisimple norms
  near a regular semisimple norm `γ` with centralizer `T` are the conjugates of the elements of
  `N(T(E))` near `γ`, hence form a neighbourhood of `γ`.

## Hypotheses

- `CharZero F`, as in the statements on orbital integrals, twisted characters and functions
  whose orbital integrals vanish off the elliptic set: the Library's `IsRegularSemisimple` and
  `IsRegularElliptic` ask for a separable characteristic polynomial, which is HL's regularity
  in characteristic zero; and the proof idea of (a) (the binomial series for `γ^{1/l}`) uses
  characteristic zero.
- Clause (b) needs `0 < n`: `GL_0(F)` is the trivial group, the characteristic polynomial of
  its element is `1`, which is not irreducible, so no element of `GL_0(F)` is regular
  elliptic.
- `IsCyclicAlgebra σ l` and the module topology on `E` give the setting of HL.

## Measures

No measure enters this statement.

## Dependencies and names

The module imports `Langlands.BaseChange.Norm` (`IsNorm`, `IsCyclicAlgebra`) and
the Library's `Langlands.JacquetLanglands.RegularElliptic` (`IsRegularElliptic`,
`IsRegularSemisimple`), with the names and argument orders as published.
