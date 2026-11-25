# Matching of test functions near the identity for a cyclic algebra

`Langlands.BaseChange.CyclicAlgebraNearIdentityMatching`. Namespace `Langlands.BaseChange`.

Proves `CyclicAlgebraNearIdentityMatchingStatement` (`cyclicAlgebraNearIdentityMatching`) by
reduction to the field case `nearIdentityMatching`.

## Statement

- `cyclicAlgebraNearIdentityMatching : CyclicAlgebraNearIdentityMatchingStatement.{u, v}`.

## Proof

Given `F`, `E`, `σ`, `l`, `n`, `μF`, `μE` as in the statement:

1. **Coordinates.** `exists_cyclicAlgebraFieldCoordinates` gives a field `L : Type v` (the residue
   field `E ⧸ 𝔪`), `τ : L ≃ₐ[F] L` with `IsCyclicAlgebra τ d`, `l = (m + 1) d`, and
   `c : E ≃ₐ[F] (Fin (m + 1) → L)` with the shift and wrap rules. `L` is given its module topology
   over `F` (`moduleTopology F L`); it is a topological ring (`IsModuleTopology.isTopologicalRing`)
   and `c`, `c⁻¹` are continuous (`IsModuleTopology.continuous_of_linearMap`, the product topology
   being the module topology). `GL_n(L)` gets its Borel σ-algebra; it is locally profinite and
   second countable (`generalLinear_isLocallyProfinite_of_finiteAlgebra`,
   `generalLinear_secondCountable_of_finiteAlgebra`). `κ = cyclicProductGLCoordinates c hc hc'`.
2. **Measures.** `exists_isHaarMeasure_measurePreserving_pi` gives a Haar measure `μ` of `GL_n(L)`
   with `MeasurePreserving κ μE (Measure.pi fun _ => μ)`. The field theorem
   `nearIdentityMatching` is applied to `(F, L, τ, d, n, μF, μ)`: it holds for every Haar measure of
   `GL_n(L)`.
3. **From `GL_n(E)`.** The field theorem gives `U_L ∈ nhds 1`; van Dantzig's theorem
   (`Topology.LocallyProfiniteProof.vanDantzig`) gives a compact open subgroup `K₀ ⊆ U_L`, and
   `U = κ⁻¹(K₀^{m+1})` is an open neighbourhood of `1`. For `φ` supported in `U`,
   `exists_concordant_ordinary_cyclicProduct` gives `φL` (the fibre integral of `φ ∘ κ⁻¹`) with
   support in `K₀ ⊆ U_L`; its match `f` on `GL_n(F)` is concordant with `φ`.
4. **From `GL_n(F)`.** `V` is the neighbourhood of the field theorem. For `f` supported in `V`, the
   field theorem gives `φL` concordant with `f`, and `exists_concordant_twisted_cyclicProduct`
   gives `φ` (the unit tensor `e_K ⊗ ⋯ ⊗ e_K ⊗ φL` in the coordinates) concordant with `f`.

The case `d = 1` (`L = F` up to isomorphism, `E` split) is not separate: the field theorem holds for
degree one.

## Declarations, in order

`cyclicAlgebraNearIdentityMatching`.

## Literature

The reduction is the one of G. Henniart and B. Lemaire, *Changement de base et induction
automorphe pour GLₙ en caractéristique non nulle*, Mém. SMF 124 (2011), §I.2.6, p. 18, for
functions with regular support, there with the product Haar measure `dg_E = dg_{E₁}^r` on
`G(E) = G(E₁)^r` (§I.2.5, p. 17); here `μE` is any Haar measure and the measure of `GL_n(L)` is
rescaled. Its orbital identity is HL §I.2.4, pp. 15–16, and J. Arthur and L. Clozel, *Simple
Algebras, Base Change, and the Advanced Theory of the Trace Formula* (1989), Chapter 1, §5,
pp. 48–49 ((5.1), (5.2)); the field case is their Chapter 1, §3, Proposition 3.1, p. 20, near the
identity (`nearIdentityMatching`).
