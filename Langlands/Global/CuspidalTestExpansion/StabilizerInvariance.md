# Stabilizer integrals and their invariance

Module `Langlands.Global.CuspidalTestExpansion.StabilizerInvariance` (namespace
`Langlands.Global`).

Let `p : P → G`, `q : Q → G` and `iV : V → Q` with `j = iV ≫ q` a closed immersion and
`V(F) \ V(𝔸)` compact, `w ∈ G(𝔸)` and `Φ : G(𝔸) → ℂ`.

## Declarations

- `stabilizerIntegral p q iV w Φ y`: the integral over `(V(F) ∩ wP(F)w⁻¹) \ V(𝔸)`, with the
  Library's `stabilizerMeasure`, of `v ↦ Φ(w⁻¹ v y)` evaluated at chosen representatives
  (`eisensteinStabilizerIntegrand`). These are the integrals obtained by unfolding the constant
  term of an Eisenstein series (Bernstein–Lapid, *Meromorphic continuation of Eisenstein
  series* (2024), proof of (6.17); `GeometricLemmaUnfoldingStatement`).
- `stabilizerIntegral_adelicPoints_mul`: for `Φ` left invariant under `P(F)`, the stabilizer
  integral is left invariant under `V(𝔸)`.
- `stabilizerIntegral_rational_mul`: for `V` normal in `Q`, `Φ` left `P(F)`-invariant and a
  rational point `x₀` of `Q` with `w⁻¹ q(x₀) w ∈ P(F)`, the stabilizer integral is invariant under
  left translation by `q(x₀)`.
- `isLeftInvariantUnder_join`: invariance under two subgroups gives invariance under their join.
- `stabilizerIntegral_isLeftInvariantUnder`: for `V` normal in `Q` (`hN`) and `Φ` left
  invariant under `P(F)`, the stabilizer integral is left invariant under the subgroup generated
  by `Q(F) ∩ wP(F)w⁻¹` and `V(F)`, which is `(Q(F) ∩ wP(F)w⁻¹) V(F)` since `V(F)` is normal in
  `Q(F)`.

## Proofs

`stabilizerIntegral_adelicPoints_mul` is the argument of
`IsIwasawaCompact.intertwiningIntegral_adelicPoints_mul`: right translation by `u` preserves the
quotient measure, and the integrand at `u y` is the integrand at `y` composed with it
(`eisensteinStabilizerIntegrand_mk`).

For `stabilizerIntegral_rational_mul`, put `δ = q(x₀)`. Conjugation by `δ` (`conjAdelic`)
preserves `V(F)` (`conjAdelic_mem_rationalSubgroup_iff`), hence the normalized Haar measure of
`V(𝔸)` (`measurePreserving_of_preserves`), and also the stabilizer subgroup because
`w⁻¹ δ w ∈ P(F)`. It therefore induces a measure-preserving map of the stabilizer quotient
(`measurePreserving_discreteQuotientMeasure`), and
`Φ(w⁻¹ (δ v δ⁻¹)(δ y)) = Φ((w⁻¹ δ w)(w⁻¹ v y)) = Φ(w⁻¹ v y)`.

`isLeftInvariantUnder_join` uses that the elements under which a function is left invariant form
a subgroup. The last statement combines the two invariances; an element `x` of
`Q(F) ∩ wP(F)w⁻¹` satisfies `w⁻¹ x w ∈ P(F)`.
