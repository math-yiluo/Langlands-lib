# Powers near one and a continuity lemma for quotients

Module: `Langlands.Algebra.CentralSimple.LandherrPowNeighborhood`.

- `powSet_mem_nhds`: over a complete nontrivially normed field `K` of characteristic zero
  and for `n ≠ 0`, the set of `n`-th powers of nonzero elements is a neighbourhood of `1`.
  The map `x ↦ xⁿ` has strict derivative `n ≠ 0` at `1`, so by the inverse function theorem
  (`HasStrictDerivAt.map_nhds_eq`) it maps the neighbourhood filter of `1` onto itself; the
  image of the open set `{x ≠ 0}` is therefore a neighbourhood of `1`.
- `ratio_preimage_mem_nhds`: for a continuous map `φ : k → K` into a normed field and
  constants `ρ, κ ∈ K`, if `φ P₀ - ρ φ Q₀ ≠ 0` and
  `κ (φ P₀ + ρ φ Q₀) / (φ P₀ - ρ φ Q₀) = 1`, then for every neighbourhood `U` of `1` the set
  of `(P, Q)` with `κ (φ P + ρ φ Q) / (φ P - ρ φ Q) ∈ U` is a neighbourhood of `(P₀, Q₀)`.
  The quotient is continuous at `(P₀, Q₀)` because its denominator does not vanish there.

## Provenance

Standard analysis over complete fields. In the proof of Landherr's theorem these facts
control local reduced norms. An element close to `1` is an `n`-th power, hence a reduced
norm when `n` is the reduced degree of the algebra. Kneser proves this using the binomial
theorem in *Lectures on Galois Cohomology of Classical Groups* (1969), §5.5, printed
p. 77 (PDF p. 83). The global approximations of a local Hilbert 90 point give quotients
close to `1`.
