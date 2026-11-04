# Regular operator families under actual character transport

Worker 200. This is an internal derivation from
`UnramifiedCharacterTransport` and `UnramifiedOperatorFamilies`. It adds no
literature assertion or analytic continuation theorem.

## Full norm family and scalar algebra

Let `A` and `B` be groups with arbitrary topologies, let `e : A ≃ₜ* B` be a
multiplicative homeomorphism, and let `ν : I → (A →* ℝ≥0ˣ)` be any indexed
family. The groups and the index type have independent universes. Write `ν'`
for the entire transported family

`ν' j = (ν j).comp e.symm.toMulEquiv.toMonoidHom`.

The existing `unramifiedCharactersHomeomorph e ν`, denoted `E` below, maps a
continuous character `χ` to `χ ∘ e.symm`. The parameter spaces retain their
existing compact-open subspace topologies and common norm kernels.

`unramifiedRegularFunctionsEquiv e ν` is a complex algebra equivalence from
`unramifiedRegularFunctions ν` to `unramifiedRegularFunctions ν'`. Its
evaluation formulas are

`(unramifiedRegularFunctionsEquiv e ν b)(χ') = b(E.symm χ')`

and

`((unramifiedRegularFunctionsEquiv e ν).symm b')(χ) = b'(E χ)`.

In particular the regular evaluation generator at `a : A` maps to the
regular evaluation generator at `e a : B`. This is an equivalence of the
actual evaluation-generated algebras, without substituting a selected lattice
or assuming either algebra is the coordinate algebra of an algebraic torus.

The implemented proof first defines precomposition on the full function
algebras, with inverse precomposition by `E`. The inverse laws follow from
the actual character homeomorphism. The image of every evaluation generator
is the corresponding evaluation at `e a`; every target generator is reached
using `e.symm`. `AlgHom.map_adjoin` therefore identifies the image of the
source generated subalgebra with the target generated subalgebra. Restricting
the full function-algebra equivalence and using that equality gives the
claimed equivalence. Its forward evaluation formula is definitional, and
its inverse formula follows by applying the forward formula to the inverse
identity.

## Exact parameter subsets

For any subset `Ω` of the transported character space,
`unramifiedParameterPreimageEquiv e ν Ω` is the equivalence

`(E ⁻¹' Ω) ≃ Ω`

induced by `E`. Its forward and inverse evaluation formulas expose exactly
`E` and `E.symm`. No openness, nonemptiness or representation-orbit quotient
is required for this subset equivalence.

## Finite expansions and a common denominator

The three equivalences in `UnramifiedOperatorFamily` apply to a vector space
`V` or to operators `V →ₗ[ℂ] W`, with independent carrier universes:

- `isPolynomialOn_transport_iff` identifies polynomiality of `f : Ω → V`
  with polynomiality of its pullback through the exact subset equivalence.
- `isPolynomialOperatorOn_transport_iff` applies that result to every fixed
  input vector.
- `isRationalOperatorOn_transport_iff` identifies rationality of the operator
  family with rationality of its pullback.

For polynomiality, transport each regular coefficient through the scalar
algebra equivalence in the appropriate direction. Keep the same finite
index and the same fixed vectors. The evaluation formulas and the subset
inverse laws prove the equality of the expansions.

For rationality, transport the single common denominator through the same
algebra equivalence. Its nonvanishing is preserved at every corresponding
parameter. The polynomial-operator equivalence then transports the
denominator-cleared numerator. The denominator remains chosen before all
input vectors; it is not chosen separately for different vectors or scalar
evaluations.

These are parameter-transport laws for the existing algebraic predicates.
They construct no standard intertwiner and prove no convergence,
continuation, representation-orbit descent or Plancherel assertion. A
consumer must still identify its actual operator family and parameter region.
