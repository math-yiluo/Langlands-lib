# Actual compact equivariance and infinitesimal cochain identities

This is an internal derived construction from the project's actual archimedean
matrix adjoint action and automorphic operator realizations. Its intrinsic
differentiation obligations are proved here using the existing compact tangent
curves and scalar derivative theorems. It claims no new identification with an
external source.

The ambient representation `ArchimedeanGL.complexCompactRepresentation` is
defined for any field `F : Type u` and rank `n : ℕ`. The cochain constructions
add `[NumberField F]` and use an actual `OperatorRealization F n`, denoted `S`.
The rank and degree may be zero. The coefficient space is the existing complex
module `S.Space`; no topology on this space or on the tensor complexification is
introduced. The private multilinear arguments allow an independent coefficient
universe `v`.

Write

- `L = ComplexLieAlgebra F n = ℂ ⊗[ℝ] RealLieAlgebra F n`;
- `K = standardInfiniteCompact F n`, including every component;
- `k𝕔 = CompactComplexLieAlgebra F n`, the actual complexification of the
  skew-adjoint real matrix Lie algebra;
- `j = compactComplexInclusion F n : k𝕔 →ₗ⁅ℂ⁆ L`;
- `Aᵠ = L [⋀^Fin q]→ₗ[ℂ] S.Space`.

The bracket on the real algebra is `YX − XY` and the adjoint convention is
`Ad(k) X = kXk⁻¹`.

`complexCompactRepresentation` is the genuine representation of the full group
`K` on `L` whose action on `X` is `complexLieConjugation F n k.val X`. The
representation laws follow from the existing conjugation laws. Its apply lemma
states this formula directly.

The source of `S.compactEquivariantLieInclusion q` is the actual submodule

```text
HorizontalAlternating.equivariant
  (complexCompactRepresentation F n) S.compactRepresentation q.
```

Its members are exactly the `f : Aᵠ` satisfying, for every `k : K` and tuple `X`,

```text
f (fun i => Ad(k) (X i)) = S.compactRepresentation k (f X).
```

The target `S.infinitesimalCompactCochains q` is the actual submodule of `Aᵠ`
whose members satisfy, for every `Y : k𝕔` and `X : Fin q → L`,

```text
S.compactLieAction Y (f X) =
  ∑ i, f (Function.update X i ⁅j Y, X i⁆).
```

The action on the left is the previously constructed restriction of the genuine
enveloping differential action. The formula inserts the bracket in the existing
position, so it has no permutation signs. Submodule closure is proved using
linearity of the coefficient action, pointwise addition and scalar multiplication
of cochains, and the finite-sum laws. `mem_infinitesimalCompactCochains` is the
exact membership equivalence.

The key theorem `S.cochain_compact_complex` proves this identity from full
compact equivariance, with no infinitesimal compatibility certificate as input.
The inclusion then sends `f` to the same alternating cochain equipped with this
proved membership. It is complex-linear and injective, and
`compactEquivariantLieInclusion_coe` records preservation of the underlying map.

The implemented proof first treats a real compact direction and a tuple of
complexified real elements. For any infinite and finite adelic coordinates
`a, b`, a private complex-linear functional evaluates `S.toContinuous v` at
`AdelicGL.pair F n a b`. `compactTangentCurve` supplies a curve `c` in `K` through
the identity whose actual matrix derivative is the chosen skew-adjoint direction.
There are two scalar derivatives:

- `S.compactCurve_evaluate_deriv` differentiates compact translation of the fixed
  cochain value, giving scalar evaluation of the actual coefficient Lie action;
- `compactCurve_scalarCochain_deriv` differentiates the cochain on
  adjoint-transformed real input tuples, giving the scalar insertion sum.

Full compact equivariance and `complexLieConjugation_complexify` identify the two
scalar curves. Uniqueness of derivatives and linearity of evaluation prove
`evaluate_cochain_compact_real`. The injective continuous-function realization,
function extensionality and the actual adelic pair projections then prove the
vector equality `cochain_compact_real`. There is no derivative in the abstract
coefficient space.

To pass to arbitrary complex tuples, a private helper bundles the insertion sum
as a complex multilinear map by summing precompositions with a linear operator
in one position at a time. The output-action side is also a multilinear map.
A second private helper proves that such maps agree everywhere if they agree on
all complexified real tuples: induction on the degree uses left currying, and
tensor-product induction in the first input uses
`z ⊗ X = z • complexify X`. The degree-zero case uses uniqueness of the empty
tuple. This proves `cochain_compact_real_complex`. Finally, tensor-product
induction in `k𝕔`, complex linearity of the actual compact inclusion and Lie
action, and linearity in the replaced argument prove `cochain_compact_complex`.

In degree zero the insertion sum is empty, so the identity says that every
cochain value is killed by the complex compact Lie action. No converse from
infinitesimal equivariance to full compact equivariance is claimed. This unit
uses ambient Lie input cochains with coefficients in `S.Space`; it does not
construct algebraic tensor coefficients, reduced horizontal restriction, a
relative differential, square-zero, or relative cohomology. Those remain
separate obligations.
