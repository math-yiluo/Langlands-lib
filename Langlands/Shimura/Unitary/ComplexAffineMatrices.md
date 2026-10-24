# Complex affine Harris matrices

This internal comparison constructs matrix coordinates of actual affine points
of the iterated complex Harris group. It combines the previously constructed
affine similitude coordinates, matrix splittings, and relative affine section
isomorphism. The comparison is derived from those constructions; it introduces
no additional geometric or comparison assumptions.

## Coefficient change and specialization

Let E be a totally real number field, K a totally complex quadratic extension
of E, and A an E- and K-algebra with the specified rational structure and
tower ℚ → E → A. Let σ be its second-kind involution,
C a `HarrisSignatureCharts σ n Φ`, and b a finite E-basis of A.
For commutative complex algebras S and T with compatible real structures
and towers ℝ → ℂ → S,T, the theorem
`iteratedScalarMatrixEquiv_natural_apply` says that for every complex algebra
homomorphism f : S → T, tensor x in S ⊗_ℝ (ℝ ⊗_ℚ A), and real embedding τ,
splitting x after changing its coefficients by f gives the pair of matrices
obtained by applying f entrywise to both factors of the splitting over S.
The coefficient change uses f restricted to ℝ. The proof is tensor induction:
the pure-tensor case uses the explicit splitting formula and f's scalar
compatibility; the sum case uses additivity, entrywise.

`iteratedScalarMatrixEquiv_complex` identifies the splitting over S = ℂ
with `iteratedComplexMatrixEquiv`, as functions on all iterated tensors.
Its proof again uses tensor induction and the pure-tensor formulas.
These two lemmas allow arbitrary universes for the coefficient algebras
and the basis index.

## Actual affine matrices

Now let D be `CentralSimpleUnitaryData E K A n`, retaining all its E-, K-,
and rational algebra structures and scalar towers, and let C be charts
for its involution. Take a commutative complex algebra T in universe zero
with compatible real and rational structures and the towers
ℝ → ℂ → T and ℚ → ℝ → T. Write X = Spec_ℂ T and G_ℝ,ℂ for
`D.complexRationalGroupScheme`.

For an actual point x : X → G_ℝ,ℂ, `complexAffinePointMatrices C T x`
applies C's iterated scalar matrix equivalence to the underlying tensor
of `D.complexAffineSimilitudes T x`. It is a pair of n-by-n matrices over T
at each real embedding of E. This construction extracts matrices from
the already constructed similitude; it does not retain the scalar multiplier.

`complexAffinePointMatrices_rational` identifies this function with
`C.scalarMatrixEquiv D.totallyRealBasis T` applied to the underlying tensor
of the rational affine coordinates of `D.complexAffineRationalPoint T x`.
The proof rewrites the affine similitude tensor-tower identity, after which
the two sides are definitionally equal.

`complexAffinePointMatrices_sections` identifies the same matrices with
`D.complexPointMatrices C X x` after entrywise application of
`Corepresented.affineSectionsAlgEquiv (CommAlgCat.of ℂ T)` to both factors.
This is the canonical relative affine section isomorphism Γ(Spec T) → T.
The proof specializes coefficient naturality to that isomorphism and to
the actual section-valued similitude. The complex and real structures on
these sections are those coming from the test scheme's structure morphism.
This theorem does not require the rational structure or rational tower on T.

## Embedding labels

Assume additionally `hΦ : IsCMSection E K Φ`, and specialize to T = ℂ.
For any actual affine complex point x and p : (E →+* ℝ) × Bool,
`complexEmbeddingPointMatrices_affine` identifies the embedding-labelled
matrix of the projected rational point at `cmFactorEmbedding Φ p` with
the first affine matrix factor at p.1 when p.2 is true, and the second
factor when p.2 is false.

The proof uses the embedding-factor formula, the rational affine matrix
comparison, and the equality of the scalar and complex splittings.
It establishes the connection between actual affine point coordinates
and the embedding labels used in the Galois calculations.

The explicit cocharacter values and weights in these affine coordinates,
reflex-field conjugacy, complex group-scheme splitting, smoothness,
reductivity, and PEL geometry remain subsequent work.
