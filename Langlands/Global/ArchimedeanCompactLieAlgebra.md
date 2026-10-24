# The compact matrix Lie algebra and Cartan decomposition

Author: Worker 16. Module: `Langlands.Global.ArchimedeanCompactLieAlgebra`.
All declarations below are in `Langlands.Global.ArchimedeanGL`.

For every `K : Type u` with `Field K` and every natural rank `n`, this module
constructs the compact matrix directions inside the published
`RealLieAlgebra K n`. This includes all number fields in arbitrary universes
and rank zero. None of the constructions require a nonempty matrix index
set or a nonzero dimension. The field-only scope is an algebraic generalization:
the number-field assumption is needed elsewhere for the analytic model.

## Involution and coordinate meaning

The published carrier is the matrix algebra over the product of the real
coordinates at real infinite places and complex coordinates at complex infinite
places. Its fixed Lie bracket is the matrix commutator `XY - YX`.
The new star, additive-star and real-star-module instances on this synonym
are inherited from that actual matrix algebra. Matrix star transposes the
indices and applies coefficient star, which is the identity on the real
coordinates and conjugation on the complex coordinates. Local associative
ring instances are used only to prove the commutator identities; the existing
Lie bracket is retained.

`cartanInvolution` is a real Lie algebra equivalence with
`cartanInvolution K n X = -star X`. Its inverse is the same map, and
`cartanInvolution_involutive` proves that applying it twice returns `X`.
The entry formulas `cartanInvolution_real` and `cartanInvolution_complex` are
respectively

- `theta(X)ᵥ(i,j) = -Xᵥ(j,i)` at a real place;
- `theta(X)ᵥ(i,j) = -conj(Xᵥ(j,i))` at a complex place.

Real linearity follows from the star-module laws and trivial real conjugation.
Bracket preservation uses reversal of products by star:
`-star(XY-YX) = [-star X,-star Y]`.

## The two eigenspaces and their direct decomposition

`compactLieSubalgebra K n` is an actual `LieSubalgebra` over the reals whose
carrier is exactly `star X = -X`. It is the `+1` eigenspace of the involution,
as proved by `mem_compactLieSubalgebra_iff_fixed`.
`mem_compactLieSubalgebra_iff_coordinates` identifies its membership with
skew symmetry at every real place and skew-Hermitian symmetry at every
complex place. The latter condition includes complex conjugation; it is not
the complex bilinear-form orthogonal Lie algebra.

`cartanComplement K n` is the real submodule defined by `star X = X`.
It is the `-1` eigenspace by `mem_cartanComplement_iff_neg`.
`mem_cartanComplement_iff_coordinates` gives the corresponding symmetric
and Hermitian entry conditions.

The linear maps `compactProjection` and `cartanComplementProjection` have
values `(1/2) • (X - star X)` and `(1/2) • (X + star X)`, respectively.
`cartanDecomposition` packages them as a real linear equivalence

`RealLieAlgebra K n ≃ₗ[ℝ] compactLieSubalgebra K n × cartanComplement K n`.

Its inverse sends `(A,B)` to `A+B`, as stated by
`cartanDecomposition_symm_apply`. Thus this is a direct decomposition,
including uniqueness, rather than just an expression as a sum.
`compactProjection_add_cartanComplementProjection` explicitly states the
sum formula. The implementation reuses Mathlib's
`skewAdjointPart`, `selfAdjointPart` and `StarModule.decomposeProdAdjoint`,
with the product factors exchanged to put the compact factor first.

The three closure laws are:

- `compactLieSubalgebra_lie`: `[k,k]` belongs to `k`;
- `compactLieSubalgebra_lie_cartanComplement`: `[k,p]` belongs to `p`;
- `cartanComplement_lie`: `[p,p]` belongs to `k`.

They follow directly from the commutator formula, product reversal by star,
and the specified signs of the two eigenspaces.

## Complex inclusion and compact enveloping subalgebra

`CompactComplexLieAlgebra K n` is the actual tensor product
`ℂ ⊗[ℝ] compactLieSubalgebra K n`, with Mathlib's scalar-extension Lie bracket.
`compactComplexInclusion` is a complex Lie homomorphism to the existing
`ComplexLieAlgebra K n`. It extends the real subtype inclusion, and
`compactComplexInclusion_tmul` states exactly

`compactComplexInclusion K n (z ⊗ X) = z ⊗ (X : RealLieAlgebra K n)`.

Bracket preservation is inherited from `LieAlgebra.ExtendScalars.map`.
`compactComplexInclusion_injective` follows because scalar extension by the
real vector space `ℂ` preserves the injective real subtype map, using
`Module.Flat.lTensor_preserves_injective_linearMap`. Thus the complexified
compact algebra is embedded in the entire published complexification,
which retains both real directions of each complex-place coefficient.

`compactEnvelopingGenerator` composes this inclusion with the existing
canonical map `envelopingGenerator` into `EnvelopingAlgebra K n`.
`compactEnvelopingGenerator_tmul` gives its elementary-tensor formula.
`compactEnvelopingSubalgebra` is the complex unital subalgebra

`Algebra.adjoin ℂ (Set.range (compactEnvelopingGenerator K n))`.

`compactEnvelopingGenerator_mem` proves generator membership.
`compactEnvelopingSubalgebra_le_iff` states the exact minimality property:
for every complex subalgebra `A` of the ambient enveloping algebra, the
constructed subalgebra is contained in `A` if and only if `A` contains every
`compactEnvelopingGenerator K n X`. These laws are the subset and universal
containment properties of algebraic generation. No injectivity of the map
into the enveloping algebra, or identification with an independently
constructed universal enveloping algebra of the compact Lie algebra, is
asserted.

## Original source and derived provenance

Harish-Chandra, *Representations of a semisimple Lie group on a Banach space I*,
Transactions of the American Mathematical Society **75** (1953), 185–243,
printed p.187 (one-based PDF3), describes the `+1` and `-1` eigenspaces of a
Cartan involution and the three bracket containments. Printed p.191 (PDF7)
defines the subalgebra of the ambient enveloping algebra generated by the
unit and the complexified compact Lie algebra. The present module realizes
these algebraic objects explicitly for the mixed archimedean matrix carrier,
using negative transpose and negative conjugate transpose. It is a derived
matrix construction, not a formalization of the source's general existence
theorem for semisimple Lie algebras.

Registered source: `provided-3653f29ecd116fbb8becf37a078787d768f76f5b4bc4b075c85b5b9647628636`.
Retained PDF: `/home/taskhub/pilot/literature/Harish-Chandra, Representations of a semisimple Lie group on a Banach space I, Trans. AMS 75 (1953).pdf`.
SHA256: `c18c739a9344ee9d3860d6683ebf78997c7e0e3588d3156ece27491793cfa2d1`.
Worker 16 verified the fingerprint and read printed pp.187–191 and 195
(PDF3–7 and PDF11), with visual checks of the Cartan formulas and Theorem 1.
No source-specific errata file was found in the available project or Library notes.

The source begins with semisimple Lie algebras; the general linear matrix
carrier has central directions. This module proves no semisimplicity,
reductivity, global group Cartan decomposition, or differential identification
with the tangent Lie algebra of `standardInfiniteCompact`. It also constructs
no exponential, compact-type projection, admissibility or reproduction theorem.
The source's Theorem 1 on p.195 asserts finite generation over the ambient
center under its specified hypotheses, not immediate finite-dimensionality.
Applying that theorem here would require further structural results and a
finite-codimensional center-ideal bridge. No such assumptions or finiteness
certificates are built into this subalgebra.
