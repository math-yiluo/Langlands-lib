# Original-factor equivalence onto the intrinsic smooth tensor slice

Author: Worker 2.

This internal construction identifies the specified original admissible local
factor with the intrinsic locally smooth subrepresentation of its actual
completed automorphic tensor slice. It uses the published exact image equation
and proves the remaining injectivity obligation.

## Genuine inputs and target

The number field `F : Type uF` and local carrier family
`V : FinitePlace F → Type uV` have independent universes. Scalars are complex,
the matrix rank is any natural number, and original carriers have only their
additive-group and complex-module structures as inputs. The construction retains
the genuine supplied `FiniteTensorPresentation P` and invariant positive form
`b` on its actual global realization `S.representation`.

For the specified place `v` and complementary tensor `y`,
`sliceHilbertSmoothRange b v y` is the published intersection of the actual
invariant completed tensor slice with the locally smooth subrepresentation of
`b.completedRepresentation.comp (localInclusion F n v).toMonoidHom`.
Both the carrier and action are inherited from that original global Hilbert
completion; smoothness refers to the inserted finite-local group.

## Construction and implemented proofs

`factorHilbertAlgebraicIntertwiner_injective` proves injectivity of the actual
original-factor map. Its definition composes the canonical inclusion into the
actual extracted factor-form completion with the actual factor Hilbert embedding.
The canonical inclusion is injective by positive definiteness and completion;
the Hilbert embedding is a linear isometry. The proof composes these two published
injectivity results. It needs the explicit nonzero complementary tensor proof,
with no admissibility or irreducibility assumption.

Under the additional `IsAdmissible (ρ v)` input, `factorHilbertSmoothEquiv`
constructs a genuine `Representation.Equiv` from the given `ρ v` onto exactly
`(P.sliceHilbertSmoothRange b v y).toRepresentation`. It applies the generic
constructor below to the actual original-factor intertwiner, the published exact
image equation and the newly proved injectivity law. Its forward intertwiner is
definitionally the published `factorHilbertSmoothIntertwiner`. No separate inverse,
surjectivity or substitute-map compatibility is assumed.

## Generic image-equivalence infrastructure

`Langlands.TensorSmoothRangeAux` works with a monoid and independently sized
complex modules. For an actual intertwiner `f` and specified subrepresentation
`R` with equal underlying image submodules, `rangeRestriction_injective`
proves that the existing codomain restriction remains injective when `f` is:
forget the target subtype in an equality and apply the original injectivity.

`rangeRestrictionEquiv` applies Mathlib's `IntertwiningMap.ofBijective` to this
injectivity and the published generic restriction's proved surjectivity.
`rangeRestrictionEquiv_apply_val` gives the unchanged ambient forward value by
reflexivity. `rangeRestrictionEquiv_symm_apply` states that the original ambient
map of the inverse value is the given target vector; it follows by forgetting the
subtype in the equivalence's right-inverse law. These generic laws apply to the
actual specialization through its definition. No additional specialized concrete
evaluation wrappers are asserted.

## Provenance and scope

This construction is derived internally from the published
`FiniteTensorHilbertSmoothRange`, `FiniteTensorHilbertComponent` and canonical
positive-form completion APIs. Their proofs are reused by import. The module
makes no identification with an unverified original-literature formula.

The equivalence requires the genuine tensor presentation, global positive form,
specified place, nonzero complementary tensor and admissibility. It requires no
irreducibility input. Existence of the presentation or positive form, automorphic
occurrence, canonical normalization and global spectral decomposition remain
separate obligations. The equivalence concerns the algebraic smooth subspace with
its inherited representation; no topology is supplied on the original factor.
