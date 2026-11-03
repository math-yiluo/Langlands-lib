# Actual cover datum from a finite tensor decomposition

Let `k` and `L` be fields in arbitrary universe `u`, with a specified
extension structure. Suppose an actual finite tensor decomposition
`e : L ⊗[k] L ≃ₐ[L] (I → L)` and specified `k`-automorphisms `s i` satisfy
`e (a ⊗ b) i = a * s i b`. Given an actual target descent datum over
`Spec L → Spec k` and a supplied simply connected central cover of that
target over `L`, `Datum.liftFromTensorComponents` constructs an actual
source descent datum and proves that the original covering homomorphism
is compatible with it and the given target datum.

The construction uses `tensorComponent` for the actual double-overlap
components. Their coproduct is an isomorphism, and both structural
projections are isomorphisms by the tensor formula. `tripleComponent`
derives an actual triple-overlap decomposition with isomorphic first
and third endpoints from these double components. The previously proved
`Datum.liftOnFieldComponents` then supplies the component source
comparisons, their lifting equations, the source cocycle and compatibility.
No field-only predicate is applied directly to a nonfield overlap.

The small-index construction uses `I : Type`. For any `J : Type v` with
a `Fintype` instance, `finiteTensorEquiv` reindexes a supplied tensor
algebra equivalence by `Fintype.equivFin J`. Its evaluation at a finite
index is evaluation at the corresponding original index. Thus
`Datum.liftWithTensorDecomposition` and its compatibility theorem accept
a finite index in any universe while leaving the fields in arbitrary
universe `u`. This includes the intended Galois-automorphism indexing type
once the separate finite Galois tensor equivalence is supplied.

This is an internal composition of the actual tensor, component and cover
constructions. The tensor equivalence and its formula, the original
cover and the target datum remain inputs. Existence of a covering group,
effective descent of the constructed datum, semisimplicity of a descended
source and unrestricted field-extension preservation are separate
obligations.
