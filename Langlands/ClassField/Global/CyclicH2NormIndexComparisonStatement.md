# Conditional cyclic H² norm-index comparison

`Langlands.ClassField.Global.CyclicH2NormIndexComparison.{u, v}` is a
Prop-valued definition in
`Langlands.ClassField.Global.CyclicH2NormIndexComparisonStatement`.
It states the following implication: assuming the two published propositions
`IdeleClassGaloisDescent.{u, v}` and
`IdeleClassNormGaloisProduct.{u, v}`, for every cyclic Galois extension
`E/F` of number fields,

```text
Nat.card H²(Gal(E/F), C_E) ∣ [C_F : N_{E/F}(C_E)].
```

The fields `F : Type u` and `E : Type v` have independent universes. The
quantifiers require `Field` and `NumberField` instances for both fields,
`Algebra F E`, `IsGalois F E`, and `IsCyclic (E ≃ₐ[F] E)`. Their
number-field structures imply finite dimensionality of the extension.
The trivial extension is included.

## Actual objects and exact scope

The left side is precisely
`Nat.card (relativeIdeleClassCohomology F E 2 : Type v)`.
The imported `Cohomology` module defines this as ordinary group cohomology
of the actual additive idele-class representation. Its coefficient group
is the additive wrapper of `NumberField.IdeleClassGroup (𝓞 E) E`,
and the action is the published arithmetic `relativeIdeleClassAut F E`.

The right side is precisely
`(Langlands.Global.AdelicFunctoriality.ideleClassNorm
  (K := F) (L := E)).toMonoidHom.range.index`.
Thus the subgroup is the range of the actual continuous idele-class norm,
viewed as a multiplicative homomorphism. Its index is taken in the actual
idele-class group of `F`. The statement introduces no replacement groups
or arbitrary maps.

The two hypotheses are whole propositions at universes `.{u, v}`,
placed before the field quantifiers. Descent asserts injectivity of the
actual inclusion and identifies its image with the Galois-fixed classes.
Norm compatibility identifies the inclusion of an actual norm with the
product of all relative Galois conjugates.

There is no hypothesis of a Herbrand-quotient formula, H¹ vanishing,
the second inequality, a bound on the norm index, or finiteness of either
the cohomology group or the norm quotient. `Nat.card` is zero on infinite
types, and `Subgroup.index` is zero when the quotient is infinite.
The conclusion is divisibility of these natural numbers with those
conventions; it does not assert their finiteness or positivity.

This module defines the conditional proposition only. It proves neither
the implication nor either of its two hypotheses.

## Derived provenance

This is an internal derived statement extracted from Worker 220's
independently universe-generalized draft theorem
`Langlands.ClassField.Global.H1VanishingProof.card_H2_dvd_normIndex`.
Worker 220 is a coauthor for the reused formulation. The draft and its
paired explanation were read at revision 4 of task
`16fe0104-64f0-48b9-9587-54db9de4c178`; that draft is context, not accepted
proof evidence. This statement is not presented as a verbatim theorem
from the literature.

The derivation motivating the statement uses the finite cyclic cohomology
quotient map
`Rep.FiniteCyclicGroup.groupCohomologyπEven` in degree two. For a generator
`g`, its domain consists of the elements fixed by `g`, which are exactly
the Galois invariants. Descent therefore supplies a surjective homomorphism
from `C_F` to the multiplicative wrapper of `H²(Gal(E/F), C_E)`.
The norm-compatibility hypothesis and
`groupCohomologyπEven_eq_zero_iff` put the actual norm range in its kernel.
Then `Subgroup.index_dvd_of_le`, `Subgroup.index_ker`, and surjectivity give
the stated divisibility. These subgroup-index facts require no finiteness
hypothesis, which explains the scope above.

The supporting Mathlib declarations were inspected in
`Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic`
and `Mathlib.GroupTheory.Index`, at the project's pinned Mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`. The argument just described is
provenance for the statement and a route for its separate proof task;
the paired Lean file contains only the proposition definition.
