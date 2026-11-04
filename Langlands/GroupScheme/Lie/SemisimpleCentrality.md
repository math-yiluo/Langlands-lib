# Central semisimple Lie elements and the whole-group adjoint action

Let `k : Type u` be any field and let `G` be an affine group scheme over
`Spec k`. The actual Lie kernel `lieKernel G k` consists of dual-number
points reducing to the identity. The subgroup functor
`Lie.elementCentralizer G X` tests commutation with the scalar extension
of `X` on every affine refinement of every scheme test.

`Lie.elementCentralizer_eq_top_iff_conjugationDerivation_eq_zero` says that
this entire subgroup functor is the whole group exactly when the global
coordinate derivation `Lie.conjugationDerivation G X` is zero. No smoothness,
connectedness, finite type, or semisimplicity assumption is needed for this
equivalence. If the centralizer is everything, evaluate its defining
conjugation equation at the universal coordinate point: every value of the
derivation vanishes. Conversely, zero derivation makes infinitesimal
conjugation equal the constant lift on every affine test algebra.
Applying this to each affine refinement gives the whole subgroup functor.

Assume now that `G` is smooth and connected and that
`Lie.IsSemisimpleElement G X` holds. Semisimplicity uses the existing
definition tested by the differentials of every finite dimensional
algebraic representation, after extension to an algebraic closure.
The principal result is

```text
Lie.elementCentralizerLie G X = top
  iff Lie.elementCentralizer G X = top.
```

The proposition `SemisimpleCentralityStatement.{u}` quantifies over all
such fields and groups, and `semisimpleCentrality` proves precisely this
proposition. It imposes no perfectness or characteristic restriction.

For the forward implication, use the existing actual closed representative
`Lie.elementCentralizerGroup G X`. The published semisimple-centralizer
smoothness theorem makes this representative smooth. Its tangent submodule
is the range of the linear tangent map of its inclusion. Full Lie
centralizer therefore gives a surjective tangent map.
`lieSubgroupEquality` applies to the smooth closed representative and the
connected smooth affine ambient group, and proves that the inclusion has
full range on every scheme test. Its representing identity then identifies
the centralizer functor with the whole group. The reverse implication
follows directly from the definition of the tangent submodule.

Combining these equivalences gives
`Lie.elementCentralizerLie_eq_top_iff_conjugationDerivation_eq_zero`
for semisimple `X`. The result compares Lie centrality, whole-group
adjoint invariance, and a zero global coordinate derivation. It does not
construct an infinitesimal subgroup or a quotient by such a subgroup,
nor does it prove the arbitrary-field `NoTorusUnipotentStatement`.

Provenance is internal and derived from the actual centralizer
representability, semisimple smoothness, represented-subgroup tangent
range, smooth full-Lie-subgroup equality, and universal coordinate
conjugation results imported in the Lean file.
