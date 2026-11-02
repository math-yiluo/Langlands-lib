# Joint continuity of the completed actual compact action

Let `F` be a number field in any universe, let `n` be any natural matrix rank,
and let `S` be an actual `OperatorRealization F n`. Its vectors are actual
stable automorphic functions, and its compact representation is the restriction
of their positive right-translation action to `standardInfiniteCompact F n`.
Let `b : S.UnitaryForm` be a supplied positive definite form invariant under
the finite and compact actions and skew under the genuine real infinitesimal
operators.

`functionRealization` is the complex-linear map sending a vector to its actual
scalar function on the full adelic matrix group. It composes `S.toContinuous`
with the underlying function evaluation. Its injectivity follows from the
injectivity of `S.toContinuous` and the two subtype inclusions.

`continuous_functionRealization_compactOrbit` proves, for every vector `f`
and every full adelic matrix `x`, continuity of

```text
k ↦ f(x · ofInfinite(k)).
```

This is the existing actual compact-translation formula. The underlying
function is continuous, the inclusion of the infinite adelic factor is a
continuous group homomorphism, and multiplication by the fixed `x` is
continuous for the existing group topologies.

`completedCompactContinuousAction b` constructs a continuous map

```text
standardInfiniteCompact F n × b.finiteForm.HilbertCompletion
    → b.finiteForm.HilbertCompletion.
```

Its value at `(k, v)` is `b.compactForm.completedRepresentation k v`.
The compact form retains exactly the positive core of `b.finiteForm`, so the
source and target here are the same actual Hilbert completion used for finite
translation, with the same inner product and dense embedding. No comparison
map or second positive form is chosen. All representation, inverse, norm and
embedded-vector formulas are those of the published positive-form completion.
In particular the dense embedded vector `f` is sent to the embedding of its
actual compact translate.

The construction applies the accompanying
`completedContinuousActionOfFiniteEvaluations` adapter. The published
`S.compactRepresentation_isFiniteVector` proves the finite-dimensional
algebraic orbit hypothesis for every actual vector. The faithful function
realization and the scalar continuity theorem above supply the other inputs.
The adapter first proves form-norm continuity on each finite orbit, then uses
density and the common isometry bound to prove joint continuity on the full
completion. It requires no bounded evaluation functional on the completion.

This is an internal construction from the published actual operator,
compact-finiteness and positive-form completion APIs and the accompanying
finite-orbit continuity argument. It asserts no new identification with
original literature. The form is supplied; its existence on an arbitrary
realization remains a separate obligation. Extension to the full infinite
adelic group, recovery of smooth vectors, differential-operator domains and
spectral occurrence are not constructed here.
