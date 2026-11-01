# Tensor presentations and actual local slices of automorphic quotients

This internal construction takes a supplied genuine tensor equivalence onto
the finite adelic action of an actual automorphic operator quotient. It
constructs local invariant slice ranges inside that quotient, proves their
generation and equivalence properties, and, for a nontrivial quotient, derives
nonzero local components and their smooth classes.

## Inputs and conventions

The number field `F : Type uF` and the family of complex vector spaces
`V v : Type uV` have independent universes. The rank `n : ℕ` is arbitrary.
For every finite place, `ρ v` represents the actual completed-local group
`FiniteLocalGL F n v`. The finite set `E`, reference family `e`, and law `he`
are the published restricted tensor inputs: outside `E`, `e v` is fixed by
the actual local integral subgroup. No topology or finite-dimensionality
is imposed on the vector carriers.

`Q : OperatorSubquotient F n` retains an actual invariant numerator of
automorphic forms and an invariant denominator. Its carrier `Q.Space` is
their genuine module quotient, with the published induced finite adelic action
`Q.finiteRepresentation` and its smooth local restriction.

`OperatorQuotientTensorPresentation F n ρ E e he Q` stores two inputs:

- `reference_nonzero` proves that `e v` is nonzero outside `E`.
- `equiv` is a genuine complex-linear representation equivalence from the
  published restricted tensor action to `Q.finiteRepresentation`.

The equivalence, including its bijective linear map, is supplied data. This
module does not assert that every quotient has such a presentation. The
target is the existing actual quotient, not a replacement carrier defined
by an automorphic occurrence condition. The actions retain the published
positive right translation convention.

## Whole local comparison and slice ranges

`restrictedEquiv v` restricts the given equivalence along the actual local
inclusion, keeping its entire carrier. `localEquiv v` composes this with
inverse published tensor separation. It is a genuine representation
equivalence

```text
V v ⊗[ℂ] LocalTensorTail F E v e ≃ Q.localRepresentation v,
```

where the source action acts on the first factor only. `localEquiv_apply`
identifies the map with reassembly followed by the supplied `equiv`.
The full complementary tensor space remains present.

For any complementary vector `y`, `localSlice v y` is the actual intertwiner
`x ↦ P.localEquiv v (x ⊗ y)`. Its invariant range `slice v y` is a
`Subrepresentation` of `Q.localRepresentation v`, on the actual quotient
carrier. This construction requires no nonzero condition.

If `y ≠ 0`, `localSlice_injective` first uses injectivity of `localEquiv`
and then applies a dual functional taking value one on `y` to recover the
first tensor coordinate. `sliceEquiv` uses the resulting injective linear
map and its covariance to give a genuine equivalence from `ρ v` onto the
actual range. `coe_sliceEquiv` records its underlying quotient-vector formula.

`top_le_iff_slices_le` states that an invariant quotient subspace contains
the entire locally restricted carrier precisely when it contains every
slice. Surjectivity of `localEquiv` and algebraic tensor induction prove
the reverse implication: pure tensors belong to their corresponding slices,
and sums remain in the supplied submodule.

`slice_isSmooth` uses the injective subtype inclusion into the already smooth
local quotient action. `sliceSmoothRepresentation` bundles that action and
`sliceClass` takes its actual categorical smooth isomorphism class, with
representative carrier in universe `uF`. These definitions also cover zero
tails. `sliceClass_eq` compares nonzero tails in any two presentations of
the same `V, ρ, E, e, he`, possibly into different actual quotients: composing
the inverse first slice equivalence with the second gives the categorical
isomorphism. Equality of the embedded slice subspaces is not claimed.

Outside `E`, `slice_exists_integral_fixed` transports `e v` through the
nonzero-tail slice equivalence. Its injectivity proves that this vector is
nonzero; covariance and `he` prove that the actual integral subgroup fixes it.

## Components of a nontrivial presented quotient

The remaining constructions assume `[Nontrivial Q.Space]`.
`exists_nonzero_localTensor` lifts a nonzero quotient vector through
`localEquiv`. `exists_nonzero_localFactor` and `exists_nonzero_tail` then
argue by tensor induction: if either factor had only the zero vector,
every tensor would vanish. The local-factor conclusion includes the
exceptional places, where no nonzero reference vector was assumed.

`localFactor_isSmooth` uses a derived nonzero tail and the corresponding
injective slice into the smooth quotient action. `chosenTail` selects a tail
from its proved existence theorem, with `chosenTail_nonzero` recording that
property. `localComponent` is its actual slice, and `localComponentEquiv`
identifies the specified local factor with that slice. A nonzero local-factor
vector and injectivity prove `localComponent_ne_bot`.

`localComponentClass` is the smooth class of the selected slice.
`localComponentClass_eq_slice` proves equality with the class obtained
from any nonzero tail. `localComponentClass_eq` proves equality for any
two nontrivial quotient presentations of the same tensor data. Finally,
`localComponent_exists_integral_fixed` specializes the fixed-vector theorem
to the chosen tail outside `E`.

## Provenance and scope

There is no new original-literature identification. This is an internal
extension of the published embedded-form tensor presentation route to the
existing actual operator quotients. It directly imports `OperatorSubquotient`
and `Global/FiniteAdelicGL/LocalTensorSeparation`. It reuses the genuine tensor
equivalence, smoothness of the actual quotient and injective transfer of
smoothness, Mathlib invariant ranges and injective linear equivalences, and
the dual-functional argument already implemented in `TensorRealization`.
The nonzeroness and generation results use algebraic tensor induction; the
class results use genuine categorical isomorphisms.

No function evaluation or topology is defined on quotient vectors. No
factorization existence theorem, irreducibility or admissibility of the local
factors, uniqueness across different factor families, one-dimensional fixed
space, Satake identification, cuspidal characterization, or spectral existence
is asserted. A single slice is not identified with the whole local restriction.
