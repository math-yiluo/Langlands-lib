# Dependent finite external tensor reindexing and regrouping

Author: Worker 288.

This module constructs actual coordinate group equivalences and representation
equivalences for `Langlands.FiniteTensor.external`. All declarations below are
in `Langlands.FiniteTensor`. The construction is internal product and tensor
algebra; no desired equivalence is supplied as a hypothesis.

## Assumptions and universes

The coefficient ring is `R : Type uR` with `[CommRing R]`. The index types
`I : Type uI` and `J : Type uJ`, the fiber family `K : J → Type uK`, the group
family `H : I → Type uG`, and the module family `V : I → Type uV` have independent
universes. Each `H i` is a group, and each `V i` is an additive commutative group
and an `R`-module. The representations are
`ρ i : Representation R (H i) (V i)`.

Reindexing and the group coordinate constructions require no finiteness.
Tensor regrouping requires `[Finite J]`. The construction works for arbitrary
inner fibers, so in particular it applies with `[∀ j, Finite (K j)]` as in the
finite external tensor application. No `Fintype` structure is required from
callers. Empty outer indices, empty inner fibers, and singleton indices are
included. There are no dimension, irreducibility, admissibility, smoothness,
nonzero-vector, or carrier-topology assumptions.

The original tensor carrier lies in `Type (max uR uI uV)`. The reindexed
carrier lies in `Type (max uR uJ uV)`, and the nested carrier lies in
`Type (max uR uJ uK uV)`. The original product group lies in
`Type (max uI uG)`; the reindexed and regrouped product groups lie in
`Type (max uJ uG)` and `Type (max uJ uK uG)`, respectively. Neither group
universes nor equalities between universes are imposed on the carriers.

## Dependent group coordinates

For `e : J ≃ I`, `reindexGroup H e` is

```text
(∀ i, H i) ≃* (∀ j, H (e j)).
```

Its forward map is `g ↦ fun j => g (e j)`. It uses
`(Equiv.piCongrLeft H e).symm`, with coordinatewise multiplication.
`reindexGroup_apply` gives the forward formula. The inverse is precise about
dependent transport:

```text
(reindexGroup H e).symm g i = e.apply_symm_apply i ▸ g (e.symm i).
```

This is `reindexGroup_symm_apply`. At an image coordinate,
`reindexGroup_symm_apply_image` states that the inverse evaluated at `e j`
is exactly `g j`.

For `e : Sigma K ≃ I`, `regroupGroup H e` is

```text
(∀ i, H i) ≃* (∀ j, ∀ k : K j, H (e ⟨j,k⟩)).
```

It composes reindexing with `Equiv.piCurry`. Its forward formula is
`g ↦ fun j k => g (e ⟨j,k⟩)`, proved by `regroupGroup_apply`.
`regroupGroup_symm_apply` gives the inverse coordinate

```text
e.apply_symm_apply i ▸ g (e.symm i).1 (e.symm i).2.
```

`regroupGroup_symm_apply_image` specializes this to `g j k` at
`e ⟨j,k⟩`. These formulas retain all dependent group transports.

Given only `[∀ i, TopologicalSpace (H i)]`, `reindexGroupContinuous` and
`regroupGroupContinuous` package the same maps as continuous multiplicative
equivalences for the ordinary product topologies. No topological group
instances are needed. Reindex continuity uses `Homeomorph.piCongrLeft`;
regrouping continuity uses coordinate evaluations and the inverse reindexing
homeomorphism. Their `_toMulEquiv` lemmas are definitional equalities to the
algebraic maps, so the group formulas above apply unchanged.

## Construction of the nested linear equivalence

`sigmaRegroupLinearEquiv R K W`, for `W : Sigma K → Type uV`, constructs

```text
PiTensorProduct R W ≃ₗ[R]
  PiTensorProduct R (fun j => PiTensorProduct R (fun k : K j => W ⟨j,k⟩)).
```

The private helper `finRegroup_exists` first constructs an equivalence with its
generator formula by induction on an outer index `Fin n`. For `n = 0`, both
the flat and nested tensors are identified with `R` using
`PiTensorProduct.isEmptyEquiv`; the pure tensor maps to `1` on each side.
For `n + 1`, the explicit private equivalence `sigmaFinSucc` sends the left
summand `k : K 0` to `⟨0,k⟩` and the right summand `⟨j,k⟩` to
`⟨j.succ,k⟩`. Reindexing and `PiTensorProduct.tmulEquivDep.symm` split off
the fiber over zero. `TensorProduct.congr` applies the induction equivalence
to the remaining fibers. The inverse of `headTailLinearEquiv` assembles the
outer tensor. The generator formula follows from the formulas for these
three constructed equivalences.

The private helper `sigmaRegroup_exists` handles arbitrary finite `J` by
choosing `Fintype.ofFinite J` and `Fintype.equivFin J`. It reindexes the flat
tensor using `Equiv.sigmaCongrLeft` and reindexes the outer tensor back from
`Fin (Fintype.card J)`. The public `sigmaRegroupLinearEquiv` selects the
constructed witness with `Classical.choose`; it does not assume an equivalence.
`sigmaRegroupLinearEquiv_tprod` is the proved specification of this witness:

```text
tprod R v ↦ tprod R (fun j => tprod R (fun k => v ⟨j,k⟩)).
```

`sigmaRegroupLinearEquiv_symm_tprod` proves that the inverse sends the displayed
nested family back to `tprod R v`, using the forward formula and the inverse
identity of the linear equivalence.

For `e : Sigma K ≃ I`, `regroupLinearEquiv R V e` first applies
`PiTensorProduct.reindex R V e.symm` and then this Sigma associator. Its
`_tprod` and `_symm_tprod` lemmas state the two formulas

```text
tprod R v ↦ tprod R (fun j => tprod R (fun k => v (e ⟨j,k⟩))),
(tprod R (fun j => tprod R (fun k => v (e ⟨j,k⟩)))) ↦ tprod R v.
```

The inverse formula is deliberately stated on the displayed reindexed family,
as permitted for dependent carriers. Every dependent family of fiber vectors
has this form: uncurry it to Sigma coordinates and use `Equiv.piCongrLeft V e`
to transport it to `I`. Thus no identification of distinct dependent carriers
is implicit in these formulas. The construction uses the genuine nested
`PiTensorProduct` carriers, including their empty cases.

## Representation equivalences and pullback orientation

For arbitrary `e : J ≃ I`, `reindexEquiv e ρ` has type

```text
Representation.Equiv
  ((external ρ).comp (reindexGroup H e).symm.toMonoidHom)
  (external (fun j => ρ (e j))).
```

The action on the original tensor is pulled back along the **inverse** group
map, from reindexed coordinates to original coordinates. Its underlying linear
equivalence is definitionally `PiTensorProduct.reindex R V e.symm`, exposed
by `reindexEquiv_toLinearEquiv`. `reindexEquiv_tprod` sends `tprod R v` to
`tprod R (fun j => v (e j))`; `reindexEquiv_symm_tprod` recovers `tprod R v`
from this displayed family.

For `e : Sigma K ≃ I` and finite `J`, `regroupEquiv e ρ` has type

```text
Representation.Equiv
  ((external ρ).comp (regroupGroup H e).symm.toMonoidHom)
  (external (fun j => external (fun k : K j => ρ (e ⟨j,k⟩)))).
```

Again the pullback is along the inverse group equivalence. Its underlying
linear equivalence is `regroupLinearEquiv R V e`, as exposed by
`regroupEquiv_toLinearEquiv`. `regroupEquiv_tprod` and
`regroupEquiv_symm_tprod` give exactly the two displayed nested generator
formulas above at the representation level.

Both constructors prove intertwining by extensionality of linear maps out of
the indexed tensor product. On pure tensors, `external_tprod`, the forward
linear formulas, and the inverse group formulas at image coordinates identify
both sides. This establishes intertwining on the whole module.
`reindexEquiv_apply_action` and `regroupEquiv_apply_action` explicitly state
these equalities for every tensor. In particular, the latter says

```text
regroupEquiv e ρ (external ρ ((regroupGroup H e).symm g) x) =
  external (fun j => external (fun k => ρ (e ⟨j,k⟩))) g (regroupEquiv e ρ x).
```

The standard `.symm` operations also give inverse representation equivalences
and their intertwining. Since the continuous group maps have definitionally
the same underlying multiplicative equivalences, these representation
constructions also apply to pullbacks written with the continuous versions.

## Provenance and scope

This is an internal construction from product coordinates, empty tensors,
dependent binary tensor splitting, and finite induction. It asserts no new
literature theorem. The existing project modules
`Langlands.Representation.Tensor.Finite` and
`Langlands.Representation.Tensor.FiniteEquivalences` supply the actual external
action and head-tail construction; their files are unchanged.

The pinned Mathlib commit is `5ed2965256430c3649e86755f9576b54eca72435`.
The principal implementation sources are
`Mathlib/LinearAlgebra/PiTensorProduct/Basic.lean` (reindexing, empty tensors,
and dependent binary splitting), `Mathlib/Logic/Equiv/Basic.lean`
(`Equiv.piCongrLeft` and `Equiv.piCurry`),
`Mathlib/Logic/Equiv/Defs.lean` (`Equiv.sigmaCongrLeft`),
`Mathlib/Data/Fintype/EquivFin.lean`, and
`Mathlib/Topology/Homeomorph/Lemmas.lean` (`Homeomorph.piCongrLeft`).
Concrete GL block-size transports and induction comparison are outside this
module.
