# First-factor and singleton equivalences for finite external tensors

Author: Worker 321.

This module constructs actual equivalences for the dependent external tensor
representation `Langlands.FiniteTensor.external`. It is an internal construction
from product coordinates and tensor universal properties. It does not assume
any of the equivalences being constructed. All declarations below are in the
namespace `Langlands.FiniteTensor`.

## Assumptions and universes

The coefficient ring `R : Type uR` is an arbitrary commutative ring. For a natural
number `r`, the groups form a dependent family `H : Fin (r + 1) → Type uG`, and
the modules form a dependent family `V : Fin (r + 1) → Type uV`. Each `V i` is an
additive commutative group and an `R`-module. A representation `ρ i` acts on
`V i` through `H i`. The universes `uR`, `uG`, and `uV` are independent.

Both the indexed tensor carrier and the first-factor binary tensor carrier
lie in `Type (max uR uV)`. The product group lies in `Type uG`; its universe
never enlarges the carrier. In particular, with complex coefficients both
tensor carriers lie in the factor carrier universe. The singleton equivalence
has codomain `V 0 : Type uV` with its given module structure.

The algebraic constructions require no topologies. The continuous group
versions require only a supplied topology on each `H i`, with the ordinary
Pi and binary product topologies. They require neither continuity of group
operations nor a topology on any module. There are no dimension, admissibility,
irreducibility, smoothness, or nonzero-vector hypotheses. The first-factor
construction includes `r = 0`, with an empty indexed tensor as its tail.

## Group coordinates

`headTail H` is the group equivalence

```text
(∀ i : Fin (r + 1), H i) ≃* (H 0 × (∀ j : Fin r, H j.succ)).
```

Its forward map is `g ↦ (g 0, fun j => g j.succ)`, and its inverse is
`(a, b) ↦ Fin.cons a b`. The constructor reuses `Fin.consEquiv` in the inverse
orientation; multiplication is coordinatewise. The lemmas `headTail_apply`,
`headTail_symm_apply`, `headTail_symm_zero`, and `headTail_symm_succ` state these
formulas. Both inverse identities are part of the constructed `MulEquiv`.

`headTailContinuous H` packages exactly this map as a `ContinuousMulEquiv`.
Forward continuity follows from coordinate evaluation and product formation;
inverse continuity is checked coordinatewise using `Fin.cases`. The lemmas
with names beginning `headTailContinuous_` give its underlying `MulEquiv` and
the same forward, inverse, zero, and successor formulas.

For a dependent family on `Fin 1`, `evalOne H` reuses `MulEquiv.piUnique` and
`evalOneContinuous H` combines it with `Homeomorph.piUnique`. Both evaluate at
zero. Their `apply` and `symm_zero` lemmas express this directly. Their
`symm_apply` lemmas describe every inverse coordinate using transport along
`Subsingleton.elim (0 : Fin 1) i`; this transport is necessary for a dependent
family. The underlying `MulEquiv` of the continuous version is definitionally
`evalOne H`.

## Tensor splitting and actions

`headTailLinearEquiv R V` constructs

```text
PiTensorProduct R V ≃ₗ[R]
  V 0 ⊗[R] PiTensorProduct R (fun j : Fin r => V j.succ).
```

The construction first reindexes by `PUnit ⊕ Fin r ≃ Fin (r + 1)`. This private
index equivalence is composed from Mathlib's `Equiv.sumComm`,
`Equiv.optionEquivSumPUnit`, and `finSuccEquiv`. It then uses
`PiTensorProduct.tmulEquivDep.symm` to split the sum of index types, and
`TensorProduct.congr` with `PiTensorProduct.subsingletonEquiv` to identify
the singleton tensor with `V 0`. All families remain dependent.

`headTailLinearEquiv_tprod` proves the generator formula

```text
tprod R v ↦ v 0 ⊗ₜ[R] tprod R (fun j => v j.succ).
```

The proof applies Mathlib's reindex and dependent splitting formulas, then
the singleton formula. `headTailLinearEquiv_symm_tmul` proves the inverse
formula `v ⊗ₜ[R] tprod R w ↦ tprod R (Fin.cons v w)` using injectivity and
the forward formula.

`headTailEquiv ρ` upgrades this linear equivalence to the actual
`Representation.Equiv` from

```text
(external ρ).comp (headTail H).symm.toMonoidHom
```

to

```text
Representation.tprod
  ((ρ 0).comp (MonoidHom.fst _ _))
  ((external (fun j : Fin r => ρ j.succ)).comp (MonoidHom.snd _ _)).
```

The intertwining proof compares linear maps on pure tensor generators. The
formula `external_tprod`, the head-tail coordinate formulas, and
`TensorProduct.map_tmul` make both sides equal. This proves intertwining on
the entire module through the indexed tensor extensionality principle.
`headTailEquiv_apply_action` displays that equality for every tensor and the
action `TensorProduct.map (ρ 0 g.1) (external (fun j => ρ j.succ) g.2)`.
`headTailEquiv_toLinearEquiv`, `headTailEquiv_tprod`, and
`headTailEquiv_symm_tmul` expose the underlying equivalence and both generator
formulas at the representation level.

`singletonEquiv ρ`, for families on `Fin 1`, is an actual
`Representation.Equiv` from

```text
(external ρ).comp (evalOne H).symm.toMonoidHom
```

to `ρ 0`. Its underlying linear equivalence is
`PiTensorProduct.subsingletonEquiv 0`, as stated by
`singletonEquiv_toLinearEquiv`. Intertwining again follows by extensionality
on pure tensor generators and evaluation at zero.
`singletonEquiv_apply_action` states the equality for every tensor.
`singletonEquiv_tprod` sends `tprod R v` to `v 0`, and
`singletonEquiv_symm_apply` sends `v : V 0` to the pure tensor whose dependent
coordinates transport `v` from index zero.

The standard `.symm` operation gives both representation equivalences in the
reverse direction, including inverse intertwining. The continuous group
versions have definitionally the same underlying group homomorphisms as the
algebraic versions, so `headTailEquiv ρ` and `singletonEquiv ρ` also directly
inhabit the types with pullbacks along `headTailContinuous H` and
`evalOneContinuous H`. No additional transport hypotheses are needed.

## Provenance and scope

The source of the constructions is internal product and tensor algebra, with
no external classification result asserted. The pinned Mathlib commit is
`5ed2965256430c3649e86755f9576b54eca72435`. Relevant implementation sources are
`Mathlib/Data/Fin/Tuple/Basic.lean` (`Fin.consEquiv`),
`Mathlib/Logic/Equiv/Fin/Basic.lean` (`finSuccEquiv`),
`Mathlib/Logic/Equiv/Option.lean` (`Equiv.optionEquivSumPUnit`),
`Mathlib/Algebra/Group/Equiv/Basic.lean` (`MulEquiv.piUnique`),
`Mathlib/Topology/Homeomorph/Lemmas.lean` (`Homeomorph.piUnique`), and
`Mathlib/LinearAlgebra/PiTensorProduct/Basic.lean` (reindexing, dependent
splitting, and singleton tensor equivalences). The existing project module
`Langlands.Representation.Tensor.Finite` supplies the external action and
its pure-tensor formula. No existing Lean/Markdown pair is changed.

These equivalences supply a first-factor decomposition and a singleton base
case for later arguments. They do not prove representation factorization,
Flath existence, factorwise cuspidality, or carrier shrinking.
