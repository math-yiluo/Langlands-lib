# Injectivity of the canonical finite smooth-dual tensor map

Worker 261 formalized this statement and explanation. Worker 624 specified
the target in coordination with Worker 52. Worker 173 supplied the canonical
construction that the statement concerns.

## Statement and exact conventions

`Langlands.FiniteTensor.SmoothDualTensorInjectivityStatement` is one closed
Prop-valued definition. It asserts the following proposition; this module
does not prove it.

Let `ι : Type uI` be any finite type. Let `G : ι → Type uG` be any dependent
family of groups, each with a supplied topology making it a topological
group. Let `V : ι → Type uV` be any dependent family of additive commutative
groups with complex module structures, and let
`ρ i : Representation ℂ (G i) (V i)` be any family of representations.
The three universe levels `uI`, `uG` and `uV` are independent.

Then the published canonical linear map

```text
FiniteTensor.smoothDualTensorMap ρ :
  PiTensorProduct ℂ (fun i => SmoothDual (ρ i))
    →ₗ[ℂ] SmoothDual (FiniteTensor.external ρ)
```

is injective. The scalar ring of that map is `ℂ`, inferred from the type of
`ρ`. `Function.Injective` applies to the underlying function of the linear
map. Equivalently, its kernel is zero; the statement does not say that the
map is an equivalence.

There are no further hypotheses. In particular, the representations need
not be smooth or admissible, and no compact-open cofinality condition is
imposed on any group. No carrier needs to be finite-dimensional or nonzero.
Irreducibility, scalar-endomorphism conditions, countability, local
compactness, separation axioms and analytic conditions are also absent.
Only `[Finite ι]` is required, so the index type may be empty, and any
carrier may be zero. These cases belong to the statement.

`SmoothDual σ` is the smooth-vector submodule of the full algebraic dual of
`σ`, for the contragredient action `(g · ℓ)(v) = ℓ(σ(g⁻¹)v)`. A functional is
smooth when an open subgroup fixes it. No topology is imposed on a carrier
or its dual. `FiniteTensor.external ρ` acts on `PiTensorProduct ℂ V` by
applying `ρ i (g i)` in each slot. Its group is the dependent product
`∀ i, G i`, with the actual product topology of the supplied factor
topologies. The statement installs no replacement topology.

## Existing construction and internal provenance

The only project import is `Langlands.Representation.Tensor.SmoothDual`.
Complex scalar structures come from `Mathlib.Basic.Complex.Basic`. The map
is reused by its published Lean name. This module changes neither that pair
nor any pair it imports.

The published `smoothDualTensorMap_val` identifies the underlying algebraic
functional of `smoothDualTensorMap ρ x`. It is Mathlib's
`PiTensorProduct.dualDistrib`, applied to
`PiTensorProduct.map (fun i => smoothDualPairing (ρ i)) x`. Here each
`smoothDualPairing (ρ i)` is the subtype inclusion of the smooth dual into
the full algebraic dual. Only this construction law is used to explain the
statement. The pure-tensor evaluation and equivariance laws in that pair do
not establish injectivity.

This is an internal derived target from canonical tensor linear algebra. It
is not a verbatim theorem of an external source, and it makes no new external
literature claim. Worker 624 isolated it as a focused algebraic prerequisite.
The intended consumer is the assembly proof of
`Classification.TwistedProductOrdinaryDualClause`. That clause is in the
published `Classification.UnitaryGenericCompatibilityStatement` pair. It is
needed by the tempered quotient coverage task
`e2afd36b-5c1f-461f-882d-86f03e86b9bd`.

Worker 52 searched the current Tensor and Contragredient modules and the
pinned Mathlib file `Mathlib/LinearAlgebra/PiTensorProduct/Dual.lean`. No
injectivity theorem for `smoothDualTensorMap` was found. Fresh TaskHub
searches found no injectivity task. These bounded searches justify a focused
prerequisite; they make no global absence claim.

The separate published
`Langlands.FiniteTensor.SmoothDualTensorSurjectivityStatement` needs
admissibility and factorwise compact-open cofinality. Injectivity needs
neither. The two statements therefore keep different scopes. Neither
supplies a full tensor-dual equivalence, and this statement makes no
surjectivity claim.

## Remaining proof obligations

A later proof must establish the proposition with no extra premises. One
prospective route has three steps.

1. Over the field `ℂ`, each inclusion `SmoothDual (ρ i) → Module.Dual ℂ (V i)`
   is injective and therefore has a linear left inverse. Tensoring the left
   inverses gives a left inverse of the tensor of the inclusions. Hence
   `PiTensorProduct.map (fun i => smoothDualPairing (ρ i))` is injective.
2. The finite algebraic map `PiTensorProduct.dualDistrib` from the tensor of
   the full duals to the dual of the tensor product is injective over a
   field, even for infinite-dimensional ambient modules. One argument puts a
   given tensor in the image of a tensor of finite-dimensional subspaces of
   the factor duals. For each such subspace, finitely many vectors of the
   factor make restriction to their span injective on that subspace.
   Mathlib's `PiTensorProduct.dualDistribEquiv` then applies to these
   finite-dimensional spans. It requires finite free factor modules, so it
   is not a global equivalence for arbitrary carriers.
3. The composite of these two injective maps is the map in
   `smoothDualTensorMap_val`. If two tensors have equal images, their
   underlying functionals agree, since the subtype inclusion is injective.
   The first two steps then make the tensors equal.

Worker 261 searched the pinned Mathlib PiTensorProduct, TensorProduct and
Dual sources and found no injectivity lemma for `PiTensorProduct.map` or
`PiTensorProduct.dualDistrib`. A proof may first
split off such a generic algebraic prerequisite. The empty index and
zero-carrier cases must also be covered.

The proof must not use classification or exhaustion results. Nor may it use
any downstream analytic or classification theorem. No analytic
integrability, central quotient comparison, classification theorem or final
block comparison is assumed or proved here.
