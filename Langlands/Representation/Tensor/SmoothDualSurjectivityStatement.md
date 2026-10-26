# Surjectivity of the canonical finite smooth-dual tensor map

Worker 52 formalized this statement and explanation. Worker 173 specified the
target and supplied the preceding canonical construction.

## Statement and exact conventions

`Langlands.FiniteTensor.SmoothDualTensorSurjectivityStatement` is one closed
Prop-valued definition. It asserts the following proposition; this module
does not prove it.

Let `ι : Type uI` be any finite type. Let `G : ι → Type uG` be any dependent
family of groups, each with a supplied topology making it a topological
group. Let `V : ι → Type uV` be any dependent family of additive commutative
groups with complex module structures, and let
`ρ i : Representation ℂ (G i) (V i)` be any family of representations.
The three universe levels `uI`, `uG` and `uV` are independent.

Assume both of the following.

- Every `ρ i` is `Langlands.IsAdmissible`.
- For every index `i` and every `K : OpenSubgroup (G i)`, there exists
  `L : OpenSubgroup (G i)` whose underlying set is compact and with `L ≤ K`.

Then the published canonical linear map is surjective:

```text
FiniteTensor.smoothDualTensorMap ρ :
  PiTensorProduct ℂ (fun i => SmoothDual (ρ i))
    →ₗ[ℂ] SmoothDual (FiniteTensor.external ρ).
```

Thus every element of the actual target smooth dual has a preimage in the
actual indexed tensor product of the factor smooth duals. This preimage can
be a sum of pure tensors; the statement does not require a single pure tensor.
`Function.Surjective` applies to the underlying function of this linear map.

The Library's `IsAdmissible` definition is exactly smoothness together with
`Module.Finite ℂ (fixedVectors (ρ i) K.toSubgroup)` for every open subgroup
`K`. Smoothness means that every vector is fixed by an open subgroup. Over
the complex numbers, these fixed spaces are finite-dimensional. The
all-open-subgroups convention is retained; it is not replaced by a condition
only on compact open subgroups.

`SmoothDual σ` is the smooth-vector submodule of the full algebraic dual
of `σ`, for the contragredient action
`(g · ℓ)(v) = ℓ(σ(g⁻¹)v)`. No topology is imposed on a carrier or its dual.
`FiniteTensor.external ρ` acts on `PiTensorProduct ℂ V` by applying
`ρ i (g i)` in each slot. Its group is the dependent product `∀ i, G i`,
with the actual product topology of the supplied factor topologies.
The statement installs no replacement topology.

Only `[Finite ι]` is required. The index type may be empty, and any carrier
may be zero. No global finite-dimensionality, nontriviality, irreducibility,
scalar-endomorphism condition, countability, local compactness of the whole
groups, or separation axiom is added to the stated hypotheses.

## Existing construction and internal provenance

The only project import is
`Langlands.Representation.Tensor.SmoothDual`; complex scalar structures
come from `Mathlib.Basic.Complex.Basic`. The construction is reused by its
published Lean name without changing that pair or any imported pair.

The existing map first tensors the inclusions of the smooth duals into the
algebraic duals and then applies Mathlib's `PiTensorProduct.dualDistrib`.
Equivariance and `smoothLift` place the image in the smooth dual of the
external tensor. Its published `smoothDualTensorMap_val` identifies that
underlying functional, and `smoothDualTensorMap_tprod_apply` identifies its
value on pure tensors with the product of the factor evaluations. These
construction and evaluation laws do not establish surjectivity.

This is an internal derived target, rather than a verbatim theorem from an
external source. It isolates the smooth-functional decomposition obligation
in the complete published
`Langlands.Representation.Classification.BlockTensorAnalyticStatement`
pair, under explicit admissibility and compact-open cofinality hypotheses.
That pair's analytic statements and every imported pair are preserved.
No external-literature claim is used to supply a missing proof.

## Remaining proof obligations

A later proof must produce a preimage for every target smooth functional.
One prospective route is to choose a product of compact open subgroups
inside an open subgroup fixing that functional. This requires a proof using
the finite product topology and factorwise cofinality; it is not an extra
certificate supplied as a premise here.

For each such factor subgroup, admissibility makes its fixed-vector space
finite-dimensional. The published
`Smooth.Contragredient.CompactDualityProof` supplies
`Langlands.smoothDualFixedRestriction_bijective`, identifying fixed smooth
functionals with the dual of that fixed-vector space.
`Smooth.Contragredient.AdmissibleDualityProof` supplies the separate smooth
separation, admissibility-of-duals and bidual results under compact-open
cofinality. `Tensor.FiniteProperties` supplies fixed-vector and admissibility
results for the actual finite external tensor. These are reusable
foundations, not a proof of the new surjectivity proposition.

The prospective argument must identify the relevant product fixed space,
decompose its dual using finite-dimensional tensor duality, lift the factor
functionals to smooth functionals on the original carriers, and verify that
their tensor maps to the original functional under precisely
`smoothDualTensorMap`. Pinned Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`,
`Mathlib/LinearAlgebra/PiTensorProduct/Dual.lean`, provides
`PiTensorProduct.dualDistribEquiv` for finite free factor modules. Such an
equivalence may be used on the finite-dimensional fixed spaces; it supplies
no full algebraic-dual factorization for arbitrary ambient carriers.
The proof must cover the empty finite index and zero-carrier cases as well.

No analytic integrability, central quotient comparison, classification
theorem, or final block tensor comparison is assumed or proved here.
Surjectivity is only one prerequisite for the downstream analytic assembly.
