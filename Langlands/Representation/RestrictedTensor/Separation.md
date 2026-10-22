# Finite-factor separation and reassembly

This module constructs finite-factor separation and reassembly for the actual
algebraic restricted tensor product, over an arbitrary field with independent
coefficient, index and local-carrier universes. It uses the finite tensor
splitting from `Basic` and the coherent changes of finite exceptional set from
`Maps`. Local vector spaces may be infinite dimensional.

For an exceptional set `E`, any finite set `A` to be exposed, and reference
family `e` nonzero outside `E`, `finiteSeparation` is a genuine linear
equivalence

```text
Space K V E e ≃ₗ[K]
  Stage K V A ⊗[K]
    Space K (fun i : Outside A => V i) (tailSet A E) (fun i => e i).
```

There is no condition that `A` contain `E`. The complementary tensor product
retains exactly the original exceptional indices outside `A`. In particular,
no nonzero reference vector is required at an originally exceptional index.
`productSeparation` gives the same construction with `ReferenceVectors` and
`Product` on both sides. `localSeparation` specializes to `A = {i}` and
uses Mathlib's singleton tensor equivalence to expose the actual local
vector space `V i`.

## Construction and inverse

`Outside A` is the genuine complement index type. `tailSet A S` retains the
part of a finite stage outside `A`. `complementIndexEquiv` swaps two nested
subtype conditions without changing the underlying index. `splitFinite`
uses this equivalence to reindex the finite-stage splitting from `Basic`.

`splitToTailStage` sends the complementary factor to its actual direct
limit. `splitToTailStage_transition` proves compatibility with every
adjoining-reference transition by its elementary-tensor formula. The
universal lift gives `splitToTail`. Canonical exceptional-set changes then
give `splitWithExceptions`, whose domain has exceptional set `E ∪ A`
and whose complementary target has exceptional set `tailSet A E`.
`splitWithExceptions_of` identifies its restriction to every finite stage.

`splitWithExceptions_injective` proves injectivity under the original
nonzero-reference hypothesis. Every source vector has a finite-stage
representative. On that stage, splitting is a finite tensor equivalence
followed by the identity tensored with a complementary stage embedding.
The latter embedding is injective by `Basic.of_injective`. Tensoring
preserves its injectivity because vector spaces over a field are flat;
the pinned Mathlib theorem `TensorProduct.map_injective_of_flat_flat`
is applied with the existing field-module instances. This introduces no
freeness or finite-dimensionality hypothesis in the exported theorem.

`joinSet` and `joinVector` explicitly assemble a finite family in `A` and
a finite complementary family. `splitWithExceptions_joinVector` evaluates
the splitting of their assembled elementary tensor. It proves equality
of complementary representatives using the direct-limit common-stage
criterion. `splitWithExceptions_surjective` then proves surjectivity
by elementary-tensor induction and closure of the range under addition
and scalar multiplication. Surjectivity alone needs no nonzero hypothesis.

`finiteSeparation` combines the canonical change from `E` to `E ∪ A`
with the linear equivalence obtained from this proved bijectivity.
`reassemble` is its inverse. Its existence is therefore derived from the
actual maps and their proved properties, not assumed as structure data.
`reassemble_separate` and `separate_reassemble` prove the two inverse
identities. `reassemble_tmul_pure` characterizes the inverse by the explicit
`joinVector` formula.

## Coherence and reusable formulas

`finiteSeparation_pure` evaluates separation on every finite stage
containing `A`; any stage can be enlarged to such a stage. Together with
the direct-limit transition identity, this makes the formula independent
of the representative. All finite families are indexed by finite sets;
no enumeration or ordering is chosen.

`regroup` changes the finite family being exposed by reassembly followed
by separation. `regroup_refl`, `regroup_trans`, and `regroup_separate`
prove identity, successive-regrouping coherence, and agreement with direct
separation. Thus exposing `A`, regrouping to `B`, and then to `C` agrees
with the direct regrouping from `A` to `C`.

`tail_preserves` restricts cofinite reference-preservation to the
complementary index type. `finiteSeparation_natural` proves that separation
commutes with every cofinite reference-preserving family of component
linear maps: the target operator is the ordinary finite tensor map on
`A` tensored with the induced restricted tensor map on the complement.
Source and target exceptional sets may differ. `reassemble_natural`
proves the inverse square. Taking identity component maps includes
coherent changes of exceptional sets and finitely many reference vectors.

`ReferenceVectors.tail` restricts the original prescribed nonzero-vector
data to the complement; `tail_family` proves equality with the restricted
total reference family, including its zero-filled exceptional coordinates.
`localSeparation_pure` explicitly evaluates the separated local coordinate.

## Relation to the other construction modules

All names in this table are in `Langlands.RestrictedTensor`, except for
the published predicate `Langlands.IsSmooth`.

| Construction | Implemented interface |
| --- | --- |
| Finite tensor system and actual algebraic direct limit (`Basic`) | `Stage`, `transition`, `Space`, `ReferenceVectors`, `Product`; transition identity/composition, `of_eq_iff`, `exists_of`, `lift`, `hom_ext`, `pure_extend`, `span_pure`, and `reference_of_injective` |
| Cofinite component maps (`Maps`) | `map`, finite-bound independence, `map_pure_of_preserves`, `map_id`, `map_comp`, and component equivalence `congr` |
| Exceptional-set and reference changes (`Maps`) | `change`, `change_refl`, `change_trans`, `changeExceptional`, and `change_natural` |
| Full-limit separation (this module) | `finiteSeparation`, `productSeparation`, `localSeparation`, `reassemble`, `regroup`, their elementary formulas, inverse and composition laws, and component-map naturality |
| Genuine restricted-product representation (`Action`) | `RestrictedGroup`, `representation`, `productRepresentation`, elementary action formulas, and `map_intertwines` |
| Smoothness (`Smooth`) | `isSmooth_representation` and `isSmooth_productRepresentation`, proved for `Langlands.IsSmooth` from local smoothness and open reference subgroups |

The algebraic constructions require no topology on the local vector spaces.
The smoothness results require only openness of the given reference subgroups,
so compact-open reference subgroups are included. These constructions do not
include the separate representation-theoretic factorization and local-factor
uniqueness theorems.

## Provenance and limits

These are intrinsic algebraic consequences of Flath (1979), section 2,
printed pages 180–181: the finite-stage direct-limit construction on page
180, its elementary-tensor spanning property, and the component-map
construction numbered (1) on page 181 (one-based PDF pages 176–177).
The detailed inverse, coherence and flatness arguments above describe the
implemented proof, rather than attributing separate numbered theorems to
Flath.

Registered original `flath-1979-tensor-products`, Corvallis Part I PDF,
SHA-256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
Mathlib's `TensorProduct.directLimitRight` was inspected, but its carrier uses
`Module.DirectLimit`, a different quotient model from this construction's
`DirectLimit`. The present maps therefore use the already proved universal
linear lift directly, followed by the proved injectivity and surjectivity.
No tensor/direct-limit commutation law is assumed.

There is no Hilbert completion, admissibility result, irreducibility claim,
automorphic factorization, or uniqueness of local representation factors.
Those representation-theoretic results are separate obligations. This module
only separates and reassembles factors of the algebraic tensor product
already constructed from a specified family.
