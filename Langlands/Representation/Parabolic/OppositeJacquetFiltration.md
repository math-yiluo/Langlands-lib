# Actual image filtrations in normalized opposite Jacquet quotients

This module constructs finite filtrations on the two actual normalized opposite
Jacquet representations from `Parabolic.OppositeRefinementFunctors`. Each
filtration retains the supplied length and every original index. Its step is
the image of that same original invariant submodule under the actual ordinary
Jacquet quotient map.

## Common algebraic construction

Let `R` be a commutative ring, `G` and `H` groups, `ρ` an `R`-linear
representation of `G` on `V`, `U` a subgroup of `G`,
`f : H →* Subgroup.normalizer U`, and `χ : H →* Rˣ`. The underlying quotient
is `Jacquet.Coinvariants ρ U`, literally the quotient of `V` by the span of
the vectors `ρ(u)v - v`. Its quotient map is `Jacquet.mk ρ U`.
The representation used here is

```text
twist χ ((Jacquet.action ρ U (Subgroup.normalizer U) le_rfl).comp f).
```

Thus `h` acts on the class of `v` by `χ(h) • [ρ(f(h))v]`, where the
normalizer element is viewed in `G`. This construction uses no topology.
The coefficient, ambient-group, acting-group and carrier universes are
independent.

`Jacquet.normalizedImageSubrepresentation U f χ ρ S` has underlying
submodule

```text
S.toSubmodule.map (Jacquet.mk ρ U).
```

To verify invariance, represent a vector in the image by `v ∈ S`. Its
translate has the representative `χ(h) • ρ(f(h))v`, which lies in `S`
by invariance and scalar closure. Linearity of the quotient map identifies
its image with the required translated quotient vector.
The `_toSubmodule` and `mem_normalizedImageSubrepresentation` lemmas expose
the image and its representative formula.

The image construction is monotone. It takes the zero subrepresentation to
zero by linearity, and the full subrepresentation to the full quotient by
`Jacquet.mk_surjective`. `Jacquet.normalizedImageFiltration U f χ ρ s`
uses these facts with `ObjectRepFiltration.ofSubrepresentations`, proving
the inherited monotonicity, zero endpoint and full endpoint in the resulting
filtration itself.

For every original index `k : Fin (l + 1)`,
`normalizedImageFiltration_toSubmodule` states the literal image equality.
`mem_normalizedImageFiltration` states

```text
q ∈ (normalizedImageFiltration U f χ ρ s).subrepresentation k
  ↔ ∃ v ∈ s.subrepresentation k, Jacquet.mk ρ U v = q.
```

The original length `l` is unchanged. No steps are deleted or reordered.
Length zero, repeated steps and zero quotient modules are allowed.

## The two opposite Jacquet specializations

For `F : PadicField p`, `T : F.TopologicalData`, an ordered block shape `B`
and an inner refinement `S`, the namespace `PadicField.TopologicalData`
provides:

- `T.normalizedRefinedOppositeJacquetFiltration B S ρ s`, on
  `T.normalizedRefinedOppositeJacquet B S ρ` for a representation of
  `B.Levi F.Carrier`;
- `T.normalizedComposedOppositeJacquetFiltration B S ρ s`, on
  `T.normalizedComposedOppositeJacquet B S ρ` for a representation of
  `GeneralLinear n F.Carrier`.

The first specializes `U` to the actual inner opposite radical and `f` to
`Geometric.refinedOppositeLeviNormalizer`. The second uses the actual full
composed opposite radical and `Parabolic.composedOppositeLeviNormalizer`.
Both target the published common refined Levi. Their actions are
definitionally the existing normalized actions, on the existing quotient
carriers.

Their `_toSubmodule` lemmas identify each original step with its image under,
respectively, `Geometric.refinedOppositeJacquetMk B S ρ` and
`Parabolic.composedOppositeJacquetMk B S ρ`. The corresponding
`mem_normalized...Filtration` lemmas give the representative membership
formula at every original index.

The scalar character is `Jacquet.inverseHalfCharacter` of the respective
opposite full modulus. The published identities
`T.inverseHalf_refinedOppositeLeviModulus B S` and
`T.inverseHalf_composedOppositeLeviModulus B S` identify these with the
positive half of the corresponding upper full modulus. In the composed case
this is the entire composed upper character, including its outer and inner
factors. The construction therefore preserves the positive upper-half
normalization on the actual lower-radical quotient.

The field and representation-carrier universes are independent. No
positive-rank condition is added; empty shapes and their refinements are
allowed. No smoothness, admissibility, finite dimension, finite composition
length, irreducibility, exactness or supplied graded comparison is assumed.

## Provenance and scope

This is an internal construction from the published ordinary coinvariant
quotient in `Jacquet.Coinvariants`, the scalar action in `Twist.Definitions`,
the finite filtration interface in `Filtration.ObjectDefinitions`, and the
two actual actions in `Parabolic.OppositeRefinementFunctors`. The displayed
submodule image is Mathlib's actual `Submodule.map`; its invariance,
monotonicity and endpoints are verified directly. No separate literal
literature theorem is asserted here.

This unit constructs the fixed image filtrations. Identification of their
graded pieces with Jacquet quotients of the original graded representations
requires a separate statement and proof. It asserts no multiplicity
comparison or irreducible-head conclusion.
