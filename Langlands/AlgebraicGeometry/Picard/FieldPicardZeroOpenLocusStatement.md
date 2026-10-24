# The geometric Picard-zero open locus over a field

`Langlands.AbelianScheme.FieldPicardZeroOpenLocusStatement` is a proposition
definition. For every field `k : Type u`, every `A : AbelianScheme (Spec k)`,
every `P : Over (Spec k)`, and every actual `L : RigidifiedFamily A P`, it assumes
`LocallyOfFiniteType P.hom` and the existing full rigidified universal property

```text
RigidifiedLineBundle.IsUniversal A.X.hom
  (unitSection A) (unitSection_comp A) L.
```

It asserts the existence of an actual open subset `U : P.left.Opens` such that
`IsPicardZeroOpenLocus A L U`. Unfolding the published predicate, this means that
for every test scheme `T : Over (Spec k)` and every actual map `h : T ⟶ P`,

```text
IsPicardZeroClass A
  (RigidifiedLineBundle.classifyingMap A.X.hom
    (unitSection A) (unitSection_comp A) L T h)
  ↔ Set.range h.left ⊆ (U : Set P.left).
```

The classifier is defined by actual rigidified relative pullback of `L`.
The class predicate is the existing geometric-fibre predicate: after passing
to the underlying family on `A ×_k T`, it requires translation invariance of
the line bundle on every algebraically closed field-valued fibre. It is not
redefined here using algebraic equivalence or a connected component.

The field is arbitrary, with no perfectness or algebraic-closedness assumption,
and the declaration is universe-polymorphic in `u`. All test schemes and maps
in the published locus predicate are retained, including nonreduced test
schemes. No projectivity hypothesis on `A`, dual parameter scheme, open locus,
or geometric comparison is supplied as input.

## Original source and derived formulation

The registered original is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft, source ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Paragraph (6.2), printed p.88 (PDF p.92), describes rigidified line bundles,
their actual pullback, and the universal Poincaré bundle. Chapter VI §3,
printed p.95 (PDF p.99), invokes the general representability theory for the
Picard scheme of an abelian variety over a field and identifies its functor
with rigidified line-bundle classes. Theorem (6.18), printed p.96 (PDF p.100),
establishes that the identity component is an abelian variety. Definition
(6.19) on that page defines the dual variety and its Poincaré bundle by
restriction of the ambient bundle.

Corollary (7.22), printed p.106 (PDF p.110), is a scheme-theoretic identification
of `Pic⁰` with the kernel of the map from the Picard scheme to the homomorphism
scheme that assigns a line bundle its associated homomorphism. The description
on printed p.95 sends a point `x` to the class of `t_x^*L ⊗ L⁻¹`.
These passages motivate the geometric translation-invariance criterion.
Corollary (7.22) alone is not a proof of the all-test-scheme statement above.

This target is a derived geometric interface in the Library's chosen
definitions, not a verbatim theorem of the source. The identity component is
a possible construction of `U`, but the statement only asserts an open subset
with the exact displayed criterion.

## Remaining proof and representability obligations

A separate proof must construct the open locus in any specified ambient
universal pair `(P, L)`. A route using the identity component must recover or
transport the relevant Picard-scheme structure from full rigidified
representability, justify openness, and identify geometric membership with the
Library's precise translation-invariance predicate. This includes the needed
base-change and actual pullback comparisons; they are not extra hypotheses.
It must then establish the equivalence for all `T` and `h`, including
nonreduced `T`, using detection on geometric fibres and the open-subscheme
factorization criterion as needed. A classification restricted to geometric
points would not prove this target.

The published `existsUnique_openLocusLift_iff` supplies the exact equivalence
between image containment and unique factorization through the actual open
parameter scheme, but it does not supply the geometric comparison or openness.
Once the asserted locus exists,
`hasDualScheme_of_isPicardZeroOpenLocus` combines it with the assumed ambient
universality to give the existing `HasDualScheme A`.

This file supplies no proof or new axiom. Existence of the ambient locally
finite type universal rigidified pair remains a separate representability
obligation, formulated by `FieldRigidifiedPicardRepresentabilityStatement`;
that statement is not assumed or imported here. Its proof and the proof of
this target are the remaining inputs to the parent field dual-scheme existence
argument. This target makes no additional assertion about the group structure,
smoothness, properness, dimension or projectivity of the open parameter scheme.
