# Conditional additive dualization over a field

For a field `k : Type u` and abelian schemes `A` and `B` over `Spec k`,
this module bundles the actual contravariant dual maps into additive
homomorphisms. It takes an explicit proof of the published
`FieldDualSchemeMapAdditivityStatement`; it does not prove that statement.

## Inputs

Both endpoints retain their actual universal-family existence proofs
`hA : HasDualScheme A` and `hB : HasDualScheme B`. Each also retains an
ordinary line bundle on the parameter-first relative space and an actual
module-sheaf isomorphism from its tensor product with the Poincare family
to the structure sheaf. These are exactly the inverse/evaluation inputs
used to construct the existing dual group schemes.

The seven explicit fixed-map hypotheses are
`pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorCompositionStatement`,
`PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`,
`PullbackTensorSymmetryStatement`, and
`PicardZeroPullbackStatement`. They describe the existing canonical
comparisons, coherence maps, and preservation predicate; they do not
supply an arbitrary dual morphism or assume its addition law.
The separate `additivity` argument supplies precisely that law at the
underlying scheme level.

## Construction and implemented proof

`fieldDualGroupSchemeMap_add` proves the addition equation for
`dualCommGroupSchemeMapFromEvaluation`. It first uses
`Additive.toMul.injective` and `Grp.hom_ext` to reduce equality to the
underlying scheme maps. Group-homomorphism addition is pointwise
multiplication, whose underlying map uses the cartesian monoidal lift
followed by the constructed dual multiplication. That multiplication is
`dualTensor` after the canonical map to the categorical product.
Applying the supplied additivity statement and simplifying the two
projections identifies this composite with `prod.lift` followed by
`dualTensor`.

`fieldDualGroupSchemeMapAddHom` packages the same function as
`(A ⟶ B) →+ (GB ⟶ GA)`, where `GA` and `GB` are the existing constructed
dual commutative group schemes. `AddMonoidHom.mk'` derives preservation
of zero from preservation of addition and cancellation in the target.
Its application lemma is reflexive, so this is exactly the existing
Poincare-pullback dualization function.

With the additional explicit `FieldDualSchemeGeometryStatement` proof,
`fieldDualAbelianSchemeMapAddHom` has target the Hom group between the
constructed dual abelian schemes, again in reversed order. Their Hom
types are definitionally the same group-scheme Hom types. Its application
lemma identifies it with `fieldDualAbelianSchemeMapFromEvaluation`.
The bundled additive laws consequently include preservation of zero,
addition, negatives, and integer multiples.

## Source, provenance, and scope

The original source is Edixhoven-van der Geer-Moonen, *Abelian Varieties*,
preliminary draft, Chapter VII, Lemma (7.16)(i) and Corollary (7.17),
printed p.104 (PDF p.108). The source gives pullback along a sum in the
relative Picard group and deduces that dualization on Hom group schemes
is a homomorphism. Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
No source errata note was present in the admission Library.

This is a derived conditional bundling construction. The mathematical
comparison with the source on all test schemes, including nonreduced
ones and their rigidifications, remains the obligation of the published
additivity statement. Its separate exact-target proof task is
`b71714f0-c50a-4258-94ac-e065ce455f61`. The geometry statement is also an
explicit input, with a separate proof obligation. This module neither
asserts unconditional representability, inverse existence, additivity,
nor geometry, and gives no arbitrary-base or rational extension.
