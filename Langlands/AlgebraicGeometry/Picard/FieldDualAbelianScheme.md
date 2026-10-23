# Conditional dual abelian schemes over a field

This module equips the previously constructed dual commutative group
scheme with smoothness, properness and geometric connectedness supplied
by an explicit proof of `FieldDualSchemeGeometryStatement`. It lifts the
actual dual maps to homomorphisms of these abelian schemes.

## Source and provenance

This is a derived construction from `DualGroupScheme`,
`DualGroupSchemeMap`, and `FieldDualSchemeGeometryStatement`. The source
convention is Edixhoven–van der Geer–Moonen, *Abelian Varieties*,
preliminary draft, Chapter VI, Theorem (6.18), Definition (6.19), and
Remark (6.20), printed p.96 (PDF p.100). The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, with SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

The source identifies the dual as the abelian variety `Pic⁰` and defines
the dual homomorphism by pullback of the Poincaré bundle. The present
module implements the final bundling step for the Library's chosen
universal representative. Its geometry is an explicit theorem
hypothesis; the comparison of the exact geometric-fibre functor with
the source's `Pic⁰` is part of that separate theorem's proof obligation.
The source's remark also separates additivity in the original
homomorphism from the existence of each dual homomorphism.

## Inputs

The field `k : Type u` is arbitrary, and `A` is an existing
`AbelianScheme` over the literal `Spec k`. The constructor takes:

- `geometry : FieldDualSchemeGeometryStatement.{u}`, universally
  quantifying fields, abelian schemes and their representability proofs;
- `hA : HasDualScheme A`, the actual all-test-scheme universal
  geometric Picard-zero family property;
- an ordinary line bundle `MA` on the parameter-first relative space
  `dualScheme A hA ×_k A` and an actual module-sheaf evaluation
  isomorphism `poincareFamily A hA ⊗ MA ≅ O`;
- proofs of the seven published fixed-map propositions
  `pullbackTensorComparisonIsIsoStatement`,
  `PicardZeroPullbackStatement`, `PullbackTensorCompositionStatement`,
  `PullbackTensorUnitCoherenceStatement`,
  `ExplicitPullbackTensorAssociativityStatement`,
  `TensorMonoidalLeftUnitorComparisonStatement`, and
  `PullbackTensorSymmetryStatement`.

Each endpoint of a dual map has its own representability proof,
inverse bundle and evaluation. The seven fixed-map propositions refer
to the existing actual pullback, tensor and coherence maps. The
constructor neither proves nor hides their hypotheses.

## Construction and implemented proofs

`fieldDualAbelianSchemeFromEvaluation` uses exactly
`dualCommGroupSchemeFromEvaluation` as its underlying commutative group
scheme. The three geometric fields are the three projections of
`geometry k A hA`. The equality lemmas for `X` and
`toCommGroupScheme` are reflexivity proofs: the actual chosen universal
parameter scheme, multiplication, inverse and origin remain unchanged.
The result is constructed from the existing group operations and the
explicit theorem hypothesis, rather than chosen from arbitrary
abelian-scheme data.

`fieldDualAbelianSchemePointMulEquiv` reuses the multiplicative
Poincaré classification on every test scheme `T` over `Spec k`. Its
application lemma identifies the equivalence with `dualPointClass`.
Thus the constructed object's points classify the actual rigidified
geometric Picard-zero classes; no reducedness restriction on test
schemes is introduced. The original universal family and conventional
Poincaré line bundle are available unchanged from `DualScheme`.

For `f : A ⟶ B`, `fieldDualAbelianSchemeMapFromEvaluation` is the
existing `dualCommGroupSchemeMapFromEvaluation`, viewed in the
abelian-scheme category. Its underlying scheme morphism is exactly
`(dualSchemeMap homPicardZeroPullback f hA hB).left`, by reflexivity.
The identity and reversed-composition equations reuse the corresponding
group-scheme equations, since abelian-scheme homomorphisms are defined
as homomorphisms of their underlying commutative group schemes.

## Scope

The construction is conditional over an arbitrary field. It supplies
neither the geometry theorem nor representability, ordinary inverse
existence, or the fixed-map hypotheses. Arbitrary-base dual geometry,
additivity as `f` varies, rational extension, biduality and polarizations
remain separate obligations.
