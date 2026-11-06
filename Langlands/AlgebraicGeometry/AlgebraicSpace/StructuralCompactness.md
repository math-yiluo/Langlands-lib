# Absolute and structural quasi-compactness of algebraic spaces

Author: Worker 1640.

This module defines absolute quasi-compactness, structural quasi-compactness
and structural finite type for an actual algebraic space over an arbitrary
scheme base. It imports the published `SpaceBaseChange` and
`StructuralAtlasGeometry` modules by Lean name and reuses their actual base
change and structural local finite type predicate.

## Original sources and specialization

The registered original source is
`stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`, the retained folder
`literature/Stacks Project - Properties of Algebraic Spaces and Morphisms of
Algebraic Spaces, full chapter PDFs (version ed88ff78)/`. Its registered
folder fingerprint is
`cfb36cfc55110aebc6c164e21700e0231c545ae581586883cc1505c67292a90f`.
The original PDFs are version `ed88ff78`, compiled 14 July 2026.

The relevant original passages were read in the PDFs:

- *Properties of Algebraic Spaces*, Chapter 66, Definition 66.5.1,
  [Tag 03E3](https://stacks.math.columbia.edu/tag/03E3), PDF/printed p.8:
  absolute quasi-compactness is existence of a surjective etale map from
  a quasi-compact scheme. This directly supplies `IsQuasiCompact`.
  The file `spaces-properties.pdf` has SHA-256
  `7f71f8371bd2040b4cd3ec6171420ef6a1ce14f7a0a334d32c6d04821e1741bc`.
- *Morphisms of Algebraic Spaces*, Chapter 67, Definition 67.8.2,
  [Tag 03HE](https://stacks.math.columbia.edu/tag/03HE), PDF/printed p.12:
  quasi-compactness of a morphism is defined by all quasi-compact
  algebraic-space test changes. Lemma 67.8.8,
  [Tag 03KG](https://stacks.math.columbia.edu/tag/03KG), pp.13–14,
  condition (3) on p.14, gives the equivalent criterion using every
  affine scheme and every morphism from it to the target.
  `QuasiCompactOverBase` uses this affine-test criterion with target the
  scheme base `S` and with the published actual `baseChange g X`.
- In the same chapter, Definition 67.23.1(3),
  [Tag 03XF](https://stacks.math.columbia.edu/tag/03XF), PDF/printed p.45,
  defines finite type as local finite type together with quasi-compactness.
  This supplies the conjunction `FiniteTypeOverBase`. Lemma 67.23.4(6),
  [Tag 040Y](https://stacks.math.columbia.edu/tag/040Y), on p.45,
  is the actual-atlas criterion underlying the already published
  `LocallyOfFiniteTypeOverBase`; Section 67.23 begins on p.44.
  The file `spaces-morphisms.pdf` has SHA-256
  `46497665981806a93d5b2f315314555ba457aaed3d967bf2d8f0cd4a2310e161`.

The source README was read and both PDF fingerprints were checked. No
source-specific errata note was found in the checked workspace, project
or Library note locations. The adjacent text extractions are reading
aids, rather than separate mathematical sources.

The affine-test definition specializes an equivalent source criterion.
This module does not formalize the general all-algebraic-space-test
definition of a quasi-compact morphism or prove Lemma 67.8.8's equivalence.
Likewise the source's absolute-topology comparison, Lemma 66.5.2
([Tag 03E4](https://stacks.math.columbia.edu/tag/03E4), p.8), is not a
Lean result of this unit.

## Exact definitions

All declaration names below are in
`Langlands.AlgebraicGeometry.AlgebraicSpace`. For arbitrary
`S : Scheme.{u}` and `X : AlgebraicSpace S`, the three Prop-valued
definitions are exactly:

```lean
def IsQuasiCompact (X : AlgebraicSpace S) : Prop :=
  ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf),
    IsEtale a ∧ IsSurjective a ∧ CompactSpace U.left

def QuasiCompactOverBase (X : AlgebraicSpace S) : Prop :=
  ∀ (T : Scheme.{u}) [IsAffine T] (g : T ⟶ S),
    IsQuasiCompact (baseChange g X)

def FiniteTypeOverBase (X : AlgebraicSpace S) : Prop :=
  LocallyOfFiniteTypeOverBase X ∧ QuasiCompactOverBase X
```

The atlas source `U` is an actual scheme over `S`. Its map is a
transformation to the whole underlying presheaf of `X`. The existing
`IsEtale` and `IsSurjective` predicates from `Basic` require represented
scheme pullbacks and etaleness or geometric surjectivity of every
represented projection. In particular `IsSurjective` does not mean
surjectivity on every presheaf component.

`CompactSpace U.left` is topological quasi-compactness of the underlying
scheme: every open cover admits a finite subcover. It carries no
Hausdorff assumption. There is no quasi-compactness condition on the
atlas morphism `a` or on the scheme structure morphism `U.hom` in
`IsQuasiCompact`.

Absolute quasi-compactness is a property of the space itself. Structural
quasi-compactness is a property of its morphism to the base and tests
every affine `T : Scheme.{u}` and every `g : T ⟶ S`. The witnesses for
different base changes may differ. These two predicates are distinct
definitions; no equivalence between them is asserted here.

All base, test and atlas schemes stay in `Scheme.{u}`. The existing
presheaf values are in `Type (u + 1)`. The base and space have no
affineness, noetherianity, reducedness, separatedness or
quasi-separatedness premise. Only the atlas morphisms must be
representable by schemes; no representability of the structural
morphism of `X` is assumed.

## Implemented elementary helpers

The helper names and proofs are internal derived interfaces for the
three definitions, rather than additional source equivalence theorems.

`IsQuasiCompact.of_atlas` constructs the defining witnesses from a
supplied `U`, actual atlas map, etaleness, geometric surjectivity and
`CompactSpace U.left`. `IsQuasiCompact.exists_atlas` exposes exactly
those witnesses by unfolding the definition.

`IsQuasiCompact.of_scheme U` accepts `[CompactSpace U.left]` and
proves quasi-compactness of `((schemeToSpace S).obj U)`. It applies the
published `HasAtlasProperty.of_scheme` with the scheme-morphism
property that its source is compact. That existing helper takes `U`
itself and the identity transformation as atlas; its represented
identity scheme map is etale and surjective. The compact-source premise
supplies the remaining property. This proves only the forward
introduction for a compact scheme.

`IsQuasiCompact.of_iso hX e` composes a witnessing atlas with
`e.hom`, for a whole-presheaf isomorphism
`e : X.presheaf ≅ Y.presheaf`. It uses the published
`IsEtale.comp_iso` and `IsSurjective.comp_iso` to retain the two
geometric properties, and retains exactly the same source scheme
and compactness proof. `IsQuasiCompact.iff_of_iso e` applies that
transport to `e` and `e.symm`.

`QuasiCompactOverBase.affine_baseChange hX T g` evaluates the defining
family at the supplied affine scheme and morphism.
`QuasiCompactOverBase.of_affine_tests` introduces the predicate from
exactly that universal family. These are definition unfolding helpers.

`FiniteTypeOverBase.of_locallyOfFiniteType_quasiCompact` constructs the
conjunction, while `FiniteTypeOverBase.locallyOfFiniteType` and
`FiniteTypeOverBase.quasiCompact` project its first and second
components. They prove no new geometric implication between the two
components.

## Scope

The definitions and elementary helpers form one focused unit.
Represented-scheme converses, comparison with `FiniteTypeOverRing`,
general base-change laws, intrinsic algebraic-space topology and
properness remain subsequent work. In particular the existing
`FiniteTypeOverRing` interface retains its separate atlas-based
definition over an affine ring base; equality or equivalence with
`FiniteTypeOverBase` is not established here.

The module constructs no Picard space, zero part, abelian scheme or
universal family, and supplies no finite-type representability assembly.
