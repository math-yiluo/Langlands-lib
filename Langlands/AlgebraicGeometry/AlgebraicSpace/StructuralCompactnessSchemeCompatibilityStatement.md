# Structural compactness and finite type on represented schemes

Authors: Worker 1640 and Worker 139, who specified the exact proposition in
the task objective.

This module supplies one Prop-valued definition,
`Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralCompactnessSchemeCompatibilityStatement.{u}`.
It states three compatibility equivalences for schemes viewed as algebraic
spaces. It contains no proof. Its sole import is the published
`Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralCompactness`.

## Exact statement and quantifiers

With `CategoryTheory` and `AlgebraicGeometry` open, the definition in namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace` is exactly:

```lean
def StructuralCompactnessSchemeCompatibilityStatement : Prop :=
  ∀ (S : Scheme.{u}) (U : Over S),
    (IsQuasiCompact ((schemeToSpace S).obj U) ↔
      CompactSpace U.left) ∧
    (QuasiCompactOverBase ((schemeToSpace S).obj U) ↔
      QuasiCompact U.hom) ∧
    (FiniteTypeOverBase ((schemeToSpace S).obj U) ↔
      (LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom))
```

Here `S` is any scheme in universe `u`, and `U : Over S` consists of an
actual scheme `U.left : Scheme.{u}` and its structure morphism
`U.hom : U.left ⟶ S`. There are no affineness, noetherianity, reducedness,
separatedness or quasi-separatedness assumptions on either scheme. The
three equivalences are independent conjuncts and require no extra premise.

The published functor `schemeToSpace S` is the actual scheme embedding.
The presheaf of `(schemeToSpace S).obj U` is `(schemeYoneda S).obj U`,
with values in `Type (u + 1)`. Thus each left side concerns the space
of this particular scheme over this particular base.

## Meaning of the three equivalences

The first conjunct compares absolute quasi-compactness of the embedded
space with compactness of `U.left`. For any space `X` over `S`, the
imported definition `IsQuasiCompact X` requires an actual scheme
`W : Over S` and a transformation
`a : (schemeYoneda S).obj W ⟶ X.presheaf` such that
`IsEtale a`, `IsSurjective a` and `CompactSpace W.left`. For the space
of `U`, the first equivalence says that such an atlas exists exactly
when `U.left` is quasi-compact. `CompactSpace` means that every open
cover admits a finite subcover; it imposes no Hausdorff condition.

The atlas predicates retain their published geometric meanings.
`IsEtale a` and `IsSurjective a` require representability by schemes
and etaleness or geometric surjectivity of the projections in every
represented scheme pullback. The surjectivity condition does not
assert surjectivity of every map on presheaf sections.

The second conjunct compares structural quasi-compactness with the
Mathlib morphism property `AlgebraicGeometry.QuasiCompact U.hom`.
The imported definition is

```lean
QuasiCompactOverBase X =
  (∀ (T : Scheme.{u}) [IsAffine T] (g : T ⟶ S),
    IsQuasiCompact (baseChange g X))
```

This display records the defining formula. Every affine test scheme
and every map from it to `S` is included; different tests may have
different compact atlas witnesses. Only the test scheme `T` must be
affine. The right side of the equivalence is quasi-compactness of the
actual structure morphism, measured by inverse images of compact
open sets under its underlying continuous map. It places no absolute
compactness premise on `S` or `U.left`.

The third conjunct uses the existing definition
`FiniteTypeOverBase X := LocallyOfFiniteTypeOverBase X ∧ QuasiCompactOverBase X`.
It compares that conjunction with the explicit Mathlib conjunction
`LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom`. In particular, the
local finite type property alone is not the right side. The structural
local finite type predicate remains the existing existential etale
geometrically surjective atlas criterion for the structure morphism.

## Current interfaces and provenance

All three structural predicates are imported unchanged from
`StructuralCompactness`. That module already provides
`IsQuasiCompact.of_scheme` for the compact identity-atlas direction,
and isomorphism transport for absolute quasi-compactness.
The `baseChange` construction comes from `SpaceBaseChange`. The published
`baseChangeSchemeIso g U` identifies the embedding of the actual
scheme pullback `(Over.pullback g).obj U` with
`baseChange g ((schemeToSpace S).obj U)`.

The published `StructuralAtlasSchemeCompatibilityProof` supplies
`exists_etale_surjective_of_represented_atlas`, reflecting an atlas of
a represented scheme to an actual etale surjective scheme morphism,
and `locallyOfFiniteTypeOverBase_schemeToSpace_iff`, comparing the
existing structural local finite type predicate with Mathlib's
property of `U.hom`. These explain the interfaces relevant to a later
proof; this statement imports no additional proof module and proves
none of the three equivalences.

The exact three-conjunct package is an internal derived statement about
these Library definitions, their scheme embedding and Mathlib's scheme
properties. It is not a verbatim theorem of the original literature.
The following original passages motivate its content.

## Original sources

The registered source is
`stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`, retained in
`literature/Stacks Project - Properties of Algebraic Spaces and Morphisms
of Algebraic Spaces, full chapter PDFs (version ed88ff78)/`.
The original Stacks Project PDFs are version `ed88ff78`, compiled
14 July 2026. The registered folder fingerprint is
`cfb36cfc55110aebc6c164e21700e0231c545ae581586883cc1505c67292a90f`.

In *Properties of Algebraic Spaces*, Chapter 66, Definition 66.5.1
([Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)), PDF/printed
p.8, defines absolute quasi-compactness by existence of a
quasi-compact surjective etale scheme atlas. Lemma 66.5.2
([Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)), on the same
page, compares that condition with quasi-compactness of the underlying
topological space. The first conjunct specializes this motivation to
the published scheme embedding and the topology of the actual scheme.
The PDF hash is
`7f71f8371bd2040b4cd3ec6171420ef6a1ce14f7a0a334d32c6d04821e1741bc`.

In *Morphisms of Algebraic Spaces*, Chapter 67, Lemma 67.8.1
([Tag 03HD](https://stacks.math.columbia.edu/tag/03HD)) and Definition
67.8.2 ([Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)),
PDF/printed p.12, relate the general quasi-compact morphism condition
to the existing representable-morphism condition. Lemma 67.8.8
([Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)), pp.13–14,
condition (3) on p.14, gives the equivalent criterion using every
affine scheme mapping to the target. For the structural map to `S`,
these are the tests used by `QuasiCompactOverBase`, motivating the
second equivalence for embedded schemes.

In the same chapter, Definition 67.23.1(3)
([Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)), p.45,
defines finite type as local finite type and quasi-compactness.
Lemma 67.23.4(6)
([Tag 040Y](https://stacks.math.columbia.edu/tag/040Y)), also on p.45,
gives the atlas criterion underlying the current structural local
finite type definition. Together with the existing scheme comparison
for local finite type, these motivate the third conjunct.
The morphisms PDF hash is
`46497665981806a93d5b2f315314555ba457aaed3d967bf2d8f0cd4a2310e161`.

Worker 1640 read the source README and the original PDF pages cited
above, checked both PDF hashes, and found no source-specific errata
file in the checked workspace, project or current Library
`notes/errata/` paths. The adjacent text extractions are reading aids.
These citations explain the derived statement and supply no Lean
proof of it.

## Scope and consumer

This unit supplies only the represented-scheme compatibility statement.
Its exact proof is a later successor after independent statement
acceptance and Library publication. General base-change stability for
arbitrary algebraic spaces, comparison with the distinct affine-base
`FiniteTypeOverRing`, intrinsic algebraic-space topology, properness
and Picard geometry remain separate. The statement makes no change to
`StructuralCompactness`, `StructuralAtlasSchemeCompatibility`,
`SpaceBaseChange` or `FiniteTypeOverRing`.

Worker 139 retains finite-type representability assembly in task
`90a7704e-771a-4107-a91a-c67873dd035e`. This proposition supplies a
compatibility target for that consumer and constructs no representer.
