# An abelian-scheme parameter for universal smooth-family classes

Statement design: Workers 402, 302 and 443. Formalization and source reading:
Worker 141.

`Langlands.AbelianScheme.SmoothFamilyAbelianRepresentabilityStatement.{u}`
is the proposition

```lean
∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S),
  ∃ (B : AbelianScheme S) (L : RigidifiedFamily A B.X),
    IsUniversalSmoothFamilyOnQuasiSeparatedTests A L
```

This module defines only that proposition. It contains no construction proof.

## The parameter and its actual universal family

All schemes, fields and base changes use the existing universe `u`.
The existential parameter is the existing `B : AbelianScheme S`, with its
actual commutative group-scheme structure, smoothness, properness and
geometrically connected fibres. The family lives on this very parameter:
`B.X : Over S` is its existing underlying object, and
`L : RigidifiedFamily A B.X` is an actual line bundle on `B.X.left ×_S A.X.left`
rigidified along the induced unit section of `A`.

The imported `IsUniversalSmoothFamilyOnQuasiSeparatedTests A L` is unchanged.
Its first conjunct, `IsAlgebraicallyTrivialFamilyViaSmoothFamily A L`, is a
condition on the global family. It forgets the rigidification and uses
`familyLineBundle` to transport the underlying bundle from the parameter-first
product to `A ×_S B.X.left`. Every algebraically closed field-valued point of
the parameter must have a fibre bundle with an actual smooth-family witness:
a smooth separated finite-type geometrically integral parameter, two rational
points, and a line bundle on the parameter-first product whose restrictions
are isomorphic to the trivial bundle and the fibre bundle.

The second conjunct says that for every `T : Over S` with
`[QuasiSeparatedSpace T.left]` and every
`q : AlgebraicallyTrivialClassesViaSmoothFamily A T`, there is exactly one
actual slice morphism `h : T ⟶ B.X` such that

```lean
RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
  (unitSection_comp A) L T h = q.val
```

This is the actual rigidified pullback class. For any representative of
`q.val`, the imported `RigidifiedLineBundle.classifyingMap_eq_iff` identifies
the equality with existence of a rigidification-preserving bundle isomorphism.
Uniqueness concerns the parameter map; the statement supplies no chosen
coherent system of witnessing bundle isomorphisms.

Every quasi-separated base and every quasi-separated test in universe `u`
is retained, including nonreduced tests. There is no further outer hypothesis:
no projectivity, polarization, noetherianity, reducedness, quasi-compactness,
ordinary-Picard existence, existing dual, global-functions, normalization,
comparison or representability assumption.

## Original sources and derived provenance

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
thesis revision March 14, 2021, is registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
The retained file is
`literature/Kai-Wen Lan - Arithmetic compactifications of PEL-type Shimura varieties (thesis revision, 2021-03-14).pdf`.
The passages read for this statement are:

- Conventions, printed p.xxvi/PDF p.26: schemes use the quasi-separated
  prescheme convention.
- Definition 1.3.1.1, printed p.67/PDF p.95: an abelian scheme is a proper
  smooth group scheme with geometrically connected fibres. The Library's
  bundle also records commutativity explicitly, as explained in
  `Langlands.AbelianScheme.Basic`.
- Definition 1.3.2.1 and Lemma 1.3.2.2, printed pp.73–74/PDF pp.101–102:
  the ordinary relative quotient uses bundles pulled back from the test
  scheme `T`, and its Picard-zero subfunctor imposes algebraic equivalence
  on every ordinary residue-field fibre. The lemma identifies these
  functors with rigidified isomorphism classes on `A ×_S T`.
- Theorem 1.3.2.3, Remark 1.3.2.4 and Definition 1.3.2.5, printed p.74/PDF
  p.102: the rigidified Picard-zero functor has an abelian-scheme representer
  and a universal rigidified Poincare bundle. The theorem is distinguished
  from the locally projective route discussed in the remark.

Lan's author errata of March 14, 2021, registered as
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were read at PDF pp.1 and 8–9. They replace the earlier separated convention
with quasi-separatedness and correct Definition 1.3.2.1 to use bundles from
`T`. The retained file is
`literature/Kai-Wen Lan - Arithmetic compactifications of PEL-type Shimura varieties (thesis errata, 2021-03-14).pdf`.

Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
is registered as `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The retained file is
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
The passages read are (0.4), printed p.1/PDF p.5, for the variety and line-bundle
conventions; (6.2), printed p.88/PDF p.92, for the universal rigidified
Poincare bundle; (6.9), printed p.91/PDF p.95, for smooth-parameter divisor
algebraic equivalence; Chapter VI section 3, printed p.95/PDF p.99, for the
field dual and normalization formula; (7.21)–(7.22), printed pp.105–106/PDF
pp.109–110, for the field Picard-zero/kernel comparison; and (7.24), printed
p.107/PDF p.111, for line-bundle algebraic equivalence and its geometric
comparison. The trivial-automorphism argument in (6.2) uses universal
structure-sheaf pushforward, a section, and the stated compactness and
separation assumptions; no such argument is proved here.

No source-specific project errata note was present in the checked project,
Library or workspace `notes/errata/` locations.

This exact proposition is a derived target motivated by Lan's abelian-scheme
representer. Lan's ordinary-fibre algebraic-equivalence functor and quotient
are distinct from the Library's explicit geometric-fibre smooth-family
predicate and actual rigidified families on the parameter-first product.
The citations supply motivation and conventions, not an imported Lean proof.

## Proof obligations and the shared construction

A future proof must construct this actual `B` and `L`, prove the global
smooth-family condition, and classify families on every quasi-separated
test, including nonreduced tests. It must establish the applicable
ordinary/geometric-fibre comparisons, the comparison of explicit
smooth-family witnesses with divisor algebraic equivalence or Picard
components, rigidification or normalization, and product-order transport.
A geometric-point bijection or existence of a parameter without the
specified abelian-scheme structure does not prove this proposition.
Comparison with geometric translation invariance remains separately owned.

The single pair is intended to feed the unchanged weaker
`SmoothFamilyQuasiSeparatedRepresentabilityStatement` by using `P := B.X`
and the same `L`, and to supply common geometry for
`SmoothFamilyFlatStatement` and `SmoothFamilyFinitePresentationStatement`.
Those latter statements quantify over an arbitrary supplied `P : Over S`;
this statement adds no restriction to their `P`. Comparing their supplied
universal families with this pair remains a separate actual-family
isomorphism argument.

The existing predicates, statements and imported closures are unchanged,
including `RelativeDualSchemeExistenceStatement`, whose universal property
uses geometric translation invariance on all tests. Existence, source
comparisons, quasi-separated-test isomorphism detection, and extension by
bundle-isomorphism gluing retain their separate ownership and operator
pauses. Neither chosen-dual geometry nor the relative-existence parent may
be used circularly to construct this pair. Only a separately accepted and
published exact proof will provide the common construction.
