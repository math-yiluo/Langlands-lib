# Quasi-compactness of the chosen dual over a quasi-separated base

`Langlands.AbelianScheme.RelativeDualSchemeQuasiCompactStatement` is a
proposition definition. For every `S : Scheme.{u}` with
`[QuasiSeparatedSpace S]`, every `A : AbelianScheme S` and every proof
`hA : HasDualScheme A`, it asserts

```text
QuasiCompact (dualScheme A hA).hom
```

that is, the structural morphism of the actual chosen parameter scheme
`dualScheme A hA : Over S` to `S` is quasi-compact in Mathlib's sense
(`AlgebraicGeometry.QuasiCompact`): the inverse image of every
quasi-compact open subset of `S` is quasi-compact. This is a relative
property of the morphism. It does not assert that `S`, or the total space
of the parameter scheme, is quasi-compact.

The only base hypothesis is quasi-separatedness of `S`. No noetherian,
reducedness, quasi-compactness, projectivity, ample-line-bundle,
polarization or coherence hypothesis is imposed on `S`, `A`, `hA`, the
parameter scheme or its morphism. The declaration is universe-polymorphic
in `u`. `HasDualScheme`, `dualScheme` and the geometric Picard-zero
predicate are the existing Library definitions in
`Langlands.AlgebraicGeometry.Picard.DualScheme`, used unchanged. This unit
defines a proposition only; it proves nothing and introduces no axiom.

## Original source and derived formulation

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
Harvard thesis, revised March 14, 2021, registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
Theorem 1.3.2.3, printed p.74 (PDF p.102), states that for every abelian
scheme `A → S` the rigidified functor `Pic⁰_e(A/S)` is representable by an
abelian scheme over `S`, the dual abelian scheme, and refers to
Faltings–Chai, Ch. I, §1 for the proof. Definition 1.3.1.1, printed p.67
(PDF p.95), requires an abelian scheme to be proper, smooth and to have
geometrically connected fibres. Remark 1.3.1.2(1) on the same page notes
that properness implies quasi-compactness, citing EGA II 5.4.1 and
I 6.6.3. Hence the source's dual abelian scheme is quasi-compact over `S`.
Definition 1.3.2.1 and Lemma 1.3.2.2, printed pp.73–74 (PDF pp.101–102),
define the relative Picard functor, the Picard-zero subfunctor by
fibrewise algebraic equivalence to zero, and its rigidified form;
Definition 1.3.2.5 on p.74 names the universal Poincaré sheaf. The
conventions, printed p.xxvi (PDF p.26), take schemes to be
quasi-separated, which is why the base hypothesis is kept.

The author's March 14, 2021 errata, registered as
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were checked at pp.1 and 8–9. Page 1 replaces the former separated-scheme
convention by quasi-separatedness and recommends reading the revision.
Page 8 corrects Definition 1.3.2.1 so that the line bundles quotiented
out are pulled back from the test scheme `T`, rather than from `S`; the
revision incorporates this correction. Page 9 contains no correction
affecting the cited statements; its first item supplies a missing "over
`S`" in a remark of the original numbering. The numbering used here is
that of the revision. Remark 1.3.2.4 distinguishes Theorem 1.3.2.3 from the locally
projective representability route; it adds no hypothesis here.

This statement is a derived consequence of Theorem 1.3.2.3, Definition
1.3.1.1 and Remark 1.3.1.2(1) for the Library's chosen parameter scheme,
not a verbatim source theorem. In the Library, `HasDualScheme A` asserts
the existence of a parameter scheme with an actual rigidified family
satisfying `IsUniversalPicardZero A`. Its fibre condition is translation
invariance on geometric fibres, and its universal property classifies
families over every test scheme, including nonreduced ones. A proof
through the source's representer must compare the geometric-fibre
translation-invariance condition with fibrewise algebraic equivalence to
zero, and compare the actual rigidified families and their pullbacks,
including over nonreduced test schemes. Agreement on geometric points
alone does not give that comparison.

The source uses quasi-separated test schemes, whereas the Library's
universal property quantifies over all test schemes. One may first
restrict that property to the source's test category, compare the
functors there, and recover an isomorphism of the actual parameter
schemes using affine tests and gluing. That recovery must not assume that
the chosen parameter scheme is already quasi-separated. Quasi-compactness
would then be transported along the isomorphism. A direct proof of the
precise geometric property, for example by a boundedness argument, is
another possible route. None of these steps is proved in this unit.

Quasi-compactness of a morphism is not a fibrewise property: quasi-compact
geometric fibres, or the field statement `FieldDualSchemeGeometryStatement`,
do not imply it. Local finite presentation, the separate statement
`RelativeDualSchemeFinitePresentationStatement`, does not imply it either.

## Role

Mathlib's `UniversallyClosed.of_valuativeCriterion` and
`IsProper.of_valuativeCriterion` both require `[QuasiCompact f]`. This
statement is the global quasi-compactness prerequisite for proving the
published target `RelativeDualSchemeProperStatement` by the valuative
criterion. Conversely, Mathlib's instance from `UniversallyClosed` to
`QuasiCompact` shows that a proof of the properness statement would imply
this one, so a proof of this statement intended as a properness
prerequisite must not assume the properness target or the parent target
`RelativeDualSchemeGeometryStatement`. The exact proof of this statement
remains a separate obligation.

The Lean statement follows verbatim the formulation specified by
Worker 529 in task `e63495ab-16b0-47b7-a0c7-616fbf34c021`, published for
the properness proof task `f39b40a8-68f7-4734-a60f-bca1f46f648c`.
