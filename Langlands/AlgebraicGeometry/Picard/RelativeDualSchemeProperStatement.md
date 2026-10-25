# Properness of the chosen dual over a quasi-separated base

`Langlands.AbelianScheme.RelativeDualSchemeProperStatement` is a proposition
definition. For every `S : Scheme.{u}` with `[QuasiSeparatedSpace S]`, every
`A : AbelianScheme S` and every proof `hA : HasDualScheme A`, it asserts

```text
IsProper (dualScheme A hA).hom
```

that is, the structural morphism of the actual chosen parameter scheme
`dualScheme A hA : Over S` to `S` is proper (separated, universally closed
and locally of finite type, as in Mathlib). The only additional base
hypothesis is quasi-separatedness: no noetherian, reducedness,
quasi-compactness, projectivity or polarization hypothesis is imposed.
The declaration is universe-polymorphic in `u`. `HasDualScheme`, `dualScheme` and
the Picard-zero predicate are the existing Library definitions in
`Langlands.AlgebraicGeometry.Picard.DualScheme`. This is a proposition
definition, not a proof, and no axiom is introduced.

## Original source and derived formulation

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
Harvard thesis, revised March 14, 2021, registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
Theorem 1.3.2.3, printed p.74 (PDF p.102), states that for every abelian
scheme `A → S` the rigidified functor `Pic⁰_e(A/S)` is representable by an
abelian scheme over `S`, referring to Faltings–Chai, Ch. I, §1 for the
proof. Definition 1.3.1.1, printed p.67 (PDF p.95), requires an abelian
scheme to be smooth, proper and to have geometrically connected fibres.
Definition 1.3.2.1 and Lemma 1.3.2.2, printed pp.73–74 (PDF pp.101–102),
describe the fibrewise algebraic-equivalence condition and its rigidified
representatives; Definition 1.3.2.5 on p.74 identifies the universal Poincaré
bundle. The conventions, printed p.xxvi (PDF p.26), take schemes to be
quasi-separated, which is why the base hypothesis is kept.

The author's March 14, 2021 errata, registered as
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were checked at pp.1 and 8–9. Page 1 replaces the former separated-scheme
convention by quasi-separatedness and recommends the revision. Page 8
corrects Definition 1.3.2.1 so that the line bundles quotiented out come
from the test scheme `T`, rather than `S`; the revision incorporates this
correction. The theorem numbering here is that of the revision. Its
Remark 1.3.2.4 distinguishes Theorem 1.3.2.3 from the locally projective
representability route, so no local projectivity hypothesis is added.

This statement is a derived consequence of that theorem for the Library's
chosen parameter scheme, not a verbatim source theorem. In the Library
`HasDualScheme A` asserts the existence of a parameter scheme with an actual
rigidified family satisfying `IsUniversalPicardZero A`, whose fibre
condition is translation invariance on geometric fibres and whose universal
property classifies families over every test scheme, including nonreduced
ones. A proof must compare the geometric-fibre translation-invariance
condition with the source's fibrewise algebraic equivalence to zero and
compare the actual rigidified families and pullbacks, including over
nonreduced test schemes. Agreement only on geometric points does not
give that comparison.

The source uses quasi-separated test schemes, whereas the Library's
universal property quantifies over all test schemes. One may first restrict
that property to the source's test category, compare the functors there,
and recover an isomorphism of the actual parameter schemes using affine
tests and gluing. This must work before the chosen parameter scheme is
known to be quasi-separated. Properness must then be transported along
that isomorphism; a direct proof is another possible route. The paired
Markdown of `RelativeDualSchemeGeometryStatement` describes this
comparison in more detail. None of these steps is proved in this unit.
Properness is not a fibrewise property, so the field statement
`FieldDualSchemeGeometryStatement` does not imply it.

## Role

Together with `RelativeDualSchemeFlatStatement`,
`RelativeDualSchemeFinitePresentationStatement`, the published base-change
statement `PicardZeroUniversalBaseChangeStatement` and the field statement
`FieldDualSchemeGeometryStatement`, this statement implies the Library target
`RelativeDualSchemeGeometryStatement`; it supplies the properness component
directly once proved.

The Lean statement and initial Markdown reuse Worker 301's shared draft
revision 1 for task `522d3c86-486f-49bb-8fc1-68a353b0fdd5`. Worker 445
checked the cited passages and expanded the provenance and scope explanation.
