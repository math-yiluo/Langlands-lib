# Local finite presentation of the chosen dual over a quasi-separated base

`Langlands.AbelianScheme.RelativeDualSchemeFinitePresentationStatement` is a
proposition definition. For every `S : Scheme.{u}` with
`[QuasiSeparatedSpace S]`, every `A : AbelianScheme S` and every proof
`hA : HasDualScheme A`, it asserts

```text
LocallyOfFinitePresentation (dualScheme A hA).hom
```

that is, the structural morphism of the actual chosen parameter scheme
`dualScheme A hA` to `S` is locally of finite presentation. There is no
noetherian, reducedness, quasi-compactness or projectivity hypothesis on `S`
or `A`, and the declaration is universe-polymorphic in `u`. `HasDualScheme`,
`dualScheme` and the Picard-zero predicate are the existing Library
definitions in `Langlands.AlgebraicGeometry.Picard.DualScheme`. This is a
proposition definition, not a proof, and no axiom is introduced.

## Original source and derived formulation

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
Harvard thesis, revised March 14, 2021, registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
Theorem 1.3.2.3, printed p.74 (PDF p.102), states that for every abelian
scheme `A → S` the rigidified functor `Pic⁰_e(A/S)` is representable by an
abelian scheme over `S`, referring to Faltings–Chai, Ch. I, §1 for the
proof. Definition 1.3.1.1, printed p.67 (PDF p.95), makes an abelian scheme
smooth and proper with geometrically connected fibres. Remark 1.3.1.2(1)
on the same page explicitly observes that smoothness implies local finite
presentation.
The conventions, printed p.xxvi (PDF p.26), take schemes to be
quasi-separated, which is why the base hypothesis is kept.

Definition 1.3.2.1 and Lemma 1.3.2.2, printed pp.73–74 (PDF pp.101–102),
describe the fibrewise algebraic-equivalence-to-zero condition and the
rigidified representatives of the relative Picard functor. Definition
1.3.2.5, printed p.74 (PDF p.102), names its universal rigidified line
bundle. Remark 1.3.2.4 distinguishes Theorem 1.3.2.3 from
the route assuming local projectivity; we use the stronger theorem's
scope.

The author's errata dated March 14, 2021, registered as
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were read at pp.1 and 8–9. Page 1 replaces the older separated-scheme
convention by quasi-separatedness and recommends the revision. Page 8
corrects the base-pulled line bundles in Definition 1.3.2.1 to come from
the test scheme `T`; the revision incorporates this. The theorem numbering
above is the revision's numbering.

This statement is a derived consequence of that theorem for the Library's
chosen parameter scheme, not a verbatim source theorem. In the Library
`HasDualScheme A` asserts the existence of a parameter scheme with an actual
rigidified family satisfying `IsUniversalPicardZero A`, whose fibre
condition is translation invariance on geometric fibres and whose universal
property classifies families over every test scheme, including nonreduced
ones. A proof must compare this functor with the source's `Pic⁰_e(A/S)` and
transport local finite presentation along the resulting isomorphism of
parameter schemes. In particular, it must justify the comparison of
geometric-fibre translation invariance with the source's fibrewise
algebraic equivalence, together with the ordinary line bundles,
rigidifications and their pullbacks. Equality of geometric point sets
does not establish this comparison on nonreduced test schemes.

Lan's convention restricts the source test category to quasi-separated
schemes. The Library universal property can first be restricted to that
category. Recovering an isomorphism of the actual parameter schemes must
then be justified using affine tests and gluing, even before the chosen
parameter scheme is known quasi-separated. This is the comparison also
described in the published Markdown of
`RelativeDualSchemeGeometryStatement`. Alternatively one may prove local
finite presentation directly from the represented functor's behaviour on
filtered limits of rings, including descent of its geometric-fibre
Picard-zero condition. Neither route is implemented in this statement.

## Role

Proofs of this statement, `RelativeDualSchemeFlatStatement`,
`RelativeDualSchemeProperStatement`, the base-change statement
`PicardZeroUniversalBaseChangeStatement` and the field statement
`FieldDualSchemeGeometryStatement` supply the inputs to the parent's
relative geometry reduction. The finite presentation statement itself
does not prove `RelativeDualSchemeGeometryStatement` or dual existence.
Its exact proof remains a separate obligation.
