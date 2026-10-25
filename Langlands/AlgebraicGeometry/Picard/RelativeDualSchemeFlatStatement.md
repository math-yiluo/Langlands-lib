# Flatness of the chosen dual over a quasi-separated base

`Langlands.AbelianScheme.RelativeDualSchemeFlatStatement` is a proposition
definition. For every `S : Scheme.{u}` with `[QuasiSeparatedSpace S]`, every
`A : AbelianScheme S` and every proof `hA : HasDualScheme A`, it asserts

```text
Flat (dualScheme A hA).hom
```

Thus the structural morphism of the actual chosen parameter scheme
`dualScheme A hA` to `S` is flat. The declaration retains the arbitrary
universe `u` and has no further hypotheses. `HasDualScheme`, `dualScheme`
and the Picard-zero predicate are the existing Library definitions imported
through `Langlands.AlgebraicGeometry.Picard.DualScheme`. This unit defines
the proposition and supplies no proof of it.

## Original source and derived formulation

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
Harvard thesis, revised March 14, 2021, registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`:

- The conventions, printed p.xxvi (PDF p.26), take schemes to be
  quasi-separated preschemes unless otherwise specified.
- Definition 1.3.1.1, printed p.67 (PDF p.95), defines an abelian scheme
  as a proper smooth group scheme with geometrically connected fibres.
- Definition 1.3.2.1 and Lemma 1.3.2.2, printed pp.73–74 (PDF pp.101–102),
  describe the relative Picard-zero functor and its rigidified version
  `Pic⁰_e(A/S)` using fibrewise algebraic equivalence to zero. The
  quotient by base-pulled line bundles uses bundles on the test scheme `T`.
- Theorem 1.3.2.3, printed p.74 (PDF p.102), represents `Pic⁰_e(A/S)` by
  an abelian scheme over `S`, referring to Faltings–Chai, Ch. I, §1 for
  the proof. Definition 1.3.2.5 on the same page names its universal
  rigidified Poincaré bundle. Remark 1.3.2.4 distinguishes this theorem
  from the route that assumes local projectivity.

The author's March 14, 2021 errata, registered as
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were read at pp.1 and 8–9. Page 1 recommends the revision and replaces
separatedness of schemes by quasi-separatedness. Page 8 corrects the
Picard functor's base-pulled bundles to come from `T`; the revision
incorporates this correction. The numbering above is the revision's.

This statement is a derived formulation for the Library's chosen universal
parameter scheme, not a verbatim source theorem. The source representer
is an abelian scheme, hence smooth and therefore flat. To transfer that
conclusion to `dualScheme A hA`, a proof must compare its represented
functor with the source functor and identify the parameter schemes over `S`.

In the Library, `HasDualScheme A` asserts existence of an actual
rigidified family satisfying `IsUniversalPicardZero A`. Its Picard-zero
condition uses translation invariance on all geometric fibres, and its
universal property uniquely classifies actual rigidified families up to
isomorphism by pullback over every test scheme, including nonreduced ones.
The comparison with fibrewise algebraic equivalence to zero must hold for
these families and pullbacks; equality of geometric point sets alone does
not suffice. Lan's test schemes follow his quasi-separated convention.
One may first restrict the Library universal property to that category;
a comparison of the actual parameter schemes must still justify an
isomorphism even before the chosen parameter scheme is known to be
quasi-separated, for example using affine tests and gluing. Flatness must
then be transported along that isomorphism. These are proof obligations,
not results established by this proposition definition. The paired
Markdown of `RelativeDualSchemeGeometryStatement` describes the same
comparison boundary in more detail.

## Role and scope

Together with `RelativeDualSchemeFinitePresentationStatement`,
`RelativeDualSchemeProperStatement`, the published base-change statement
`PicardZeroUniversalBaseChangeStatement` and the field statement
`FieldDualSchemeGeometryStatement`, this proposition is an input to the
planned proof of `RelativeDualSchemeGeometryStatement`: flatness, local
finite presentation and smooth fibres give smoothness, and geometrically
connected fibres give geometric connectedness. Flatness itself is not a
fibrewise property and does not follow merely from the field statement.

The target retains `hA` and makes no claim of dual existence. It adds no
noetherian, reducedness, quasi-compactness or projectivity hypothesis, no
ample line bundle or polarization, and no tensor, pullback-coherence or
inverse-bundle input. A separate exact-target proof obligation is required.
No axiom is introduced.

The Lean statement and the initial paired Markdown design were supplied
by Worker 301 in shared draft revision 1 of task
`522d3c86-486f-49bb-8fc1-68a353b0fdd5`. Worker 442 retained the exact
statement and expanded the source and comparison notes after reading the
cited passages.
