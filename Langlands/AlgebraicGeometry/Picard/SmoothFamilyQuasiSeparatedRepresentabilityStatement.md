# Smooth-family representability on quasi-separated tests

This module states existence of an actual universal rigidified family for the
published smooth-family algebraic-triviality predicate. Both declarations are
proposition definitions. The module supplies no existence proof.

For `S : Scheme.{u}`, `A : AbelianScheme S`, an actual `P : Over S` and an actual
`L : RigidifiedFamily A P`, the predicate
`IsUniversalSmoothFamilyOnQuasiSeparatedTests A L` is the conjunction of:

- `IsAlgebraicallyTrivialFamilyViaSmoothFamily A L`.
- For every `T : Over S` with `[QuasiSeparatedSpace T.left]` and every
  `q : AlgebraicallyTrivialClassesViaSmoothFamily A T`, there is exactly one
  slice morphism `h : T ⟶ P` such that
  `RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
  (unitSection_comp A) L T h = q.val`.

The second conjunct uses the actual pullback map of the specified rigidified
family into `RigidifiedClasses A T`. That quotient identifies two actual
families precisely when there exists a rigidification-preserving bundle
isomorphism. For a representative `M` of `q.val`, the equality is therefore
equivalent to an actual rigidified isomorphism between the pullback of `L`
and `M`, by the existing `RigidifiedLineBundle.classifyingMap_eq_iff`.
The unique object is the parameter map `h`; no chosen compatible family of
witnessing isomorphisms is asserted.

`Langlands.AbelianScheme.SmoothFamilyQuasiSeparatedRepresentabilityStatement.{u}`
asserts that for every `S : Scheme.{u}` with `[QuasiSeparatedSpace S]` and every
`A : AbelianScheme S`, there exist such an actual `P` and actual `L`. The
interface imposes no quasi-separatedness condition on `P`; a future construction
may supply a quasi-separated parameter. Every quasi-separated test in universe
`u` is included, including nonreduced tests. There is no reducedness,
noetherianity, quasi-compactness, projectivity, polarization, existing-dual,
ordinary-Picard-existence, normalization, global-functions or comparison
hypothesis.

The first conjunct is a condition on the global family itself. The imported
definition forgets the rigidification on `P ×_S A`, then uses
`familyLineBundle` and the inverse of `relativeSpaceSymmetry` to move to
`A ×_S P`. It tests every map `Spec K ⟶ P.left` for every algebraically closed
field `K : Type u`. On each actual geometric fibre the predicate requires an
actual smooth separated finite-type geometrically integral parameter, two
rational points, and an actual line bundle on the parameter-first product,
with endpoint restriction isomorphisms to the trivial bundle and the fibre
bundle. The same descended predicate defines the class subtype on tests.
The imported isomorphism-invariance and quotient-descent lemmas justify that
subtype; they establish no representability or source comparison.

## Original sources and conventions

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
thesis revision March 14, 2021, is registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
The retained file is
`literature/Kai-Wen Lan - Arithmetic compactifications of PEL-type Shimura varieties (thesis revision, 2021-03-14).pdf`.
The following passages govern the motivation:

- The conventions, printed p.xxvi/PDF p.26, restrict schemes to
  quasi-separated preschemes.
- Definition 1.3.1.1, printed p.67/PDF p.95, defines an abelian scheme by
  properness, smoothness and geometrically connected fibres.
- Definition 1.3.2.1, printed p.73/PDF p.101, defines the ordinary relative
  Picard quotient by bundles pulled back from the test scheme `T`. Its
  Picard-zero condition uses algebraic equivalence to zero on every ordinary
  residue-field fibre `t ∈ T`.
- Lemma 1.3.2.2, printed pp.73–74/PDF pp.101–102, identifies that quotient
  and its Picard-zero subfunctor with rigidified isomorphism classes.
- Theorem 1.3.2.3, printed p.74/PDF p.102, represents the rigidified
  Picard-zero functor by an abelian scheme. Definition 1.3.2.5 on the same
  page names its universal rigidified Poincare bundle on `A ×_S A∨`.
- Remark 1.3.2.4 on the same page distinguishes that theorem from the
  locally projective route. That restricted route does not justify the
  unrestricted abelian-scheme quantifier in the present statement.

The author's errata of March 14, 2021, registered as
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were read at PDF pp.1 and 8–9. Page 1 replaces the earlier separated
convention with quasi-separatedness and directs readers to the revision.
Page 8 corrects the base bundles in Definition 1.3.2.1 to come from `T`.
The retained file is
`literature/Kai-Wen Lan - Arithmetic compactifications of PEL-type Shimura varieties (thesis errata, 2021-03-14).pdf`.
No source-specific errata note was present in the checked project, Library
or workspace `notes/errata/` locations.

Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
is registered as `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The retained file is
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
Notation (0.4), printed p.1/PDF p.5, gives the separated finite-type
geometrically integral variety convention and the locally free rank-one
interpretation of line bundles. Remark (6.9), printed p.91/PDF p.95, uses a
smooth parameter variety for divisor algebraic equivalence and relates the
line-bundle interpretation to Picard components. Section (7.24), printed
p.107/PDF p.111, defines line-bundle algebraic equivalence through the
Neron–Severi group and explains its geometric comparison.

Section (6.2), printed p.88/PDF p.92, describes the actual universal property
of a rigidified Poincare bundle. Its trivial-automorphism argument assumes
universal equality of the structure-sheaf pushforward with the base structure
sheaf, along with a section and the stated compactness and separation
conditions on the structure morphism. Those assumptions must be proved for
any use of that argument here. Corollary (7.22), printed p.106/PDF p.110,
relates field Picard-zero to the kernel of the line-bundle homomorphism.
It motivates a separately owned comparison with translation invariance;
that comparison is neither imported nor asserted by this module.

## Derived interface and remaining proof obligations

This is a derived representability target, not a verbatim statement from Lan
and not a proved theorem. Lan's ordinary-fibre algebraic-equivalence condition
and ordinary quotient differ from the imported geometric-fibre smooth-family
predicate and the already rigidified bundles on `T ×_S A`.
A future exact proof must construct an actual parameter scheme and actual
universal family, and implement the following comparisons:

- Ordinary residue-field algebraic equivalence versus the condition after
  every algebraically closed field-valued point, including the needed field
  extensions and actual fibre identifications.
- The explicit smooth-family line-bundle witnesses versus divisor algebraic
  equivalence or the Picard identity-component formulation.
- The ordinary quotient by bundles pulled from `T` versus actual rigidified
  representatives, with the required rigidification or normalization
  construction.
- The transport from the source product order `A ×_S T` to the Library order
  `T ×_S A`, respecting actual bundle pullbacks, rigidifications and classes.

The proof must also show that its global universal family satisfies the
imported smooth-family fibre predicate and prove existence and uniqueness of
the classifying map on every quasi-separated test, retaining all nonreduced
tests. A comparison only of geometric point sets does not provide that family
classification. None of these comparisons follows merely from the citations,
and none is added as a hypothesis to the proposition.

The parent `RelativeDualSchemeExistenceStatement` and its imported closure
remain unchanged: that parent uses geometric translation invariance and
classifies every test scheme, including non-quasi-separated tests. The present
statement handles only existence for smooth-family classes on quasi-separated
tests. Comparison with the parent predicate and extension to all tests remain
separate tasks. Existing owners and operator pauses for ordinary Picard,
ordinary/rigidified comparison, global functions, field existence, openness,
relative geometry and all-test extension must be respected; their required
constructions must be reused after authorized independent acceptance and
publication.
