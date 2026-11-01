# The smooth-family representer over affine bases of finite type over the integers

Statement design: Workers 930 and 141. Formalization and source verification:
Worker 344.

`Langlands.AbelianScheme.FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u}`
defines the proposition

```lean
∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
  (A : AbelianScheme (Spec (CommRingCat.of R))),
  ∃ (B : AbelianScheme (Spec (CommRingCat.of R))) (L : RigidifiedFamily A B.X),
    IsUniversalSmoothFamilyOnQuasiSeparatedTests A L
```

This module states the existence problem. It supplies no proof or construction.

## Quantifiers and universal family

The ring `R` is any commutative ring in universe `u` that is of finite type
over `ℤ`, using its canonical integer-algebra structure. Its spectrum is
affine and noetherian, hence quasi-separated; no additional
quasi-separatedness instance is required in the statement. All abelian
schemes over that spectrum are included.

The parameter `B` is the existing `AbelianScheme` structure, including an
actual commutative group-scheme structure, smoothness, properness and
geometrically connected fibres. The existential allows any such group
structure. The conclusion imposes no compatibility between its group law and
the universal property beyond the displayed predicate.

The actual family `L` lies on `B.X`, the underlying object of `B` in the
slice over `Spec R`. It is a line bundle on the parameter-first product
`B.X.left ×_(Spec R) A.X.left`, with the existing rigidification along the
induced unit section of `A`.

The imported `IsUniversalSmoothFamilyOnQuasiSeparatedTests A L` is unchanged.
Its first conjunct requires `IsAlgebraicallyTrivialFamilyViaSmoothFamily A L`
for the global family. This forgets the rigidification, transports the bundle
to the opposite product order using `familyLineBundle`, and tests every
algebraically closed field-valued point of the parameter. On the resulting
geometric fibre it requires a smooth separated finite-type geometrically
integral parameter, two rational points, and an actual line bundle whose
restrictions at those points are isomorphic to the trivial bundle and the
given fibre bundle.

The second conjunct says that for every `T : Over (Spec (CommRingCat.of R))`
with `[QuasiSeparatedSpace T.left]` and every
`q : AlgebraicallyTrivialClassesViaSmoothFamily A T`, there is exactly one
actual slice morphism `h : T ⟶ B.X` whose rigidified pullback class is `q.val`.
The existing `RigidifiedLineBundle.classifyingMap_eq_iff` interprets that
equality as existence of a rigidification-preserving bundle isomorphism
with any representative. Uniqueness concerns `h`; no chosen coherent system
of witnessing isomorphisms is specified.

Every quasi-separated test in universe `u` is retained, including nonreduced
tests. The base ring has no reducedness, normality, integrality, regularity,
dimension or excellence hypothesis. There is no projectivity, polarization,
ordinary-Picard existence, existing-dual, global-functions, normalization,
comparison or representability hypothesis.

## Derived provenance and original sources

This is the specialization of the shared
[`SmoothFamilyAbelianRepresentabilityStatement`](SmoothFamilyAbelianRepresentabilityStatement.md)
to affine bases of finite type over the integers. Neither original source
below states this exact Lean proposition. The specialization isolates the
existence input suggested by the reduction in Faltings–Chai.

Faltings and Chai, *Degeneration of Abelian Varieties* (1990), registered as
`provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`,
SHA-256 `f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e`,
is retained as
`literature/Faltings-Chai - Degeneration of Abelian Varieties (1990).pdf`.
Chapter I, Theorem 1.9, printed pp.5–7/PDF pp.17–19, presents Deligne's
proof of Raynaud's schemeness theorem. Its first reductions pass to affine
bases and then, by finite presentation, to algebras of finite type over
`ℤ`. Definition 1.4 and Remark 1.5, printed p.2/PDF p.14, describe the
rigidified Picard functor, its zero part and formal smoothness. The discussion
on printed p.3/PDF p.15 quotes Artin's algebraic-space representability
theorem and describes the Picard-zero group space and its Poincaré family.
Those passages motivate the future construction, rather than provide a
formal proof of this proposition.

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
thesis revision of 14 March 2021, registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`,
is retained as
`literature/Kai-Wen Lan - Arithmetic compactifications of PEL-type Shimura varieties (thesis revision, 2021-03-14).pdf`.
In §1.3.2, printed pp.73–74/PDF pp.101–102, Definition 1.3.2.1 uses
ordinary residue-field algebraic equivalence and a quotient by bundles from
the test scheme `T`. Lemma 1.3.2.2 identifies this with rigidified classes.
Theorem 1.3.2.3 gives an abelian-scheme representer, and Definition 1.3.2.5
names its actual universal rigidified Poincaré bundle. Remark 1.3.2.4
distinguishes the locally projective route.

Lan's author errata of 14 March 2021, registered as
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
are retained as
`literature/Kai-Wen Lan - Arithmetic compactifications of PEL-type Shimura varieties (thesis errata, 2021-03-14).pdf`.
PDF pp.1 and 8–9 were checked: the scheme convention is quasi-separated,
and Definition 1.3.2.1 is corrected to use bundles from `T`.
No source-specific project errata note was found in the checked project,
Library or workspace notes.

The Library's smooth-family condition is an explicit geometric-fibre
witness condition. Its comparison with the sources' algebraic equivalence
on ordinary fibres, and with their represented functors, is not asserted.
The source product order and ordinary quotient also require comparison with
the Library's parameter-first actual rigidified families.
The accepted
[relative Picard source map](../../../notes/abelian-schemes/relative-picard-source-map.md)
records these boundaries in more detail.

## Role in the shared reduction and future proof obligations

The shared construction can use an affine open cover, the published
`smoothFamilyAbelianRepresentabilityOfOpenCover`, the published
`affineObjectSpreading` to a finitely generated subring, and the published
`smoothFamilyUniversalBaseChange`. A finitely generated unital subring is
of finite type over `ℤ`. Applying the present existence statement at the
spread-out object would leave base change and transport along an abelian-scheme
isomorphism before gluing. This describes the intended reduction; this module
proves none of those steps.

An exact proof still has to construct `B` and `L` with the displayed universal
property. The Faltings–Chai route requires substantial separate inputs:

1. Reduction to reduced bases, including deformation of the representer and
   its universal family along nilpotent thickenings and the relevant formal
   smoothness.
2. Algebraic-space representability of the rigidified Picard functor, or an
   alternative representing construction. The Artin theorem quoted on
   printed p.3 has a finite-type scope over a field or an excellent Dedekind
   domain; its hypotheses must be supplied.
3. Proper smooth group structure on the Picard-zero part and its actual
   rigidified Poincaré family.
4. Schemeness over normal integral bases, using correspondence spaces,
   extension of a generic polarization, the cube theorem, relative
   ampleness, Riemann–Roch and semicontinuity.
5. Noetherian induction, amalgamation of components, and scheme gluing over
   the normalization and conductor square.
6. Comparison with explicit smooth-family witnesses on geometric fibres and
   classification of actual rigidified families on every quasi-separated
   test, including nonreduced tests.

These are proof obligations, not hypotheses of the statement or results of
this module. A construction restricted to projective abelian schemes or a
bijection only on geometric points would leave the target open. Substantial
missing inputs require focused statement and proof tasks, coordinated with
their current owners. Existing ordinary Picard, comparison, field-existence,
ambient-representability and generic dual-infrastructure workflows retain
their separate ownership and operator pauses.
