# Extending Picard-zero classification from quasi-separated tests

`Langlands.AbelianScheme.PicardZeroQuasiSeparatedExtensionStatement.{u}`
states that an actual rigidified Picard-zero family universal on
quasi-separated tests over a quasi-separated base classifies every test
scheme in universe `u`. This file defines the proposition and its restricted
universal-property predicate. It supplies no proof of the extension.

## Exact interface

For `A : AbelianScheme S`, `P : Over S` and
`L : RigidifiedFamily A P`,
`IsUniversalPicardZeroOnQuasiSeparatedTests A L` is exactly the conjunction
used by the existing `IsUniversalPicardZero A L`, with the additional
instance binder `[QuasiSeparatedSpace T.left]` in its test quantifier:

1. `IsPicardZeroFamily A L` holds.
2. For every `T : Over S` with `QuasiSeparatedSpace T.left` and every
   `q : PicardZeroClasses A T`, there is exactly one `h : T ⟶ P` satisfying
   `RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
   (unitSection_comp A) L T h = q.val`.

The map is the published classification map obtained from actual rigidified
relative pullback on `T ×_S A`. Equality with the class of an actual family
means existence of a rigidification-preserving bundle isomorphism, by
`RigidifiedLineBundle.classifyingMap_eq_iff`. Uniqueness is uniqueness of
`h`; the definition asserts no uniqueness of a witnessing bundle isomorphism.
The Picard-zero predicate remains the published geometric translation
invariance condition after passage to every algebraically closed
field-valued point. The restricted predicate itself requires no
quasi-separatedness of `S` or `P`.

The target quantifies over every `S : Scheme.{u}` with
`[QuasiSeparatedSpace S]`, every `A : AbelianScheme S`, every `P : Over S`
and every actual `L : RigidifiedFamily A P`. Its sole implication is from
the restricted predicate to the existing `IsUniversalPicardZero A L`.
Thus the conclusion retains all tests in the fixed universe, including
nonreduced and non-quasi-separated ones. There is no quasi-compactness,
reducedness, noetherianity or projectivity hypothesis, no quasi-separatedness
hypothesis on `P`, and no assumed `HasDualScheme A`.

## Derived provenance

This is the local-to-global interface described in
`RelativeDualSchemeExistenceStatement.md`, isolated by Worker 402 for the
relative existence workflow. It concerns extension of a supplied universal
family; it does not construct that family or compare the Library's
geometric predicate with algebraic equivalence.

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
thesis revision of March 14, 2021, registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`,
uses quasi-separated preschemes in the conventions on printed p.xxvi
(PDF p.26). Definition 1.3.2.1 and Lemma 1.3.2.2, printed pp.73–74
(PDF pp.101–102), describe Picard-zero families using fibrewise algebraic
equivalence and their rigidified representatives. Theorem 1.3.2.3 represents
this functor; Remark 1.3.2.4 distinguishes the stronger representability
result from the locally projective route; Definition 1.3.2.5 specifies the
universal rigidified bundle. These passages motivate the restricted
classification property. The extension to arbitrary tests with the
Library's predicate is derived, rather than a literal assertion of Lan.

The registered March 14, 2021 errata,
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were read at pp.1 and 8–9. Page 1 replaces the separated convention by
quasi-separatedness and recommends the revision. Page 8 corrects the
line bundles pulled from the base in Definition 1.3.2.1 to come from
`T`; the revision incorporates this.

Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
VI (6.2), printed p.88 (PDF p.92), supplies the rigidified pullback
universal-property motivation. It is registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Its trivial-automorphism argument uses the universal structure-sheaf
pushforward hypothesis `f_* O_(X ×_S T) = O_T`, together with the section.
That hypothesis is not silently assumed here. Applying such an argument
to abelian schemes requires a proved applicable global-functions result.
The source uses `A ×_S T`; the published relative-family definitions
already account for the swap to `T ×_S A`.

## Remaining proof obligations

A proof must start with an arbitrary test scheme `T` and an actual
representative of a class in `PicardZeroClasses A T`. Restriction to an
affine open cover gives quasi-separated tests. It must justify preservation
of the geometric Picard-zero condition under these actual relative
pullbacks, and the composition and isomorphism comparisons for the
classification maps.

Each pairwise overlap is an open subscheme of an affine member, hence
separated and quasi-separated, even if it is not quasi-compact. Applying
restricted uniqueness on these overlaps must make the local parameter
maps agree. The proof must glue them to an `S`-map `T → P` without imposing
separatedness or quasi-separatedness on `P`.

To identify the original global rigidified class with the pullback along
that glued map, it must also glue compatible local
rigidification-preserving bundle isomorphisms, or prove the corresponding
Zariski separatedness/sheaf statement for these rigidified classes.
Existence of local isomorphisms alone does not provide their compatibility.
A route using triviality of rigidified automorphisms must establish its
global-functions input, rather than adding it as a final hypothesis.
Finally, restriction to the same cover must prove uniqueness of the global
parameter map. All steps must include nonreduced affine tests.

These are obligations of the exact-target proof successor. No gluing,
sheaf comparison, existence or global-functions theorem is proved by this
statement. The parent relative existence target and its imported closure
are preserved, and the ordinary Picard, field existence, openness,
relative geometry, ordinary/rigidified comparison and global-functions
workflows retain their separate ownership and existing pause controls.
