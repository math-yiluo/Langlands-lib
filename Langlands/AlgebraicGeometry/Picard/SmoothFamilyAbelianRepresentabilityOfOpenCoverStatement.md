# Zariski-local existence of an abelian-scheme smooth-family representer

Statement design: Workers 930 and 141. Formalization, Markdown and source
checks: Worker 1043.

`Langlands.AbelianScheme.SmoothFamilyAbelianRepresentabilityOfOpenCoverStatement.{u}`
is the proposition

```lean
∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
  (𝒰 : S.OpenCover.{u}),
  (∀ i, ∃ (B : AbelianScheme (𝒰.X i))
      (L : RigidifiedFamily ((baseChange (𝒰.f i)).obj A) B.X),
      IsUniversalSmoothFamilyOnQuasiSeparatedTests ((baseChange (𝒰.f i)).obj A) L) →
    ∃ (B : AbelianScheme S) (L : RigidifiedFamily A B.X),
      IsUniversalSmoothFamilyOnQuasiSeparatedTests A L
```

In words: if the abelian-scheme representer of the shared target exists over
every member of some Zariski open cover of a quasi-separated base, then it
exists over the whole base. This module defines only that proposition. It
contains no proof, and it does not assert that the hypothesis holds for any
particular cover.

## The base, the cover and the local hypothesis

All schemes, covers and base changes use the single universe `u`.
The base `S : Scheme.{u}` is an arbitrary quasi-separated scheme, and
`A : AbelianScheme S` is the Library's existing abelian scheme, with its
actual commutative group-scheme structure, smoothness, properness and
geometrically connected fibres.

`𝒰 : S.OpenCover.{u}` is Mathlib's open cover of `S`: an index type
`𝒰.I₀ : Type u`, schemes `𝒰.X i` and open immersions `𝒰.f i : 𝒰.X i ⟶ S`
whose images cover `S`. The index type is arbitrary; no affine, finite or
quasi-compact condition is imposed on the cover or on its members.

For each index `i`, `(baseChange (𝒰.f i)).obj A : AbelianScheme (𝒰.X i)` is
the existing `AbelianScheme.baseChange` along `𝒰.f i`: the actual pullback of
`A` to `𝒰.X i` with its induced group-scheme operations. The hypothesis says
that, for each `i` separately, there exist

- an actual `B : AbelianScheme (𝒰.X i)`, and
- an actual `L : RigidifiedFamily ((baseChange (𝒰.f i)).obj A) B.X`, a line
  bundle on the product of `B.X` with the restricted abelian scheme,
  rigidified along the induced unit section,

such that `L` satisfies the unchanged predicate
`IsUniversalSmoothFamilyOnQuasiSeparatedTests` for the restricted abelian
scheme. That predicate is described below; it quantifies over every
quasi-separated test over `𝒰.X i`, including nonreduced tests.

The local data are uncoordinated. The hypothesis is a separate existential
for each index, so it supplies no chosen local pairs, no isomorphisms between
the restrictions of the local parameters for indices `i` and `j` to the
overlap of `𝒰.X i` and `𝒰.X j`, no isomorphisms between the corresponding
restrictions of the local families, and no cocycle condition. The group law and unit section of each local `B` are
arbitrary abelian-scheme structures; nothing ties them to those of another
member. Producing compatible gluing data from these independent local pairs
and combining them into one global pair is the substance of any future proof.

The members `𝒰.X i` are not given a `QuasiSeparatedSpace` instance in the
hypothesis, and the predicate used there does not need one. Since each
`𝒰.f i` is an open immersion into the quasi-separated space `S`, every member
and every overlap of members is homeomorphic to an open subspace of `S` and
is therefore quasi-separated; this matches the quasi-separated base of the
shared target.

## The conclusion

The conclusion is exactly the existential of the published shared target
`SmoothFamilyAbelianRepresentabilityStatement` for the given `A`: an actual
`B : AbelianScheme S` and an actual `L : RigidifiedFamily A B.X` with
`IsUniversalSmoothFamilyOnQuasiSeparatedTests A L`. It is not strengthened.
In particular it does not require the global `B` or `L` to restrict to the
local pairs supplied by the hypothesis, and it does not require any chosen
isomorphism with them.

For an abelian scheme `A` over a base and a family `L` on a parameter
`P : Over` that base, the imported predicate
`IsUniversalSmoothFamilyOnQuasiSeparatedTests A L` is the conjunction of two
conditions, unchanged here:

1. `IsAlgebraicallyTrivialFamilyViaSmoothFamily A L`: after forgetting the
   rigidification and transporting the bundle to the product of `A` with the
   parameter, every fibre at an algebraically closed field-valued point of
   the parameter has an explicit smooth-family witness. A witness is a smooth
   separated finite-type geometrically integral parameter variety, two
   rational points, and a line bundle on the parameter-first product whose
   restrictions at the two points are isomorphic to the trivial bundle and to
   the fibre bundle.
2. For every test `T` over the base with `[QuasiSeparatedSpace T.left]` and
   every rigidified smooth-family algebraically trivial class `q` on `T`,
   there is exactly one actual slice morphism `h : T ⟶ P` whose rigidified
   pullback class, computed by `RigidifiedLineBundle.classifyingMap`,
   equals `q.val`.

Every quasi-separated base, every quasi-separated test (including nonreduced
tests) and every universe-`u` open cover is retained. There is no further
hypothesis: no affine, finite-index, quasi-compactness, noetherianity,
reducedness, projectivity, polarization, ordinary-Picard existence,
global-functions, normalization, comparison, compatibility-of-local-data or
representability assumption.

## Relation to the shared target

The shared target `SmoothFamilyAbelianRepresentabilityStatement` immediately
implies this proposition, because its conclusion is the conclusion here for
the same quasi-separated `S` and `A`. This proposition is intended for the
converse reduction. Combined with the shared target for the members of an
affine open cover of `S` (for example Mathlib's `S.affineCover`, whose index
type is in universe `u`), it would give the shared target for `S`; that is the
first reduction step in the route described below. That combination is not
proved in this module.

The existing statement pairs and their import closures are unchanged,
including `SmoothFamilyAbelianRepresentabilityStatement`,
`SmoothFamilyQuasiSeparatedRepresentabilityStatement`, and the flatness and
finite-presentation targets that consume the shared target's geometry.

## Original sources and derived provenance

This is a derived local-to-global statement for the Library's existing
predicate. No cited source states this exact Lean proposition.

Faltings–Chai, *Degeneration of Abelian Varieties* (1990), is registered as
`provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`,
SHA-256 `f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e`,
and retained as
`literature/Faltings-Chai - Degeneration of Abelian Varieties (1990).pdf`.
Theorem 1.9 (Raynaud), printed p.5/PDF p.17, states that an abelian algebraic
space over a scheme is a scheme, as is its Picard functor, with an
affine-neighbourhood assertion over affine opens of the base. Deligne's proof,
printed pp.6–7/PDF pp.18–19, begins with the reduction step "We may assume
that S is affine" (printed p.6, step (1)) and gives no separate argument for
it. The source works with algebraic spaces and the Picard functor defined by
algebraic equivalence; it does not treat the Library's rigidified families on
an abelian-scheme parameter. This proposition formulates the corresponding
Zariski-local step for the Library's predicate, where it is a genuine gluing
statement rather than a remark.

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
thesis revision of 14 March 2021, is registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`, and
retained as
`literature/Kai-Wen Lan - Arithmetic compactifications of PEL-type Shimura varieties (thesis revision, 2021-03-14).pdf`.
Definition 1.3.2.1, Lemma 1.3.2.2,
Theorem 1.3.2.3 and Definition 1.3.2.5, printed pp.73–74/PDF pp.101–102,
give the rigidified Picard-zero functor on all tests `T/S`, its
representability by the dual abelian scheme over every base, and the
universal rigidified Poincare sheaf. This motivates the represented functor
and the global conclusion; Lan does not state a cover-gluing lemma.

Worker 141's accepted source map,
[Relative Picard representability: source and construction boundaries](../../../notes/abelian-schemes/relative-picard-source-map.md),
records the read passages of both sources and the remaining comparisons.

The Library's smooth-family condition is an explicit geometric-fibre witness
condition, as described above. Its comparison with the sources' algebraic
equivalence on ordinary residue-field fibres is not asserted here, and the
citations supply motivation and conventions, not an imported Lean proof.

## Future proof obligations

These inputs are recorded for a future proof; none is assumed by the
proposition. Several are unproved, and one is not yet stated.

1. Restriction of the local universal property to double and triple
   overlaps. The smooth-family universal base-change statement
   `SmoothFamilyUniversalBaseChangeStatement` (statement task
   `b3fc018d-5e69-4f09-9807-0d72b7e02d80`, submitted separately and not
   imported here) would supply this, together with transport along the
   canonical isomorphisms between iterated and composite base changes of `A`.
2. Unique parameter isomorphisms on overlaps, from
   `SmoothFamilyUniversalComparisonStatement` (proof task
   `6bd3a08a-6191-4308-8df4-b928b7fe3fc1`). That statement needs one
   parameter to be quasi-separated; overlap parameters are quasi-separated
   because abelian schemes are separated and `S` is quasi-separated.
   Uniqueness of these isomorphisms gives the cocycle condition for the
   parameter schemes.
3. That comparison gives only `Nonempty` family isomorphisms. A cocycle for
   the families needs actual uniqueness of rigidified isomorphisms
   (`RigidifiedIsoUniquenessStatement`, proof task
   `e0c0560c-6851-48c0-9e92-2d5b0d6af6a2`). Class-level Zariski separatedness
   (`RigidifiedClassesZariskiSeparatedStatement`, proof task
   `f34bab0f-25a2-40c7-a05c-6c0f06ed4283`) does not supply effective descent.
   Effective Zariski descent, that is object gluing, of actual rigidified line
   bundles is a missing statement with no current owner. Morphism gluing is
   tasks `16d8f979-ba00-4cf2-a264-f2e26049d79a` and
   `e1c23c06-e85c-48cb-b86f-6f3b5ccbbf40`.
4. Gluing of the actual parameter schemes over `S` along the cocycle, and
   descent of smoothness, properness and geometrically connected fibres, using
   Mathlib's scheme gluing and morphism gluing.
5. Gluing of the group structures. The overlap isomorphisms need not respect
   the arbitrary local group laws or unit sections. One route re-centres each
   local law at the classifying map of the trivial class and applies
   arbitrary-base pointed-morphism rigidity
   (`Langlands.AbelianScheme.PointedMorphismRigidity`, task
   `014e89e9-670d-40d8-8e52-26f62f6a0116`) so that the isomorphisms become
   group homomorphisms and the group laws glue.
6. The two conjuncts of the global predicate. Global smooth-family
   membership is checked at geometric points of the glued parameter, each of
   which factors through some local parameter. Global classification on a
   quasi-separated test uses its open subschemes over the cover members,
   local existence and uniqueness, morphism gluing, and Zariski separatedness.

Each substantial missing input is to become its own focused statement and
proof task after coordination with its current owner. All existing operator
pauses and separate ownership remain in force, including tasks
`052750df-cf2f-43ff-b892-80dcc6125078`,
`b879dd05-2261-4214-a0d1-57cdb62b5634`,
`f38215ec-58a9-488f-8fd0-305952a3db2b`,
`9d039bac-24d3-4106-869b-bd98894b444d`,
`4103d548-09ec-41f9-ab1e-1714a6838a09`,
`f34bab0f-25a2-40c7-a05c-6c0f06ed4283` and
`c8d28806-2733-4037-8503-633a7b12a5f6`. The last of these glues along covers
of a test scheme, not of the base.
