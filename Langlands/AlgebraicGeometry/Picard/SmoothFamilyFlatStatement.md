# Flatness of a universal smooth-family Picard parameter

`Langlands.AbelianScheme.SmoothFamilyFlatStatement.{u}` is a proposition
definition. It supplies no proof. For every `S : Scheme.{u}` with
`[QuasiSeparatedSpace S]`, every `A : AbelianScheme S`, every `P : Over S` and
every `L : RigidifiedFamily A P`, it asserts

```text
IsUniversalSmoothFamilyOnQuasiSeparatedTests A L → Flat P.hom
```

Thus the structure morphism `P.hom : P.left ⟶ S` of the parameter of any actual
universal family is flat, in Mathlib's sense `AlgebraicGeometry.Flat`. The
parameter `P` and the family `L` are actual data quantified universally; no
other parameter or family is assumed to exist. The statement assumes nothing
about `P.left`: not quasi-separatedness, finite presentation, or any other
geometric property. It also has no projectivity, polarization, ordinary-Picard
representability, pullback-stability, coherence, global-functions,
normalization, noetherian or reducedness hypothesis. The universe `u` is
arbitrary.

## The imported universal predicate

`IsUniversalSmoothFamilyOnQuasiSeparatedTests` is the accepted Library
definition in
`Langlands.AlgebraicGeometry.Picard.SmoothFamilyQuasiSeparatedRepresentabilityStatement`.
This module imports it unchanged. For the given `L` it is the conjunction of:

- `IsAlgebraicallyTrivialFamilyViaSmoothFamily A L`. The rigidification of `L`
  is forgotten and the bundle is moved from `P ×_S A` to `A ×_S P`. Then for
  every algebraically closed field `K : Type u` and every morphism
  `Spec K ⟶ P.left`, the bundle on the geometric fibre has an actual witness.
  The witness is a smooth, separated, locally finite-type, quasi-compact and
  geometrically integral parameter `C` over `Spec K`, with two rational points
  `c0`, `c1` and a line bundle `N` on `C ×_{Spec K} A_K`. Its restriction at
  `c0` is isomorphic to the trivial bundle and its restriction at `c1` to the
  fibre bundle.
- For every `T : Over S` with `[QuasiSeparatedSpace T.left]` and every
  `q : AlgebraicallyTrivialClassesViaSmoothFamily A T`, there is exactly one
  `h : T ⟶ P` in `Over S` such that
  `RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
  (unitSection_comp A) L T h = q.val`.

The classifying map pulls `L` back along `h` and takes its class in
`RigidifiedClasses A T`. Two rigidified families have the same class exactly
when there is an isomorphism of rigidified bundles between them. The class
subtype uses the same geometric-fibre smooth-family condition as the first
conjunct, descended to classes. The tests include every quasi-separated
`T` in universe `u`. Among them are all affine and all nonreduced tests. The
predicate is not an arbitrary equivalence of functors, and it is not a
condition on geometric points.

## Original source

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
thesis revision March 14, 2021, is registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`. The
retained file is
`literature/Kai-Wen Lan - Arithmetic compactifications of PEL-type Shimura varieties (thesis revision, 2021-03-14).pdf`.
The following passages were read:

- Conventions, printed p.xxvi (PDF p.26): schemes almost always mean
  quasi-separated preschemes, and a geometric point is a morphism from an
  algebraically closed field.
- Definition 1.3.1.1, printed p.67 (PDF p.95): an abelian scheme is a proper
  smooth group scheme with geometrically connected fibres.
- Definition 1.3.2.1, printed p.73 (PDF p.101): the relative Picard functor is
  the quotient of line bundles on `X ×_S T` by those pulled back from the test.
  `Pic⁰(A/S)` requires each ordinary fibre `L_t`, for `t ∈ T`, to be
  algebraically equivalent to zero.
- Lemma 1.3.2.2, printed pp.73–74 (PDF pp.101–102): these functors are
  canonically isomorphic to the functors `Pic_e(A/S)` and `Pic⁰_e(A/S)` of
  isomorphism classes of bundles rigidified along `e_T`.
- Theorem 1.3.2.3, printed p.74 (PDF p.102): `Pic⁰_e(A/S)` is representable
  by an abelian scheme over `S`, the dual abelian scheme `A∨`. For the proof
  the source refers to Faltings–Chai, Ch. I, §1. Remark 1.3.2.4 notes that the
  locally projective case also follows from Hilbert schemes. Definition
  1.3.2.5 names the universal rigidified sheaf on `A ×_S A∨` the Poincaré
  sheaf.

The author's errata of March 14, 2021, are registered as
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`. The
retained file is
`literature/Kai-Wen Lan - Arithmetic compactifications of PEL-type Shimura varieties (thesis errata, 2021-03-14).pdf`.
They were read at PDF pp.1 and 8–9. Page 1 says to read the revision and
replaces the separated-scheme convention by quasi-separatedness. Page 8
corrects Definition 1.3.2.1 so that the bundles `M` lie on `T`; the revision
cited above already has this. No source-specific errata note was found under
`notes/errata/`.

The source theorem uses no polarization and no local projectivity. Its
representer is an abelian scheme, so it is smooth over `S` and therefore flat.

## Derived formulation and remaining proof obligations

This is a derived proposition, not a verbatim source theorem. Lan's
representer is not stated for an arbitrary `P` with the Library's predicate.
A future proof of this statement must, without changing it, do the following:

1. Construct, or reuse after its acceptance and publication, an actual abelian
   scheme over `S` with an actual universal rigidified family representing
   Lan's `Pic⁰_e(A/S)` on quasi-separated tests.
2. Show that the actual classes and pullbacks of that representer agree with
   `AlgebraicallyTrivialClassesViaSmoothFamily` and `classifyingMap`,
   including the global smooth-family fibre condition on its family. This
   compares Lan's ordinary residue-field algebraic equivalence with the
   Library's condition after every algebraically closed field-valued point,
   using the explicit smooth-family witnesses. It also compares the source
   quotient with the Library's actual rigidified families, and the source
   product order `A ×_S T` with the Library order `T ×_S A`. Nonreduced tests
   must be retained throughout.
3. Identify the supplied `P` with the representer by an isomorphism in
   `Over S`, using the two unique classifications on affine or quasi-separated
   tests. This must work before `P.left` is known to be quasi-separated, for
   example by affine tests and gluing.
4. Transport flatness of the smooth representer along that isomorphism.

Citing the source is not a Lean proof of these steps. The published
`SmoothFamilyQuasiSeparatedRepresentabilityStatement` asserts only that some
`P` and `L` satisfying the predicate exist. It says nothing about their
geometry, so it does not prove this proposition. Agreement of geometric
points, or flatness of the geometric fibres, does not give flatness either:
the inclusion of the origin into the affine line over a field has flat
fibres over every point, but it is not flat. A proof must not use
`RelativeDualSchemeFlatStatement` or `RelativeDualSchemeGeometryStatement`.
Those targets concern the chosen dual, and their planned proofs may use this
result, so using them here would be circular.

A separately allocated sibling statement for local finite presentation uses
the same quantifiers and predicate and concludes
`LocallyOfFinitePresentation P.hom`. Each statement asserts one geometric
property. Both need the same actual representer construction in a future
proof. Neither statement proves it.

The Lean statement and this Markdown were written by Worker 302.
