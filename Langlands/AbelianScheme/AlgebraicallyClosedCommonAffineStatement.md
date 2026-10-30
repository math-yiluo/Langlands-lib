# Common affine neighbourhoods of two closed points of an abelian group scheme

`Langlands.GroupScheme.AlgebraicallyClosedCommonAffineStatement` is a
universe-polymorphic `Prop`-valued definition. It states the common-affine-open
lemma used in Milne's proof of Theorem 7.1 over an algebraically closed field.
This module supplies no proof.

For every universe `u`, every field `K : Type u` with `IsAlgClosed K`, every
actual `G : Grp (Over (Spec (CommRingCat.of K)))`, and every commutativity
instance `IsCommMonObj G.X`, it asserts

```text
Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
  ∀ x y : G.X.left, IsClosed ({x} : Set G.X.left) → IsClosed ({y} : Set G.X.left) →
    ∃ U : G.X.left.Opens, IsAffineOpen U ∧ x ∈ U ∧ y ∈ U.
```

The field, the instance `IsAlgClosed K`, the group object, the commutativity
instance and the three geometric hypotheses are exactly the binders and
hypotheses of the published
`Langlands.GroupScheme.AlgebraicallyClosedSeparatingLineBundleStatement`
(module `Langlands.AbelianScheme.AlgebraicallyClosedSeparatingLineBundleStatement`)
and of `Langlands.GroupScheme.AlgebraicallyClosedProjectivityStatement`. This
module imports neither statement, and it imports only Mathlib.

## The conclusion

- `x` and `y` are points of the underlying topological space of the actual
  scheme `G.X.left`. The hypotheses `IsClosed ({x} : Set G.X.left)` and
  `IsClosed ({y} : Set G.X.left)` say that they are closed points. This is the
  condition defining Mathlib's set `closedPoints G.X.left`.
- `U : G.X.left.Opens` is an open subset of `G.X.left`. `IsAffineOpen U` is
  Mathlib's predicate saying that the open subscheme on `U` is an affine
  scheme. `x ∈ U` and `y ∈ U` are membership of the points in this open set.
- The points need not be distinct. The case `x = y` is included, and there it
  only asks for an affine open neighbourhood of `x`.

No affine chart, rational point, translation or other witness is part of the
data. The affine open is existentially quantified.

## Original source: Milne, proof of Theorem 7.1, p.11

The original is J. S. Milne, *Abelian Varieties*, the 1986 *Arithmetic
Geometry* article, author corrected version January 2, 2022. It is
registered as `milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`,
retained as
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
Printed and one-based PDF page numbers agree. Pages 2, 3, 10, 11 and 42 were
read directly.

Theorem 7.1 (p.10) states: "Every abelian variety is projective." The proof
first treats an abelian variety `A` over an algebraically closed field. On
p.11 it reduces the construction of a very ample linear system to two
observations. The first is: (i) for every closed point `a ≠ 0` of `A` there
is a prime divisor `Z` with `0 ∈ Z` and `a ∉ Z`. Milne writes that its proof
"will be equally obvious once we have shown that 0 and a are contained in a
single open affine subset of A". He then proves that claim:

> Let U again be an open affine neighbourhood of 0, and let U+a be its
> translate by a. Choose a closed point u of U ∩ (U+a). Then both u and u+a
> lie in U+a, and so U+a−u is an open affine neighbourhood of both 0 and a.

The present statement is this claim.

### How the Lean statement is derived from the source

The following comparisons explain the formulation; this module proves none of
them in Lean.

- **Closed points.** Milne's `0` and `a` are closed points of `A`. His
  conventions (p.2) identify a `k`-rational point with a closed point `v`
  satisfying `k(v) = k`. Over an algebraically closed `K` and for `A` of
  finite type, every closed point has residue field `K`. Mathlib's
  `AlgebraicGeometry.pointEquivClosedPoint` (in
  `Mathlib.AlgebraicGeometry.AlgClosed.Basic`), for a structure morphism that
  is locally of finite type, is a bijection between the sections
  `Spec K ⟶ X` of the structure morphism and `closedPoints X`. Smoothness
  gives local finite type. So the topological closed points of the Lean
  statement are exactly Milne's closed points, and each is the image of a
  unique rational point. The statement is phrased through closed points, as
  Milne phrases it. Rational-point witnesses are not part of it.
- **From `0, a` to arbitrary `x, y`.** Milne treats the identity `0` and a
  closed point `a ≠ 0`. The Lean statement takes two arbitrary closed points.
  Translation reduces it to Milne's case. Translation by a rational point is
  an automorphism of the scheme, so it carries affine opens to affine opens
  and closed points to closed points. If `V` is an affine open containing `0`
  and `y − x`, then its translate `V + x` is an affine open containing `x`
  and `y`. The same translation argument also applies directly: start from an
  affine open `U ∋ x`, choose a closed point `u` of `U ∩ (U + (y − x))`, and
  take `U + (y − x) + (x − u)`. This open set contains `u + (x − u) = x` and
  `u + (y − x) + (x − u) = y`. This generalization is derived provenance.
- **Distinctness.** Milne assumes `a ≠ 0` only because observation (i) is
  about such points. His argument does not use it. The Lean statement allows
  `x = y`; in that case it follows because affine opens form a basis of every
  scheme.
- **Translation.** Milne's `U + a` is the translate of `U` by the group law.
  The published Library translation is `Langlands.GroupScheme.translation`
  (module `Langlands.AlgebraicGeometry.Picard.GeometricPicardZero`), left
  multiplication by a section `Over.mk (𝟙 S) ⟶ G.X`, built from the actual
  group law of `G`. Under `IsCommMonObj G.X` left and right translations
  agree, so Milne's additive `U + a` is this left translation. The instance
  is kept to match the parent statement; Milne's Corollary 2.4 (p.3) shows
  that the group law of an abelian variety is commutative anyway.
  Commutativity is not essential to the argument. Without it, one takes the
  right translate `U · a`, which contains `a`, and chooses a closed point `u`
  of `U ∩ U · a`. Then `u` and `u · a` both lie in `U · a`, and left
  translation by `u⁻¹` carries `U · a` to an affine open containing the
  identity and `a`.
- **Why `U ∩ (U + a)` has a closed point.** Over an algebraically closed
  field, an abelian variety is irreducible, so two nonempty open subsets
  meet. A scheme of finite type over a field is Jacobson, so the nonempty
  open intersection contains a closed point.

## From the actual group scheme to Milne's variety convention

The passage is the same as for the parent separating-line-bundle statement.
The opening definition of Section 20, p.42, calls a group scheme over `S` an
abelian scheme if it is proper and smooth with connected geometric fibres;
for `S = Spec K` this gives the three geometric hypotheses. They are kept in
the parent's form; `GeometricallyConnected` is not replaced by connectedness.
Mathlib's `GeometricallyConnected` asks for connectedness, including
nonemptiness, after every field-valued base change.

Milne's conventions, p.2, take a scheme over `k` to be of finite type and a
variety over `k` to be a separated scheme of finite type whose base change to
`k̄` is integral. A group variety has multiplication, inverse and a rational
identity `ε ∈ V(k)`. On p.3, a complete connected group variety is called an
abelian variety. The translation `t_a` by `a ∈ V(k)` maps `V` to itself
(p.3).

The variety properties that Milne's argument uses are recorded in a separate
published statement,
`Langlands.GroupScheme.FieldAbelianVarietyPresentationStatement` (module
`Langlands.AbelianScheme.FieldAbelianVarietyPresentationStatement`). For a
commutative smooth proper geometrically connected group scheme over any
field, it asserts local finite type, quasi-compactness, separatedness,
nonemptiness and geometric integrality of the structure morphism. It is a
statement, not a proof. Its proof is owned by task
`2d28e6bb-86ce-4f1e-8ab2-c7264d1cbef3`, which reuses the geometric-integrality
proof task `13d3f4b1-fadd-43c6-b422-d793dc9adf5f`. The present module neither
imports nor assumes it.

The facts that Milne's argument actually needs are irreducibility and closed
points in nonempty opens. The published Library module
`Langlands.AbelianScheme.SeparatingLineBundle.RationalPoints` already proves
them, for the same hypotheses:
`Langlands.GroupScheme.SeparatingLineBundle.irreducibleSpace_of_smooth_of_isProper`
shows that `G.X.left` is irreducible, and
`Langlands.GroupScheme.SeparatingLineBundle.exists_rationalPoint_mem_of_isOpen`
supplies a rational point whose underlying point lies in each of finitely
many nonempty open subsets. These are cited here only as existing owners of
the prerequisites; this module does not import them.

Dimension zero is not excluded. Mathematically, a connected smooth proper
group scheme of dimension zero over an algebraically closed field is
isomorphic to `Spec K`, which is affine, so `U` can be the whole scheme.

## Errata

The complete [author errata](https://www.jmilne.org/math/articles/1986b.html)
were read in the registered retained original
`milne-abelian-varieties-1986-errata-2026-10-25`, SHA256
`e206fed351fc3d740772f2c1d3275e877552393fafc1644c6c2f38fedd1d9a55`, file
`literature/J. S. Milne - Abelian Varieties (1986 article errata, HTML snapshot 2026-10-25).html`.
The page states that all listed corrections are incorporated into the
xnotes version used here. Its entries are keyed to pages of the printed 1986
article (pp.103–150). The first entry, for printed p.104, replaces a
lowercase `w` by `W` in a displayed equation; in the xnotes version this
appears to be the display in the hypothesis of Theorem 2.1 (p.3), which
already reads `W` and is not used here. All other entries concern printed
pp.119–145. They lie after Section 7: the entry for printed p.122 concerns
Proposition 12.1, and by the xnotes table of contents Section 7 occupies
pp.10–11 while Section 12 begins on p.19. So no entry concerns the
conventions or Theorem 7.1. The latest entries, for printed p.145, correct a
denominator and the series `−log(1−t) = t + t² + ⋯`; neither occurs in the
definition of an abelian scheme used here. No source-specific project errata
note exists for either registered source in the current Library.

## Provenance and scope

The provenance is derived. Milne's claim for `0` and a closed point `a ≠ 0`
of an abelian variety over an algebraically closed field is generalized by
translation to two arbitrary, possibly equal, closed points. It is translated
through Section 20's group-scheme presentation and the conventions of
pp.2–3. The hypotheses are exactly those of the parent separating-line-bundle
statement.

The statement covers every universe, every characteristic and dimension
zero. It adds no finite-type, separatedness, integrality, irreducibility,
chosen affine chart, rational-point witness, projectivity, quasi-projectivity
or ampleness hypothesis, and does not assume the desired affine
neighbourhood. These consequences are left to the proof.

This statement is a prerequisite of the separating-line-bundle statement,
which in turn is intended to give projectivity. Its proof must therefore not
use projectivity, quasi-projectivity, ample line bundles or any of their
consequences, for example
`Langlands.GroupScheme.AlgebraicallyClosedProjectivityStatement`,
`Langlands.GroupScheme.FieldAmpleExistenceStatement` or
`Langlands.GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement`.
After independent acceptance and publication, a separate exact-target proof
must have this entire named proposition as its type, with no extra outer
hypotheses. This module adds no axiom.
