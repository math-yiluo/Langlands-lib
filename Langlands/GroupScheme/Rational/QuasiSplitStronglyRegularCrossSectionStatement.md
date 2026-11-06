# A rational cross-section of the strongly regular classes

Authors: Worker 1744 and Worker 1341. The Lean definition reuses Worker 1341's
shared draft; the source explanation has been checked and revised by Worker 1744.

The paired module
`Langlands.GroupScheme.Rational.QuasiSplitStronglyRegularCrossSectionStatement`
defines the closed proposition
`Langlands.GroupScheme.QuasiSplitStronglyRegularCrossSectionStatement.{u} : Prop`.
For a simply connected quasi-split group over any field, it asserts the existence
of an affine scheme mapping to the group which meets each strongly regular
geometric conjugacy class in exactly one point, rational over the field of the
given element. This is a derived packaging of Steinberg's cross-section and its
type `A_n`, `n` even, substitute, with Borel–Springer's arbitrary-field extension.
This module supplies a statement; its proof remains a separate obligation.

## Quantifiers and hypotheses

There is one arbitrary universe `u`. The definition universally quantifies over
`K : Type u`, its `Field K` instance, and an actual group scheme
`G : GroupScheme (Spec (CommRingCat.of K))`. Its only hypotheses on `G` are
`IsSimplyConnected G` and `IsQuasiSplit G`.

The imported `IsSimplyConnected` requires semisimplicity and requires every
central isogeny onto `G` from a semisimple group over `K` to be an isomorphism.
The imported `IsQuasiSplit` requires connected reductivity and an actual Borel
subgroup over `K` which remains Borel after extension to an algebraic closure.
No torus, root datum, pinning or particular Borel is supplied as input.

The conclusion first chooses `A : Type u`, a `CommRing A` instance, an
`Algebra K A` instance, and a morphism

```lean
incl : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A))) ⟶ G.X
```

Thus `X = Spec A` is an affine `K`-scheme mapping to the underlying scheme of
`G`, over `Spec K`. These choices depend on `K` and `G` and precede every
subsequent field and point. The conclusion does not assume a cross-section as
input.

For each `E : Type u` with `Field E` and `Algebra K E`, the property applies to
every morphism `y : Spec E ⟶ G.X` over `Spec K`. There is no finiteness,
algebraicity or separability restriction on `E/K`. Finite fields and imperfect
fields of positive characteristic are included.

Write `b_E : Spec E ⟶ Spec K` for the map induced by `algebraMap K E` and
`G_E = (baseChange b_E).obj G`. The remaining inputs are an actual group scheme
`S` over `E` and a group-scheme homomorphism `j : S ⟶ G_E`. They must satisfy:

- `IsTorus S`: the group becomes a split torus after a field extension.
- `IsClosedSubgroup j`: the underlying scheme morphism is a closed immersion.
- For every test scheme `Z` over `Spec E` and every `c : Z ⟶ G_E.X`, if `c`
  commutes with the restriction of `y` to `Z`, there exists `s : Z ⟶ S.X`
  with `s ≫ j.hom.hom = c`.

In the last condition, the `E`-rational point of `G_E` corresponding to `y` is
`(baseChangeBasePointsEquiv b_E G).symm y`. Its restriction to `Z` is obtained
by precomposing with `toUnit Z`. Multiplication is the group operation on
scheme-valued points. Tests range over all `Z : Over (Spec E)`, including
nonreduced schemes, so this is containment of the scheme-theoretic centralizer
in the closed torus, rather than merely containment on field-valued points.
It is exactly the centralizer condition used in
`QuasiSplitRegularClassRationalStatement`.

To explain its meaning, apply the condition to `y` itself: since `y` commutes
with itself, it factors through `S`. Commutativity of `S` then puts every
`S`-point in the centralizer, on every test scheme. The centralizer therefore
equals `S`. Over an algebraic closure, `y` is semisimple because it lies in a
torus. A maximal torus containing `S` centralizes `y`, so lies in `S` and equals
it. Thus `S` is a maximal torus and the scheme-theoretic centralizer is that
torus: `y` is regular semisimple, or strongly regular in the sense used here.
This explanation is a mathematical interpretation, not a lemma proved by this
module.

## Unique point and extension-field conjugacy

For every such `E`, `y`, `S` and `j`, there is exactly one

```lean
n : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))
```

with the following property. There are a field `E' : Type u`, an
`Algebra K E'` instance, a morphism `q : Spec E' ⟶ Spec E` over `Spec K`, and
a point `g : Spec E' ⟶ G.X` over `Spec K`, such that

```lean
g * (q ≫ n ≫ incl) * g⁻¹ = q ≫ y
```

The morphism `n` is an `E`-point of `X`, equivalently a `K`-algebra map
`A → E`. The morphism `q` corresponds to an injective field homomorphism
`E → E'` compatible with `K`; it supplies the extension over which conjugacy
is witnessed. An `Algebra E E'` instance is not separately included in the
Lean formula. No finiteness or separability condition is imposed on this
extension either.

The `∃! n` ranges over all `E`-points of `X`. Its predicate existentially
quantifies `E'`, `q` and `g`, so two points with different extension fields or
different conjugating elements must still be equal. Neither the extension
field nor the conjugating element is asserted to be unique. This is geometric
conjugacy; a conjugating element in `G(E)` is not required.

## Sources and exact locators

Provenance: derived. All PDF page numbers below are one-based.

R. Steinberg, *Regular elements of semi-simple algebraic groups*,
Publications Mathématiques de l'IHÉS **25** (1965), 49–80,
[original Numdam PDF](https://www.numdam.org/article/PMIHES_1965__25__49_0.pdf).
Source ID: `steinberg-1965-regular-elements-semisimple-groups`.
SHA-256:
`bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`.
PDF page equals printed page minus 47.

| Passage | Printed pages | PDF pages | Content used |
| --- | --- | --- | --- |
| 1.4–1.5 | 50 | 3 | The root-subgroup cross-section `N`; differential criterion for regularity. |
| 1.6–1.7 | 51 | 4 | Rationality hypotheses, the type `A_n`, `n` even, exception, and rational elements in semisimple classes. |
| 6.10–6.11, especially 6.11(c),(d) | 64 | 17 | The character quotient `p`; the unique regular and unique closed semisimple class in each fibre. |
| 7.9, 7.14 and its proof | 68–69 | 21–22 | The restriction of `p` to `N` is an isomorphism, via triangular character coordinates. |
| 7.16(a), 8.1 | 70 | 23 | One point of `N` per fibre and the independent-differentials criterion. |
| Opening of §9, 9.2–9.5 | 72–73 | 25–26 | Perfect-field convention and construction of `N` over the ground field in the permitted cases. |
| 9.6–9.8 | 73 | 26 | The limitation on a global cross-section, the finite-piece substitute `N'`, and reduction to the two types of factors. |
| 9.11, 9.13 | 74–75 | 27–28 | Construction of `N'` from disjoint closed affine pieces and products. |
| 9.15–9.19 and the concluding proof of 9.7/9.11 | 75–77 | 28–30 | Character formulas, isomorphisms onto the strata `f = 0` and `f ≠ 0`, and rationality of the pieces. |

A. Borel and T. A. Springer, *Rationality properties of linear algebraic groups
II*, Tohoku Mathematical Journal (2) **20** (1968), 443–497,
[original publication](https://doi.org/10.2748/tmj/1178243073).
Source ID: `borel-springer-1968-rationality-properties-ii`.
SHA-256:
`e465d0622ca9540ff21e0d53d7b2fdb00a14cf70a7caceee352c040a3cb1abef`.
PDF page equals printed page minus 442.

| Passage | Printed pages | PDF pages | Content used |
| --- | --- | --- | --- |
| 8.2 | 481–482 | 39–40 | A connected reductive group with a ground-field split maximal torus is split, over arbitrary fields. |
| 8.6 | 483–484 | 41–42 | Steinberg's proof carries over to arbitrary fields for regular semisimple classes, using 8.2 and the single intersection point with multiplicity one, deduced from Steinberg 8.1. |

The cited originals and these passages were read. No source-specific errata
file was found in the supplied project or current Library notes.

## Derivation of this formulation

Over an algebraic closure, let `p : G → V` be the adjoint quotient, expressed
by the fundamental characters as in Steinberg 6.10. The quotient and the maps
used in the rationality argument descend to the ground field; the coordinates
need not individually be ground-field characters. For regular semisimple `y`,
its geometric class is the whole geometric fibre of `p`: by 6.11 the regular
class is dense and open in that irreducible fibre, and the semisimple class is
closed. Here they are the same class, so they exhaust the fibre.

If there is no simple component of type `A_n` with `n` even, Steinberg
9.2/9.4 construct `N` over the ground field. Theorems 7.9 and 7.16(a) identify
`p|N` with an isomorphism onto `V`. Consequently each quotient value of an
`E`-rational strongly regular point has one `E`-rational lift to `N`.
Geometrically it lies in the same class as `y`. The isomorphism gives a
reduced single-point fibre; the differential formulation 8.1 is the
multiplicity-one observation used in Borel–Springer 8.6.

For the exceptional type, use `N'` of Steinberg 9.7, rather than assuming the
same global section. It has finitely many disjoint closed irreducible pieces
defined over the ground field, and `p` maps each piece isomorphically onto a
subvariety of `V`. These images partition the geometric points of `V`
(9.7(b),(c)). In the single-component construction, 9.19 identifies the two
images explicitly as `f = 0` and `f ≠ 0`; 9.11 takes products for several
components. Thus an `E`-rational quotient value belongs to exactly one stratum
and has exactly one `E`-rational lift through its isomorphism. On that piece
the fibre is one reduced point. For a regular semisimple class this is its
single meeting point with `N'`; this explanation uses 9.7(c)/9.19 also for
the piece whose elements are not all regular. It does not assert that `N'`
consists entirely of regular elements.

These constructions give an affine source. In the first case `N` is closed
in the affine group `G` (1.4 and its discussion of 7.1). In the exceptional
case take the finite disjoint union of the closed pieces in 9.7/9.13; each
piece is affine, so the disjoint union is affine as well. Its map into `G`
is induced by the inclusions of the pieces. For a general simply connected
group, take the product of the two types of factors and their cross-sections,
as in the reduction in 9.8. Products and the descended affine schemes remain
affine. Their coordinate rings may be taken in the same universe `u`.
Writing this affine scheme as `Spec A` gives precisely the existential algebra
and morphism in the Lean statement.

Steinberg §9 explicitly assumes a perfect ground field. Borel–Springer 8.6
states that, using 8.2, the proof of Steinberg 1.7 carries over to arbitrary
ground fields for regular semisimple classes, with the multiplicity-one
intersection observation. Applying that extension to the same two-case
cross-section construction is the arbitrary-field part of the derived
packaging here; 8.6 does not print this Lean-shaped assertion as a separate
theorem. The reduced single point of intersection is essential over an
imperfect field: after extension to an algebraic closure its intersection
scheme is one reduced point, so its descent is `Spec E`, rather than a
nontrivial purely inseparable point. This also explains why mere uniqueness
of a geometric point would not suffice for this formulation.

The meeting point and `y` are conjugate over an algebraic closure of `E`,
which may be realized in universe `u`, providing `E'`, `q` and `g`.
Conversely, if any other `E`-point of `Spec A` becomes conjugate to `y` over
any field extension, its quotient value is `p(y)`. The isomorphism on the
unique relevant piece, or equivalently the reduced singleton intersection,
forces equality with the meeting point. Equality can be checked after a
field extension by faithful flatness. This yields the full `∃!` even when
the two conjugacy witnesses use different fields.

## Scope and consumer

The statement deliberately exposes only an affine source, unique points and
extension-field conjugacy. It gives no quotient map, root construction,
finite-type assertion on `A`, or immersion property for `incl`. It does not
state the multiplicity-one intersection as a separate scheme-theoretic
conclusion. Nothing is asserted for classes outside the strongly regular
ones.

In particular, no global `K`-rational section of the adjoint quotient is
asserted when a type `A_n`, `n` even, component occurs. The piecewise inverse
on the strata of 9.7/9.19 does not supply such a morphism on all of `V`;
Steinberg 1.6/9.4 exclude this case from the construction of `N`.

The consumer is `Langlands.GroupScheme.QuasiSplitRegularClassRationalStatement`.
For a Galois-stable strongly regular class over a finite Galois extension,
uniqueness makes its meeting point Galois invariant; affineness permits
descent through the corresponding algebra map. This module preserves the
consumer's centralizer and point conventions and imports
`CocharacterTransport`, `SimplyConnected.Basic`, `Reductive.QuasiSplit` and
`Torus.Lattice`, with the same category and group-object notation. It publishes
no proof, instance or simp lemma.
