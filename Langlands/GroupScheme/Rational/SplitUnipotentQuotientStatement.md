# Images and sections of split-unipotent quotients

## Fppf-epimorphic images of split unipotent groups

`Langlands.GroupScheme.SplitUnipotentFppfQuotientStatement.{u}` is a
Prop-valued statement for every universe `u`. Let `k : Type u` be a field and
let `φ : H ⟶ Q` be a homomorphism of actual group schemes over
`Spec (CommRingCat.of k)`. The source `H` must satisfy:

- `IsAffineHom H.X.hom`, `LocallyOfFiniteType H.X.hom` and `Smooth H.X.hom`;
- its underlying space `H.X.left` is connected;
- it satisfies the published `RelativeRoot.IsSplitUnipotent`.

The target `Q` must satisfy `LocallyOfFiniteType Q.X.hom`. The map `φ` must be
surjective as a map of fppf sheaves, in the following explicit form. For every
scheme `T` over the base and every point `y : T ⟶ Q.X`, there are a scheme `V`
over the base and a morphism `v : V ⟶ T` over the base with three properties:
the underlying scheme morphism `v.left` is flat, surjective and locally of
finite presentation, and some point `x : V ⟶ H.X` satisfies
`x ≫ φ.hom.hom = v ≫ y`. The statement asserts
`RelativeRoot.IsSplitUnipotent Q`.

`IsSplitUnipotent` is imported unchanged. It asks for a finite
`RelativeRoot.HasSplitSeries` whose endpoint is trivial on all tests. Each step
of that series has a smooth, connected, normal closed kernel and a represented
fppf quotient whose all-test point functor is naturally the one-dimensional
additive group. The statement places no perfectness or characteristic
restriction on `k`. It does not assume that `φ` is flat, or that `Q` is
smooth, connected, quasi-compact or separated. Mathematically, no separatedness
hypothesis is needed, since group schemes over a field are separated.

### Provenance

This is a derived interface statement. It isolates the quotient half of the
argument needed to prove `SplitNormalFppfProductStatement`, which in turn feeds
`SplitUnipotentRadicalExistenceStatement`.

The source is Milne, *Algebraic Groups* (2017), §16.g, printed p.343
(PDF p.359): "Quotients of split solvable groups are split because nontrivial
quotients of `Ga` and `Gm` are isomorphic to `Ga` or `Gm` (Exercise 14-3)."
For unipotent groups the same argument uses only `Ga`. A quotient of a split
unipotent group therefore has a subnormal series whose quotients are `Ga`, and
it is split in the sense of Definition 14.61 (printed p.299, PDF p.315). By
14.62 on the same page, such a group is smooth and connected.

Milne's Definition 5.5 (printed p.99, PDF p.115) defines a quotient map of
algebraic groups as a faithfully flat homomorphism. Proposition 5.43
(printed p.109, PDF p.125) shows this is equivalent to the image functor
`R ↦ φ(H(R))` being fat in `Q`: every point of `Q` lifts to `H` after a
faithfully flat extension. The proof of Proposition 5.7 (printed p.99) makes the
extension a finite union of affine opens of the fibre product, so it may be
taken fppf. The Lean hypothesis is this fppf lifting condition, stated for
arbitrary relative schemes `T`. It is used instead of flatness of `φ` because
the intended application obtains `φ` from a represented fppf product. There,
the lifting property is immediate, while flatness is not.

The hypotheses on `H` follow Milne's setting of algebraic groups. Affineness,
local finite type, smoothness and connectedness are all part of the intended
application, where `H` is a closed smooth connected subgroup of an affine
locally finite-type group. Milne's Definition 14.61 uses arbitrary subnormal
series. The published `HasSplitSeries` uses finite series in which each
represented kernel is normal in its immediate predecessor and each quotient map
is an fppf quotient.

Registered source: `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0` (printed
page `p` is PDF page `p + 16`).

The file defines a proposition and supplies no proof.


## Scheme sections of quotients by split unipotent normal subgroups

`Langlands.GroupScheme.SplitUnipotentQuotientSectionStatement.{u}` is a
proposition target for the normal-subgroup case of Springer's Theorem
14.2.6(i). This file states the target; it does not prove it.

Let `k` be any field and let `G` be a smooth connected affine solvable group
scheme over `k`. Let `n : N ⟶ G` be a smooth connected closed normal
unipotent subgroup that is split over `k`. Given an actual smooth affine
group scheme `Q` and a represented fppf quotient `q : G ⟶ Q` with kernel
equal to the range of `n` on every test scheme, the target asserts that
there is a morphism over `k`

```text
s : Q.X ⟶ G.X,     s ≫ q.hom.hom = 𝟙 Q.X.
```

Thus the underlying scheme morphism of `q` has a section. The section
carries no requirement to preserve multiplication. Evaluating it at a
`k`-point of `Q` gives a `k`-point of `G` above that point; the statement
does not assume pointwise surjectivity of an arbitrary fppf quotient.

The predicates are the existing Library definitions:

- `IsSolvableGroupScheme` tests solvability on algebraic-closure points.
- `IsUnipotent` is the existing group-scheme unipotence predicate.
- `RelativeRoot.IsSplitUnipotent` asks for a finite normal series with
  actual represented fppf quotients naturally isomorphic to the additive
  group on every test scheme.
- `RelativeRoot.IsFppfQuotient` requires flatness, surjectivity and local
  finite presentation of the actual scheme morphism, and equality of its
  all-test kernel range with the specified subgroup functor.

The smooth affine hypotheses put `G`, `N` and `Q` in the finite-type
algebraic-group setting of the source: `N` is a closed subgroup of the
affine `G`. The source's split-unipotent normal series is represented by
the Library's finite Ga-series predicate. The fppf quotient and exact
kernel formulation expresses the represented sheaf quotient. A proof
must identify this quotient with the source's `G/N` and transfer its
section to the supplied `Q`; that identification is part of the proof
obligation.

The provenance is **derived**. Springer, *Linear Algebraic Groups*,
second edition (1998), Theorem 14.2.6(i), printed pp.242–243 (PDF
pp.256–257), proves the existence of a section of `G ⟶ G/H` for a
connected split unipotent subgroup `H` of a connected solvable group over
the ground field. The paragraph immediately preceding that theorem
defines the section as a morphism of varieties over that field. The
present target restricts to normal `H = N` and supplied smooth affine
group quotient models, and uses the existing group-scheme predicates.
Theorem 14.4.3, printed p.250 (PDF p.264), uses 14.2.6 to lift rational
points in its induction for maximal-torus conjugacy.

Every field and characteristic is retained, including finite and
imperfect fields. The ambient group and its tori have no splitness
assumption. This prerequisite supplies only quotient sections; the full
rational conjugacy theorem remains a separate proof obligation.
