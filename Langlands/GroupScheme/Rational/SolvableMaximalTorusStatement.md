# Rational conjugacy of maximal tori in smooth connected solvable groups

Author: Worker 274.

`Langlands.GroupScheme.SolvableMaximalTorusConjugacyStatement.{u}` defines
the rational conjugacy assertion for maximal tori of a smooth connected
solvable affine group over every field `k : Type u`. This module supplies
the proposition to be proved in a separate proof task.

## Original source

T. A. Springer, *Linear Algebraic Groups*, second edition, Progress in
Mathematics 9, Birkhäuser (1998), registered source
`springer-1998-linear-algebraic-groups`, SHA-256
`44d69662b47d85998f4e65baba1dd1454a3a30e065bcd58342c227d59a73aabf`.
The retained file is
`/home/taskhub/central-library/Springer--Linear algebraic groups (book, 2nd edition)--1998.pdf`.
Printed page numbers are PDF page numbers minus 14.

- Theorem 14.4.3, printed p.250 (PDF p.264), asserts that two maximal
  `F`-tori of `G` are conjugate by an element of `G(F)`.
- The standing hypothesis at the start of §14.4, printed p.248
  (PDF p.262), makes `G` a connected solvable `F`-group.
- Theorem 13.3.6 and Remark 13.3.7, together with the paragraph immediately
  following the remark, printed p.231 (PDF p.245), identify maximal
  `F`-subtori with maximal geometric tori defined over `F`. The theorem is
  first stated for infinite `F`; the remark covers finite `F`.
- §13.1 and Proposition 13.1.1(ii), printed p.223 (PDF p.237), describe
  `F`-tori and their splitting over a separable closure.

The scanned original pages were read. No project errata file for this source
was present when this statement was prepared.

## Exact scheme statement

Let `S = Spec (CommRingCat.of k)`. The definition quantifies over every
`k : Type u` with `[Field k]`, then every `G : GroupScheme S` with
`[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]` and
`[ConnectedSpace G.X.left]`. Given `IsSolvableGroupScheme G`, it asserts
that for every `T T' : CommGroupScheme S` and every pair of homomorphisms
`i : T.toGrp ⟶ G`, `i' : T'.toGrp ⟶ G`,
`IsMaximalTorus i` and `IsMaximalTorus i'` imply
`SubgroupConjugate i i'`.

The unchanged predicate `SubgroupConjugate` expands to

```lean
∃ (g : Over.mk (𝟙 S) ⟶ G.X) (e : T.toGrp ≅ T'.toGrp),
  i ≫ (G.innerIso g).hom = e.hom ≫ i'
```

Thus the conjugator is an actual rational point, a section of `G` over
`Spec k`, and `e` is an actual isomorphism of the source group schemes.
For the closed embeddings supplied by maximality, the equation expresses
Springer's equality of conjugate subgroups: conjugation by `g` carries the
image of `i` onto the image of `i'`. The equation concerns morphisms of group
schemes, hence their values on every test scheme.

All field characteristics, finite fields and imperfect fields are included.
The ambient group and its tori need not split over `k`.

## Correspondence with the unchanged predicates

The smooth affine hypotheses put the ambient group in the setting of
Springer's linear algebraic `F`-groups. An affine smooth morphism to a field
is of finite type; the connectedness hypothesis records the connected
group in §14.4. Here Springer's `F` is the arbitrary field `k`.

`IsSolvableGroupScheme G`, imported from
`Langlands.GroupScheme.Absolute.Borel`, says that the abstract group of
`AlgebraicClosure k`-points of the base change of `G` is solvable. Its
published correspondence with solvability of smooth affine algebraic groups
is used unchanged.

`IsTorus`, as defined in `Langlands.GroupScheme.Torus.Lattice`, says that
the group scheme becomes a finite product of copies of `𝔾_m` after some
field extension `K : Type u` with `Algebra k K`. This is the usual torus
condition; it permits tori that are not split over `k`. Geometrically such
tori split over an algebraic closure, and Springer's Proposition
13.1.1(ii) gives splitting over a separable closure.

`IsMaximalTorus i`, imported through
`Langlands.GroupScheme.Torus.Maximal`, requires `IsTorus T.toGrp`, the
closed-immersion condition `IsClosedSubgroup i`, and maximality among
closed torus embeddings defined over `k`: if
`f : T.toGrp ⟶ U.toGrp` and `j : U.toGrp ⟶ G` satisfy
`IsTorus U.toGrp`, `IsClosedSubgroup j` and `f ≫ j = i`, then `f` is an
isomorphism. This records containment using maps rather than a chosen
subgroup object.

This last condition is rational maximality: its quantifiers range over
`k`-defined tori. Geometric maximality instead tests maximality after base
change to an algebraic closure. These conditions are not definitionally
identical. Springer explicitly identifies the two notions for `F`-subtori
in the paragraph following Remark 13.3.7, including finite fields. This
identification explains why Theorem 14.4.3 supplies the intended original
theorem for the Library's rational maximality predicate. The scheme
comparison remains a genuine obligation for a future formal proof; this
statement adds no comparison or conjugacy assertion as a premise.

The declaration is the source theorem expressed through the existing
scheme predicates and rational conjugacy relation. The module imports
`Absolute.Borel` and `Rational.SubgroupConjugacy`; it has no dependency on
the general smooth maximal split torus conjugacy statement or its proof.
