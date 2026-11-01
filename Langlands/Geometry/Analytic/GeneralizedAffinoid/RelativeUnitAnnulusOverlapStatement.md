# The actual overlap as a closed principal quotient of the unit annulus

Authors: Worker 105 and Worker 948. This statement isolates the comparison
of two existing closed-equation quotients. It defines a proposition to
prove; it supplies neither its proof nor a premise for the binary Laurent
gluing statement.

## The complete proposition

`Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus.OverlapPresentationStatement.{u}`
quantifies internally over every `K : Type u` with its given
`NormedField`, `IsUltrametricDist` and `CompleteSpace` instances, every
`A : PresentedAffinoidAlgebra K`, and every `f : A`. Let

\[
U=\mathrm{RelativeUnitAnnulus.Algebra}\ K\ A,\qquad
O=\mathrm{BinaryLaurent.Overlap}\ K\ A\ f,\qquad
F=\mathrm{RelativeUnitAnnulus.toOverlap}\ K\ A\ f.
\]

These are the published actual carriers and map. Writing
`T₂ = GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 2)) A`,
`C` for its constant series map and `X,Y` for its two coordinates,

\[
U=T_2/\overline{\operatorname{span}\{XY-1\}},\qquad
O=T_2/\overline{\operatorname{span}\{X-C(f),C(f)Y-1\}}.
\]

Both norms are their inherited quotient norms. If \(b,x,y\) are the
published annulus `baseMap`, `annulusX` and `annulusY`, the map `F`
already sends them to the overlap coefficient map `overlapBase` and the
two overlap coordinates `overlapX`, `overlapY` (published lemmas
`toOverlap_baseMap`, `toOverlap_annulusX`, `toOverlap_annulusY`). It is
the published bounded map, not an existentially chosen substitute.

The proposition is the conjunction of exactly three conclusions:

1. `Function.Surjective (toOverlap K A f)`: `F` is surjective onto the
   actual overlap.
2. Its ring-homomorphism kernel is the closed principal ideal
   \[
   \ker(F)=\overline{\operatorname{span}\{x-b(f)\}}\quad\text{in }U.
   \]
   The left side in Lean is
   `RingHom.ker (toOverlap K A f).toAlgHom`. The right side is
   `(Ideal.span {annulusX K A - baseMap K A f}).closure`: ideal
   generation followed by the topological ideal closure for the existing
   annulus quotient norm.
3. For every `o : O` and every real `ε > 0`, there exists `z : U`
   with `F z = o` and `‖z‖ < ‖o‖ + ε`.
   Together with the already published contractivity
   `norm_toOverlap_le`, this gives arbitrarily close lifts for the
   original quotient norms. Exact attainment of a minimum is not asserted.

All three are conclusions to be proved, not premises. No new quotient
type or algebra equivalence is constructed by this statement; the title
describes its surjectivity, kernel and norm conclusions, which together
say that `O` is the closed principal quotient of `U` by `x-b(f)` with
its quotient norm.

The base need not be strict, Noetherian, nonzero or reduced, the field
valuation need not be nontrivial, and `f` may be zero or nilpotent. No
bound on `‖f‖` or spectrum-point assumption occurs. A zero overlap is
allowed (for instance when `f` is nilpotent, `C(f)Y` is nilpotent, so
`C(f)Y-1` is a unit of `T₂`). Completeness of `K` is
required because the published map `toOverlap` is defined only under
`CompleteSpace K`. No normal form, closedness of the ordinary principal
ideal, injectivity, comparison, exactness or gluing assertion is a
premise.

## Internal derivation and source context

This target is an internal presentation comparison suggested by the
existing equations. In `T₂`, put `g = X-C(f)` and `h = C(f)Y-1`.
The polynomial identities

\[
XY-1=Yg+h,\qquad h=(XY-1)-Yg
\]

show that the ordinary generated ideals
`span{XY-1, g}` and `span{g,h}` coincide. A future proof must justify the
corresponding statement for closures and for the actual quotient map.
It must also identify the published two-variable coefficient evaluation
`toOverlapSeries` with the existing overlap projection, for example using
relative bounded-homomorphism uniqueness. The approximate lift should
then follow from `RelativeRelations.exists_representative_norm_lt` for
`O` and contractivity of the annulus projection. None of those
comparison steps is proved by this proposition definition.

The source context is Piotr Achinger, *Introduction to non-Archimedean
Geometry*, November 22, 2020, registered as
`achinger-2020-non-archimedean-geometry-nov22`, SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`,
retained at
`/home/taskhub/pilot/literature/Piotr Achinger, Introduction to non-Archimedean Geometry (November 22, 2020).pdf`.
Printed p.6 and pp.63–65 were read. In the proof of Proposition 7.1.1 on
p.64 the source writes
\(A\langle f,f^{-1}\rangle = A\langle X,Y\rangle/(X-f,fY-1)
= A\langle X,X^{-1}\rangle/(X-f)\) with
\(A\langle X,X^{-1}\rangle = A\langle X,Y\rangle/(XY-1)\), and uses this
in its exact-sequence argument. This statement is the Library's version
of the second equality for its actual relative carriers: since the
Library quotients are by closures of generated ideals, the kernel is
stated with the closure, and the norm conclusion records the quotient
norm comparison. The specific closed-kernel and approximate-lift
interface is internal to this Library; it is not attributed as a
separate source theorem. The source assumes a complete, nontrivially
valued field (p.6) and affinoid algebras; this target omits the
nontrivial valuation hypothesis and allows any presented affinoid base,
because its intended proof uses only polynomial relation identities and
closed quotient properties. No errata for this source are registered.

## Separate obligations

The ordinary ideal generated by `x-b(f)` is not asserted to be closed;
the closure in conclusion 2 is essential to the stated general scope.
Replacing it by the ordinary ideal over a strict Noetherian Banach base
requires a separate proved closed-ideal result. Injectivity of
multiplication by `x-b(f)` is also separate. The Laurent coefficient
normal form, principal-relation sequence, scalar descent and gluing
remain outside this statement. In particular, surjectivity of `F` from
the annulus does not state surjectivity of the difference map from the
upper and lower quotients. The independent strict/relative binary
diagram comparison has different carriers and is not supplied here.
