# Optimal points of the coordinate affine \(A_2\) alcove

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Example
13.4.3, printed p. 473 / PDF p. 504, starts in the apartment of the
diagonal torus of split \(\mathrm{SL}_3\), with coordinates \(a,b\)
given by the finite simple roots. We implement the calculation on that
coordinate arrangement, using the Library's Definitions 13.4.1–13.4.2
in `KPOptimalPoints`. The example provides the arrangement; this module
does not construct the building or prove a coordinate comparison for
an actual algebraic group.

## Roots, chamber and rational points

In the namespace `Langlands.Geometry.Building.AffineRootSystem.A2Alcove`,
`coordinate` consists of the affine functionals
\(u_0=a,\;u_1=b,\;u_2=1-a-b\) on \(\mathbb R^2\).
`roots` takes all integer translates of each \(u_i\) and \(-u_i\).
Since \(u_2=1-(a+b)\), this is the integer-shift arrangement of
\(\pm a,\pm b,\pm(a+b)\) in the source. Write \(v_i=1-u_i\) for
`complement i`. `center` is the point \((1/3,1/3)\), where each
\(u_i=1/3\) and no root vanishes (`regular_center`).

- `rootPeriod_roots`: translation by one preserves the arrangement.
  Any positive rational period takes \(a\) to another root, whose
  value at the origin is integral; the period is therefore at least
  one.
- `mem_facetClosure_center`: the closed facet is the triangle cut out
  by \(u_i\ge 0\) for all \(i\). Every point of the closed facet has
  these three weak signs. Conversely, the \(u_i\) sum to one, so they
  all lie in \([0,1]\) on the triangle. Each \(\pm u_i+n\) there has the
  sign of its value at `center` or is zero, by separating \(n\le-1\),
  \(n=0\) and \(n\ge1\).
- `mem_positiveRootsBelowPeriod_center`: \(\Sigma\) consists of the
  six roots \(u_i,v_i\). At `center`, the only shifts with value
  strictly between zero and one are \(u_i+0\) and \(-u_i+1\). A
  root's sign and its shift by minus one have the same respective
  signs throughout the open chamber as they do at `center`.
- `isRationalPoint_iff`: root rationality is equivalent to \(a,b\)
  both being rational. Necessity evaluates the two roots \(a,b\);
  sufficiency uses the integral translations and the formula for
  \(u_2\).

## Optimizers and the seven-point set

For a nonempty set of vertices \(I\subseteq\{0,1,2\}\),
`faceBarycenter I` is the point with coordinates \(u_i=1/|I|\) on
\(I\) and zero off \(I\) (`coordinate_faceBarycenter`). Vertices
\(0,1,2\) are \((1,0),(0,1),(0,0)\), respectively. The points are
root-rational and in the triangle. `faceBarycenters` forms their image
as a `Finset` over the nonempty subsets of the three indices.
`card_faceBarycenters` proves it has exactly seven points: the positive
coordinates recover \(I\), and the power set has \(2^3\) elements
before removing the empty face.

`isOptimalPointFor_coordinates_iff` proves that for any nonempty
\(I\), the root set \(\{u_i : i\in I\}\) has the unique optimal point
`faceBarycenter I`. The selected coordinates have sum at most one,
so their minimum is at most \(1/|I|\). At an optimizer each selected
coordinate must be at least \(1/|I|\); since the total is one and the
others are nonnegative, every coordinate must equal its weight at
the barycenter. Taking \(I=\{0\},\{1\},\{0,1\},\{0,1,2\}\) gives
four of the individual calculations in the example.

`isOptimalPointFor_complement_iff` identifies the optimal points for
\(\{v_i\}\) with the rational points on the opposite edge \(u_i=0\).
The root is at most one and reaches one at a vertex of that edge.
For \(i=2\), this is the \(a+b\) assertion in the example with the
rationality requirement of Definition 13.4.2 retained: the *real*
maximizer set is the whole edge \(a+b=1\), but only its rational
points are optimal in that definition. The authors' corrections of
1 November 2024 do not amend §13.4 (Chapter 13 entries, PDF p. 49);
this restriction is a consequence of the printed definition.

`exists_optimal_mem_faceBarycenters` proves that the fixed seven-point
set contains an optimal point for **every nonempty** `Finset` contained
in \(\Sigma\). `exists_optimal_faceBarycenter` finds the index of a
suitable face by writing a given root set as selected coordinates
\(u_i\) for \(i\in I\) and selected complements \(v_j\) for \(j\in J\).

- If \(I\) is empty and \(J\) omits an index, the vertex at that
  index has value one on all selected roots, the upper bound on the
  triangle. If \(I\) is empty and \(J\) contains all three indices,
  the average of the complements is \(2/3\), attained by each at the
  center.
- If \(I=\{i\}\) and \(i\notin J\), the vertex \(i\) gives value one
  on all selected roots. If \(i\in J\), the pair \(u_i,1-u_i\) bounds
  the minimum by \(1/2\). A midpoint of an edge containing vertex
  \(i\) attains \(1/2\) on \(u_i\), and gives every complement at
  least \(1/2\).
- If \(|I|\ge2\), the minimum over the coordinates in \(I\) is at
  most \(1/|I|\). At their face barycenter all selected coordinates
  attain this bound and every complement is at least
  \(1-1/|I|\ge 1/|I|\).

These finite-coordinate arguments are derived verifications of the
example. They give neither a building-wide set of translates nor the
Lie-lattice conclusion of Lemma 13.4.4. No external code is adapted.
