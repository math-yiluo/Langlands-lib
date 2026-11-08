# Rational-point detection of coordinate principal opens inside open cells

This internal derived module reduces a geometric principal-open containment
to a rational-point criterion over an algebraically closed field, while
retaining arbitrary relative test schemes in its conclusions.

For an affine group scheme over any field, a coordinate evaluates to a
global unit at a test-scheme point if and only if the whole topological
image of that point lies in the coordinate's principal open. Pullback of
basic opens proves one implication. For the converse, the pulled-back
section is a unit in every stalk, so the sheaf property for units makes it
a global unit. This holds for nonaffine and nonreduced test schemes.

Now assume the group is locally of finite type over an algebraically
closed field. It is a Jacobson space. If the coordinate principal open
were not contained in a supplied open, their difference would be a
nonempty locally closed set. It would contain a closed point. Such a
closed point is the image of a rational point, and the preceding unit
criterion would make the coordinate value at that rational point a unit.
Therefore checking rational points with unit coordinate values suffices
for containment of the entire principal open.

Apply this to the open image of a supplied multiplication morphism
`U x P -> G`. A rational factorization on the coordinate unit locus puts
every relevant rational point in that open image. The principal-open
containment follows. Consequently every unit-valued point over any
relative test scheme has its whole image in the same multiplication
cell. The definition `unitPointCellLift` uses the open immersion's lift
to construct an actual morphism from the entire test scheme to `U x P`.
Its `unitPointCellLift_comp` identity proves that multiplication returns
the original point, so the projections give global factors.

The hypotheses explicitly include the actual open immersion and the
rational factorization criterion. The module does not prove either
hypothesis for a highest-weight coefficient, nor construct Borel or Weyl
data or prove Bruhat covering or Steinberg irreducibility. Its provenance
is the implemented argument from Mathlib's principal-open pullback,
stalkwise detection of units, Jacobson spaces and rational realization of
closed points, together with published coordinate evaluation and actual
cell multiplication. No external structural theorem is assumed.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.
