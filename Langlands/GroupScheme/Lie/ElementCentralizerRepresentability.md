# Closed representability of actual Lie-element centralizers

For an affine group scheme over `Spec R`, supplied natural finite coordinates
on its actual Lie kernel define an actual algebraic adjoint representation.
Its action in every test algebra is the published adjoint action in those
coordinates.

The all-test `Lie.elementCentralizer G X` equals the stabilizer of the constant
coefficient vector of `X` in this representation. On an affine test, the
coordinate equivalence and coefficient naturality identify the stabilizer
equation with the actual adjoint equation. On an arbitrary test scheme,
equality of the action and constant points is checked on all affine
refinements. The reverse implication restricts membership in the stabilizer
and uses its affine comparison. Thus this is equality of subgroup functors
on all scheme tests, including nonreduced and nonaffine tests.

The affine coefficient space is separated, so the published closed-stabilizer
theorem supplies closed representability. For any affine locally finite type
group scheme over a field, the published scalar-extension and finite-coordinate
construction supplies the required coordinates. This corollary needs no
smoothness or connectedness of the group, and no semisimplicity of `X`.

This is a derived representability prerequisite for the adjoint stabilizer
used before Milne, *Algebraic Groups* (2017), Proposition 17.76, printed p.377 /
PDF p.393. The proof uses the Library's algebraic finite-coordinate action and
closed section-stabilizer constructions. Its private affine-refinement
extensionality argument is the general commutative-ring version of the
affine-open-cover argument in `OrbitLimit.hom_ext_of_algebraSpec`.
It does not establish semisimple smoothness or identify the tangent module
with a Lie-bracket centralizer.
