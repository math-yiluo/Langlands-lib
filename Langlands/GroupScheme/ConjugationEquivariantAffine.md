# Conjugation equivariance detected on affine tests

`IsConjugationEquivariant` asserts that an actual group-scheme
endomorphism commutes with conjugation on every relative scheme test. Its
full pointwise image is consequently normal.

For an affine group over an affine base, it suffices to check this equation
on affine algebra tests. The product of the group with itself is affine.
Apply the affine hypothesis to its canonical affine presentation and the
two universal projection points. Cancel the presentation isomorphism to
obtain equality of the two actual maps from that product. Composing with
any pair of points gives the equation on every scheme test, including
nonreduced and nonaffine tests.

For the reconstruction in `RestrictedAffinePointEndomorphism`, the exact
point formula and the multiplicative base-change point equivalence transfer
conjugation equivariance from the original restricted transformation to all
affine tests. The preceding criterion gives full scheme-test equivariance.

This is an internal affine representability argument. No equality over a
general base is inferred from geometric fibres.
