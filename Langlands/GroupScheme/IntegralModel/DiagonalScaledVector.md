# Integral vector models with independent coordinate scales

For a domain `R` with fraction field `K` and a finite family of nonzero
scales `t j` in `K`, `diagonalScaledVector` is the polynomial vector group
over `R` whose generic-fibre identification multiplies coordinate `j` by
`t j`. This identification is an actual group-scheme isomorphism.
The model is smooth and has geometrically connected fibres.

Its integral-section map has coordinate formula
`x j ↦ t j * algebraMap R K (x j)`. The image theorem proves both
inclusions: in the canonical section coordinates, its actual integral-point
image is the submodule `diagonalVectorLattice` with independently scaled
principal ideals in each coordinate. The latter submodule is defined even for
zero scales, while the model requires nonzero scales so that its generic
identification is invertible.

Given two scale families `s` and `t` and integral coefficients satisfying
`algebraMap R K (c j) * t j = s j` for every coordinate, the integral
diagonal map is an actual extension of the identity on the generic vector
group. The generic compatibility follows from the diagonal base-change
square and coordinatewise composition. This constructs the transition and
does not presume its existence.

If `R` is local, every integral-model homomorphism extending this same
generic identity equals the explicit transition by flat generic rigidity.
Its special-fibre map is therefore the actual residue-field base change of
the diagonal map. The diagonal kernel theorem proves smoothness, connectedness
of the underlying scheme and representation-theoretic unipotence of its
scheme-theoretic kernel. Different residue coefficients may vanish
independently. Equal scales and dimension zero are included.

This is derived infrastructure for Task 6392, extending the uniform scalar
model construction coordinate by coordinate. Its source motivation is the
additive models of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Section C.2 and Fact C.2.1, printed pp.697–698 / PDF pp.728–729, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. The independently scaled
vector construction is an internal consequence of those polynomial models
and the existing all-test vector coordinates. The result retains the
coefficient equations as explicit inputs; it does not prove that a ramified
root lattice has this form, or match it with a supplied apartment filtration.
