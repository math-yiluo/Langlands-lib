# The character pairing on algebra points

For a finite projective commutative bialgebra `A` over `R` and a
commutative `R`-algebra `C`, `coefficients` identifies `A ⊗[R] C` with
the `R`-linear maps from the convolution dual to `C`. It sends
`a ⊗ c` to the map `f ↦ f(a) • c`.

The group-like coefficient equations say that the tensor evaluates
to `1` at the convolution identity and that its pullback along
comultiplication is the product of its two coordinate pullbacks.
`isGroupLikeCoeff_iff` contracts these equations against functionals
in the dual. Against two such functionals, the two sides of the
comultiplication equation give the value at their convolution
product and the product of their individual values. The perfect
tensor pairing and extensionality on pure tensors give the converse.
This makes the associated linear map into an algebra map.

When `A` is Hopf, a point `y` of its dual gives `pointCharacter y`.
Evaluation of the coefficient tensor for `y` respects multiplication
and the identity in the original point group by the two equations.
The group law therefore makes every value a unit. The pairing is
natural under maps of coefficient rings.

For cocommutative `A`, the tensor corresponding to the identity
linear map of the dual represents the pairing. Flipping this tensor
and applying the evaluation equivalence on the double-dual factor
gives the analogous tensor for the dual algebra. Contracting one
factor and evaluating the other proves this equality of tensors.
It gives `pointCharacter_bidual` and implies multiplicativity in
the dual point.

This coefficient calculation implements the group-like element and
evaluation arguments in Demazure and Gabriel, *Groupes algébriques*,
Tome I (1970), Chapter II, §1, no. 2, 2.10(a) and 2.10(d), printed
pp. 156–158. It supplies the algebraic pairing for the relative
scheme character comparison.
