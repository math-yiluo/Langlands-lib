# Recovering an actual character from a normalized covariant coordinate

For affine group schemes `G,H` over a field `k : Type u`, an actual homomorphism
`i : H → G`, coordinates `χ,d`, left covariance of `d` with weight `χ`, and the
normalization `d(1)=1` at the rational identity suffice to recover an actual
rational character of `H` whose coordinate is exactly `χ`.

This is an internal derived construction from coordinate evaluation, covariance,
and the multiplicative group's functor of points. It uses no external theorem
about highest weights, Steinberg modules, or Borel subgroups.

The rational normalization pulls back to the identity of every relative test
scheme. Evaluating covariance at the identity then identifies `χ(h)` with
`d(i(h))`. Applying covariance once more shows multiplicativity of `χ`.
Its value at `h⁻¹` is an explicit inverse to its value at `h`, also for
nonreduced or nonaffine tests. These units form a natural family of group
homomorphisms. The published `homOfPoints` construction and `Gm.pointsEquiv`
recover the character `normalizedCovariantCharacter`.

The evaluation theorem holds for every test scheme. Evaluation at the universal
point and injectivity of `globalAlgHom` show that the recovered character's
coordinate equals the original `χ`. If `i` is a monomorphism and a supplied
homogeneous quotient is proper, the published finiteness theorem for actual
character coordinates therefore gives finite dimensionality of every entire
space `leftCovariantSubspace i (χ ^ e)`.

These results are support for the geometric and induced-module construction in
`SteinbergBigCellStatement`. They do not construct its geometric witnesses,
prove properness of a Borel quotient, or establish irreducibility.
