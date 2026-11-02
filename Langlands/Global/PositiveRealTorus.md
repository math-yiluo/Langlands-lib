# Positive real points of actual split tori

Worker 112.

This construction is over an arbitrary number field `F`. Its inputs are an
actual commutative group scheme `T` over `Spec F`, a finite index type `I`,
and a group-scheme isomorphism `e : T.toGrp ≅ splitTorus (Spec F) I`.
The map `full` sends a family of positive real units to actual
`Lie.AffinePoints T.toGrp (Adeles F)`. These are morphisms of schemes over
`Spec F`, with the published point-group law. Its image `subgroup` is thus a
subgroup of actual adelic torus points. The map is injective. Empty `I` is
allowed throughout.

The source is Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*
(1995), Chapter I, §2.1, printed pages 18–19, registered as
`moeglin-waldspurger-1995-spectral-decomposition`. For a number field the passage
fixes a splitting of the split torus and inserts the same positive real at
each infinite place, with identity at each finite place. This module realizes
the resulting subgroup before any central-extension lifting. It generalizes
that coordinate construction to any actual supplied split-torus isomorphism.
No central extension or lifting is constructed here.

`coordinates` first applies the published `isoPointsEquiv` to `e`, then
`splitTorus.affinePointsEquiv`. It identifies the actual `A`-points with
families of units of `A`, for any commutative `F`-algebra `A`.
`full` takes the product of the scalar maps `PositiveRealIdeles.full F` and
applies the inverse point equivalence. `coordinates_full` proves its precise
coordinates. The scalar injectivity in every coordinate proves injectivity
of `full`.

For an actual algebraic character `χ : characterLattice T`,
`characterExponents` pulls `χ` back along `e.inv` and applies the published
split-torus character-lattice equivalence. `positiveCharacter` is the
multiplicative map given by the corresponding integer monomial on positive
real units. The monomial formula is a derived consequence of the existing
lattice API: express a character as the finite sum of its coordinate
characters, evaluate a sum as a product and an integer multiple as an integer
power, and apply the actual affine-point equivalence for the multiplicative
group. `split_characterValue_eq_prod` proves this affine version;
`characterValue_eq_prod` transports it through `e`, using its inverse law.

`characterValue_full` proves that evaluating `χ` on the constructed adelic
point gives exactly the scalar idele of `positiveCharacter χ x`.
`absoluteValue_characterValue_full` consequently gives its normalized idelic
norm as the positive monomial raised to `Module.finrank ℚ F`. The scalar
embedding is unrescaled, so the degree is retained.

This module does not install a topology on general affine points or assert
continuity of the transported map. Its splitting is supplied; no maximal
split torus, central split torus, minimal parabolic, positive or simple root
system is chosen. It proves no independence of the splitting, split-centre
decomposition, reduction theorem, Siegel covering or finite-volume theorem.
These remain separate structural and analytic obligations.
