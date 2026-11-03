# Central-spectrum inversion for the actual smooth contragredient

Author: Worker 480.

This is an internal derived prerequisite for the general rank-one
self-association argument. It proves inversion of central spectra for the
actual smooth contragredient. It uses the published uniform-power
generalized-character definitions, compact averaging, dual-eigenfunctional
existence and admissible smooth bidual reflexivity.

The topological group `G` and complex representation carrier `V` have
independent universes. Compact open subgroups must be cofinal among open
subgroups of `G`. A group `A`, in another independent universe and without a
topology, maps to `G` by a homomorphism `z` with central image.

`exists_smoothEigenfunctional_of_centralEigenfunctional` starts with a
nonzero full algebraic dual functional satisfying
`φ(ρ(z(a))v) = χ(a) φ(v)`. Choose a vector on which it is nonzero and a
compact open subgroup `K` fixing that vector. Compose the functional with
the actual normalized compact averaging map. The composite stays nonzero
because averaging fixes the chosen vector. Right translation by `K`
preserves the finite orbit used to define the average, so the composite is
a smooth functional fixed by `K`. Central action commutes with averaging
by the published naturality theorem. Evaluating at `a⁻¹` proves that this
smooth functional is an ordinary eigenvector for the actual inverse
transpose action with character `χ⁻¹`.

`smoothCentralEigenfunctional` selects a smooth functional from this proved
existence result by classical choice. It takes the same smoothness,
cofinality, central-image and nonzero eigenfunctional data, with no
admissibility assumption. `smoothCentralEigenfunctional_ne_zero` and
`smoothCentralEigenfunctional_action` record its nonvanishing and its
inverse-character eigenvector equation. The selection is not asserted to
be canonical or functorial.

`exists_smoothEigenfunctional_of_isGeneralizedEigencharacter` combines this
construction with the published
`DualEigenfunctional.exists_dualEigenfunctional_of_isGeneralizedEigencharacter`.
Admissibility and compact-open cofinality supply that theorem's
finite-dimensional fixed-vector argument. The conclusion is a nonzero
ordinary eigenvector of the smooth contragredient, not just a functional
on a finite subspace.

`isGeneralizedEigencharacter_smoothContragredient_inv_iff` proves both
directions. The forward construction gives one direction with uniform
power one on the dual side. For the other, apply it to the admissible
smooth contragredient, then use surjectivity of the canonical smooth
bidual map to pull its eigenvector back to `V`. Injectivity and
equivariance of evaluation preserve nonvanishing and the ordinary
eigenvector equations. The inverse character is inverted twice.

`generalizedCentralCharacterSpace_ne_bot_iff_isGeneralizedEigencharacter`
identifies the two existing full-center spectrum conventions by unpacking
their nonzero-vector conditions. Both use one finite power for all
central elements at each vector.

`isCentralExponent_smoothContragredient_inv_iff` specializes the preceding
equivalence to the full center of `G`. The inverse character has the same
kernel, so the open-kernel condition in `IsCentralExponent` is preserved.
No finite-length hypothesis or central-spectrum decomposition is needed.

This module supplies no opposite-Jacquet duality, general-group Jacquet
admissibility, square-integrability criterion or proof of
`RationalRankOneSelfAssociationStatement`. In particular, character
inversion here is an algebraic contragredient operation and does not
identify it with complex conjugation.

Translation invariance of averaging uses the published `Compact.orbitMean_apply`.
