# Relative coroot commutators

Fix an arbitrary commutative ring `R` in universe `u`, a finite coordinate type `I`, a reductive group scheme `G` over `Spec R` with `IsAffineHom G.X.hom`, and a supplied coordinate-torus homomorphism `i` and fibrewise coordinate root datum `P`. Under these hypotheses, the coroot theorem applies to each root index and every test scheme over `Spec R`. The earlier transporter lemmas in this module instead work over any base scheme with a supplied actual transporter and inversion equality.

The all-test transporter version of the inversion calculation allows the normalizing point to live on the current test scheme. The proof restricts that transporter along the fppf square-root refinement and applies the same elementary commutator identity. Affine-cover descent removes affineness of the test scheme.

These are internal group and cover calculations, with no new structural input. Their purpose is to apply the etale-local reflection normalizers directly to the original ambient group's points.

`locallyCommutator_coroot` combines this calculation with the etale-local normalizers of a fibrewise coordinate root datum. It pulls their cover back to the given test scheme, transports each normalizing section to a transporter for the original ambient group, and applies the inversion calculation. The coordinate pairing is the standard dot product because the prescribed base point supplies an actual residue-field realization. This argument remains valid for arbitrary affine base rings, including nilpotents, and arbitrary test schemes; it assumes neither semisimplicity nor root-group parametrizations.

`corootCommutatorCover` chooses the resulting jointly surjective flat locally finitely presented cover. Its membership theorem states explicitly that the restricted point belongs to the ordinary abstract commutator subgroup on every member. It is a choice of an actual cover, with no quasi-compactness hypothesis.
