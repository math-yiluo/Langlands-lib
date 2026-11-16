# The open cell of actual relative dynamic root groups

Fix an arbitrary commutative ring `R` in universe `u`, a finite coordinate type `I`, a reductive group scheme `G` over `Spec R` with `IsAffineHom G.X.hom`, a coordinate torus maximal on every residue fibre, and a supplied fibrewise coordinate root datum `P`. A base of `P` and finite enumerations of its negative and positive roots specify the order of the factors.

For each root, choose an integral cocharacter which annihilates exactly that pair of opposite roots, using the reduced root datum and the published generic-kernel construction over the fixed auxiliary field `ULift ℚ`. The actual root factor is the dynamic unipotent group of its coroot inside the centralizer of this isolating cocharacter, with the published actual inclusion in `G`. These factors are smooth over `R`.

Worker 243's exact field-fibre comparison supplies additive coordinates on every field fibre of each chosen factor, whose composite with its actual inclusion is the prescribed root parametrization. The generic actual-factor cell theorem then proves that their ordered multiplication, with the coordinate torus in the middle, is an open immersion. This construction uses no global additive coordinates, locality or reducedness of `R`.

The content is an internal composition of the published isolating-cocharacter and dynamic-group constructions and the companion actual-factor coordinate/openness helpers, together with the exact field-fibre comparison developed in this task.

The final reduction additionally assumes semisimple geometric fibres and closedness of the coordinate-torus inclusion. If every value of each chosen actual root factor is fppf-locally a commutator, then every point of `G` has that property. It chooses a base and finite positive/negative enumerations, uses the completed torus commutator theorem for the middle factor, and applies the open-unit-cell fppf generation theorem. The local commutator premise on root values remains explicit here.
