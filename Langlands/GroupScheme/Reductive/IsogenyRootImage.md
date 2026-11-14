# Root characters from finite equivariant additive-line images

This internal derived lemma starts with a finite actual homomorphism from a
naturally coordinated additive line into an affine group of finite type over
an arbitrary field. Its nonzero source character belongs to a specified split
torus T. Equivariance is for conjugation through an actual morphism T → T'
and a specified morphism from another split torus T' into the target group.
The entry definition `HomImage.rootExpCharFactor` chooses an actual root β of the latter action and a natural
number r, together with a proof that the pullback of β is (ringExpChar k)^r times the source
character in the integral character lattice.

The finite image is an actual additive line. The source torus acts on this
image by the restricted target action, and the image has natural coordinates
of a single character γ. The actual image projection is epimorphic and
equivariant, so the vector-line polynomial theorem gives γ equal to a
characteristic-power multiple of the nonzero source weight. Thus γ is
nonzero. The image's Lie module is one dimensional and entirely of weight γ.
The closed inclusion has injective differential, yielding a nonzero vector
of weight γ in the target Lie module. The split-torus weight-restriction
theorem supplies β and the asserted exact pullback equation.

Provenance: derived from actual finite additive images, actions on schematic
images, vector-line coordinates and their polynomial characteristic-power
classification, equivariant tangent maps, and split-torus weight restriction.
The differential used for nonvanishing is that of the closed image inclusion;
no separability of the original finite map is assumed. This module does not
yet prove a root-index bijection, identify whole root subgroups, or prove the
full root-datum comparison.
