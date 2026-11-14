# Etale conjugacy of relative parabolics with equal residue fibres

`relativeParabolicConjugacyOfEqualResidue` constructs actual etale
subgroup-conjugacy data for two relative parabolic inclusions in a reductive
group over any scheme, provided their subgroup ranges agree over the canonical
residue field of the specified base point.

The construction first obtains compatible dynamic presentations over a common
pointed etale neighbourhood. Reductivity survives base change, so the ambient
group there is smooth and affine over that neighbourhood. The presenting
cocharacters agree at the specified residue-valued point. The arbitrary-base
field-point conjugacy constructor therefore gives conjugacy on a further etale
neighbourhood. Composing projections and transporting the conjugator through
the canonical pullback comparison returns conjugacy data over the original
base. The original point-projection identity ensures that the composite
neighbourhood contains the specified base point.

This is an internal composition of the imported compatible-presentation and
field-point-conjugacy constructions. It does not assert the case of a nonidentity
initial residue conjugator; that case requires the separate pointed conjugator
reduction.
