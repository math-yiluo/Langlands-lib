# Forward and dual factors after a common auxiliary twist

`CommonTwistPairComparisonStatement` concerns a finite place of a cyclic
Galois extension of number fields with compact adelic quotients. The
cuspidal presentations have irreducible admissible finite components,
and the supplied original duals and duals of the common twists are
actual global contragredients. The lower common twist is a Hecke
character, and the upper common twist is its idelic norm pullback. The
second member of each pair, including each dual pair, is the same
rank-one presentation and has trivial local action at the places in
question. The lower character family exhausts the local norm characters,
with multiplicity given by the number of upper places.

`HasCommonTwistAuxiliaryData` supplies either the original spherical power
relation or the highly ramified standard factor formulas for the relevant
local twists. The conclusion identifies the product of the forward Euler
values, the product of the dual Euler values, and the positive forward
epsilon base. It holds for the supplied certified finite factor choices.

Compose local determinant twists to express the two successive lower
twists using the product character. Local compatibility with the smooth
contragredient identifies the actual dual of a twist with the inverse
twist of the original dual. These equivalences turn the given forward and
dual factor choices into the inputs of `commonNormTwistAuxiliaryFactors`.
Inversion preserves the norm-character exhaustion and fiber counts.
It also commutes with the residue-degree power on spherical spectra, so the
spherical comparison applies to the dual choices. In the highly ramified
case, the formulas already cover the inverse twists.
