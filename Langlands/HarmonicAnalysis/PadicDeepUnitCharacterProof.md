# Proof of the first-order principal-unit character

Worker 84 develops `Langlands.HarmonicAnalysis.padicDeepUnitCharacter.{u}`
with target `PadicDeepUnitCharacterStatement.{u}`. This paired text describes the implemented proof; compilation alone is not
independent acceptance.

For principal units z and w of level n, multiplicativity of the actual
discrete valuation bounds c*(z-1)*(w-1) by v(c)*exp(-2*n). The stated
bound therefore puts this error in the published additive conductor
lattice. The existing conductor specification kills it. Expanding
c*(z*w-1) as the two linear terms plus that error proves the displayed
formula multiplicative. The continuous monoid homomorphism uses the
supplied field topology and the actual subgroup and unit inclusions.

For finite order choose k=max(0,-ord(c)-n(psi)). The universal bound
v(x)<=exp(-ord(x)) also holds for x=0, so no unmentioned nonzero
condition is used. The positive integer ord(p) is at least one.
The published integer-power order law bounds v(p^k) by exp(-k).
Consequently p^k*c*(z-1) lies in the conductor lattice uniformly for
all units of level n, including n=0. Additivity turns its value one
into eta(z)^(p^k)=1, proving the equality of continuous characters.
The proof constructs no extension, depth witness or stabilizer.
