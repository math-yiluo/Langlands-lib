# Ambient Xi controls the normalized Levi Xi on the full minimal chamber

`HasRationalLeviXiHalfModulusComparison` bounds the literal standard-Levi
Xi times the norm of the standard half modulus by ambient Xi on the full
closed chamber of `M₀(F)`. All spherical functions use the given compact
subgroup and its literal Levi intersection. The bound is uniform in the
chamber point.

`hasRationalLeviXiHalfModulusComparison_of_basis` starts from the
simultaneous standard basis at a structural compact and the minimal-Levi
Cartan covering there. The compact dominant reduction writes every
chamber point as a dominant uniformizer point with two multipliers from a
fixed compact subset of `M₀(F)`. The tube lemma chooses two nested basis
levels whose conjugates by those compact factors fit inside the next
level and the evaluation compact. The minimal Levi normalizes the
opposite radical, and the minimal standard basis contracts that radical
at every dominant uniformizer point. Shrinking the first basis level
also ensures that its parabolic factors project inside the evaluation
compact. The generic lower spherical estimate then applies directly at
all chamber points.

This is a derived comparison for the weak and positive terms of the
Waldspurger VI.3.1 packet argument, using the pointwise form of II.1.6.
The estimate has a constant factor and uses the original half modulus.
