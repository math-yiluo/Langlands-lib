# Rational formal homomorphisms on p-divisible towers

On level \(n\), multiplication by \(p^n\) vanishes, so any ring map
from \(\mathbb Z_p\) to the endomorphisms agrees with the canonical
residue action. To establish this in `padicAction_unique`, compare a
scalar with the integer representative of its residue modulo \(p^n\).
Their difference is a multiple of \(p^n\) and therefore maps to zero.
The level identities imply the identity of tower actions.

The formal scalar action restricts to a ring action on the actual
finite kernel schemes. The uniqueness result identifies it with the
canonical p-adic action. Thus `Hom.pDivisibleMapLinear` is linear over
\(\mathbb Z_p\), and `RationalHom.pDivisibleMap` extends the restriction
to rational tensors. Restriction commutes with identity and
composition. `QuasiIsogeny.pDivisibleMap` sends the two maps of a
formal quasi-isogeny to inverse rational maps of the actual towers.

Tate (1967), §2.2, printed pp. 162–163 (PDF p. 3), constructs the
p-divisible group of a divisible commutative formal group from its
finite scalar kernels. The construction here uses that direction on
the represented kernels, with the formal scalar action and rational
Hom convention used for the rigidifier. See Drinfeld (1976), §1 and
§2 A, printed pp. 108–109 (PDF pp. 2–3).
