# Comparison of cuspidal pair Euler products away from one place

`cuspidalPairAwayEulerComparison` uses actual cuspidal pairs and their
smooth-dual presentations in a cyclic extension of number fields with
compact adelic quotients. It assumes arithmetic weak base change for both
members. At each finite place the restrictions of the supplied global
character family exhaust the local norm-trivial characters, each with
multiplicity equal to the number of places above it. The theorem produces
a finite-order Hecke character trivial at the distinguished lower place,
with norm pullback trivial at all places above it.

At every other finite place the theorem gives two equalities, one for the
forward Euler values and one for the dual values. Below, the first member
is twisted by each norm character times the auxiliary character. Above,
the first member is twisted by the norm pullback of the auxiliary character.
The duals use the inverse characters.

Weak base change gives matching residue powers for both spectra outside a
finite set. At such places inversion commutes with residue powers and gives
the spectral match for the duals. The spherical completion comparison
matches both products, since inverting the global character list preserves
the local restriction multiplicities. At the other finite places, except
for the distinguished place, the auxiliary Hecke character is chosen to
meet the conductor bounds for both pairs in both fields. Highly ramified
vanishing then makes all the indicated Euler factors one there.

The result implements the finite-place comparison used in Henniart and
Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle* (2011), II.6.19, equations (3)–(5), printed
pp. 133–134 (PDF pp. 141–142), in the number-field setting. The retained copy
is registered as `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
