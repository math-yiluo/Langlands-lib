# Finite values at actual inducing representatives

This derived module gives the smooth-section choice used in the lower inclusion
of Waldspurger VIII.4.2, printed p.330 (PDF p.96), on the existing product-induced
section space. It turns finite parameter isolation into isolation at actual
inducing representatives, with no choice of torus parameters supplied by the
caller.

`productInducedSmoothOrbitEvaluation` evaluates an existing coherent smooth
orbit section at an actual irreducible admissible representative in the orbit,
with values in that representative's actual normalized product-induced space.

`exists_productInducedSmoothOrbitSection_finiteClasses` takes a target
representative, a finite set of representatives in different smooth
isomorphism classes from the target, and a desired product-induced value at
the target. It produces a section with that value and zero values at all the
selected representatives.

The proof selects the existing auxiliary parameter for each representative.
The supplied class inequalities imply that the finitely many selected
parameters are separated from the target by all stabilizer translations:
the published fiber equivalences show that these translations preserve
the smooth class. The parameter theorem of `SmoothFamilyFiniteValues` then
gives a smooth section. Coherence transports its prescribed value and zeros
back to the actual representatives. The inverse target transport supplies
the initial parameter-fiber value.

The theorem retains the existing locally compact nonarchimedean group,
semidirect decomposition, closed radical and parabolic, compact open subgroup,
continuous norm family and Levi projection, factorization, torus coordinates
and finite actual class-stabilizer hypotheses. The carrier universe is
independent of the group and torus universes.

This module does not prove packet membership, cuspidality, the Waldspurger
VIII.4.2 cuspidal coefficient equality or the same-level coefficient lifting.
