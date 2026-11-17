# Smoothness of the actual conjugation pairing

This internal construction supplies the compact conjugation-orbit finiteness
and quotient measurability used in the proof of Waldspurger's Corollary VIII.3.2,
printed pp.326–327 (PDF pp.92–93) of *La formule de Plancherel pour les groupes
p-adiques* (2003), registered as `waldspurger-2003-plancherel`. The source invokes
smoothness on p.327 to make its conjugation bounds uniform on compact sets.
The local constancy and Bochner measurability conclusions here make that
elementary step explicit for the Library's totalized pairing.

If a complex function `f` is bi-invariant under an open subgroup `H`, then
`h ↦ conjFun h f`, valued in the set of entire functions on the group, is
locally constant: on the open neighborhood `H x` of `x`, the conjugation by
`y` differs from conjugation by `x` by multiplication on the left and right
by inverse elements of `H`. Restricting this locally constant map to a
compact subset gives a finite image. Composing with inversion gives the
second, inverse-conjugator finiteness assertion. Compactness of `H` is not
needed for these generic assertions.

Postcomposing the same locally constant map with the total integral
`φ ↦ ∫ g, φ(g) f₂(g) dμ` proves that the conjugation pairing is locally
constant. The canonical projection onto left cosets is an open quotient
map. Its quotient topology detects local constancy, so the already
published central descent is locally constant as well. This proof uses
neither convergence of the integral nor invariance of the measure.

Every element of the generic Schwartz space belongs to a compact open
level, by `mem_schwartzSubmodule_iff`. The constructions
`Space.locallyConstantConjugates` and
`Space.leftConjugationPairingLocallyConstant` apply the preceding argument
at such a level. The finite-image theorems hold on every compact subset.

The entry construction
`rationalLeftConjugationPairingLocallyConstant` has exactly the underlying
function `rationalLeftConjugationPairing` on the actual quotient by
`(rationalPoints.map s).range`, where `hs : IsSplitComponent s`.
The supplied compact open Iwasawa subgroup witnesses existence of a
compact open level; it need not be the level of either function. The field,
affine locally finite type group scheme, torus, cocharacter, matrix
representation and Schwartz weights retain their existing types and
arbitrary universe. There are no reductivity, maximality, genericity,
closed matrix realization or cuspidality assumptions in this unit.

For the displayed Borel measurable structure of that exact left quotient,
continuity gives `StronglyMeasurable` with complex values, hence
`AEStronglyMeasurable` for every measure on it. In particular the latter
theorem supplies the measurability input of the published integrability
adapter for any compatible quotient measure. It supplies no estimate of
the integral of the norm and no convergence of the inner integral.
The closed VIII.3.2 theorem still requires those analytic and geometric
inputs. The right-quotient convention is untouched.
