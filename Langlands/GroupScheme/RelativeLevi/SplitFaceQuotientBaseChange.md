# Actual vector quotient comparison after coefficient change

This internal adapter for the finite vector-bundle filtrations of supplied
relative radicals constructs the actual full quotient
isomorphism between the original coefficient-changed vector quotient and
the vector quotient of an independently chosen fresh face chart on the
pulled-back roots. It proves this actual comparison linear, rather than
assuming any transition linearity.

The main setting is an arbitrary nontrivial commutative ring `R` at
universe `u`, an affine reductive actual group `G`, a fibrewise maximal
split torus, its actual fibrewise root datum, actual root
parametrizations and a supplied split parabolic face chart `C`. The
coefficient ring `A` is any commutative `R`-algebra; it need not be
nontrivial. A supplied fresh chart `D` is a face chart on the actual
base-changed torus, unchanged root datum, base-changed root
parametrizations and unchanged original cocharacter coordinates.
No restriction is made on its choices of positive base or auxiliary
chart. Their corresponding exact-support index types may differ, but
their cardinalities agree: both are the roots at the same unchanged
unscaled face height. These cardinalities may be zero.

`step_comp_affineBaseChangeTermIso` proves that the actual
inclusion-compatible term isomorphisms supplied by `RootWeightBaseChange`
respect the actual consecutive steps. It cancels the target ambient
representing inclusion, applies the actual term inclusion equations and
uses `step_comp_inclusion` and functoriality of base change.

`affineBaseChangeQuotientMap` is the original actual quotient pulled back
to `A` and followed by the canonical standard vector-group base-change
isomorphism. `isFppfQuotient_affineBaseChangeQuotientMap` proves its full
fppf quotient predicate with the actual pulled-back next-term range as
kernel. `affineBaseChangeQuotientIso` descends the compatible actual term
isomorphisms by full fppf quotient uniqueness. Its `_fac` theorem retains
exactly the actual quotient-map factorization.

The target action `affineBaseChangeTargetAction` uses the ORIGINAL
`C.faceCocharacter`, now in the base-changed torus, acting on the fresh
term. It does not use a newly chosen multiplier for `D`.
`affineBaseChangeTargetAction_quotient` proves that the fresh actual
quotient carries the common scalar power `C.faceMultiplier * (d+1)`.
The existing equality of the two exact unscaled face-height functionals,
the original `C.facePairing` formula and `D.weight_eq` derive the required
root pairings on every fresh exact-weight coordinate.
`affineBaseChangeTargetAction_ambient` derives its actual ambient
conjugation equation for the actual base-changed original cocharacter
from the two torus-action inclusion equations and the actual
fixed-exponent cocharacter base-change theorem.

The generic
`AutomorphicAction.coefficientChange_isEquivariant_of_conjugation`
compares an original coefficient-changed action and a fresh action
whenever their actual monomorphic ambient inclusions agree and their
actual ambient conjugation equations correspond. It cancels the target
inclusion and uses the pullback point equivalence, including its
compatibility with multiplication, inverse and the actual cocharacter.
`affineBaseChangeTermIso_isEquivariant` applies it to the actual term
isomorphism and the proved action equations. No term-equivariance
premise remains.

`affineBaseChangeQuotientIso_isEquivariant` then transfers the actual
term and quotient equivariance through the full quotient. The
quasi-compactness needed for local quotient lifts follows from the
original affine coordinate quotient and its actual base change and
target isomorphism. The result is actual scalar-power equivariance on
every scheme test.

The common power is positive because the original face multiplier is
positive and `d+1>0`. Arbitrary-ring scalar-weight rigidity therefore
proves the comparison linear. `affineBaseChangeLayerLinearEquiv`
constructs its actual linear equivalence on each coefficient algebra over
`A`. `affineBaseChangeQuotientIso_isEquivariant_power` proves commutation
with EVERY common natural scalar power, using the base-ring matrix of
that same actual morphism. This allows subsequent compositions whose
chosen source realization has a different multiplier.

All comparisons are actual group-scheme morphisms and hold on arbitrary
scheme tests, including nonreduced tests and rank-zero layers. The
provenance is internal: actual coefficient-change quotient transport,
the original-to-fresh term comparison and exact face-height equality,
actual cocharacter and torus-action formulas, full fppf quotient
uniqueness and positive scalar rigidity. Étale-global reflection of
linearity and the final filtration descent remain consumer obligations.
