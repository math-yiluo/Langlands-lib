# Geometric finite-order reduction for the original CM rigidity target

This internal reduction uses exactly the datum, signature charts, universes,
and named prerequisite statements of `CMSmallLevelRigidityStatement`.
`CMRigidityFromIntegralPolarizedAutomorphismsStatement` states an implication:
finite order of actual integral polarization-preserving automorphisms over
algebraically closed characteristic-zero fields, together with injectivity of
the actual one-prime rational Tate endomorphism map, implies that unchanged
rigidity target. Both geometric inputs remain premises.

The integral finite-order premise concerns each actual abelian scheme B,
its supplied actual dual witness W, and an actual geometric polarization lam.
Its equation is equality of integral homomorphisms,
`g.hom ≫ lam ≫ W.map P W g.hom = lam`. The second premise concerns the
published `PrimeAdic.rationalHomMap` on the actual prime-adic rational Tate
module at the identity field point. Neither premise substitutes a supplied
abstract representation or automorphism group.

The prerequisite bundle P uses the target's nine tensor and Picard statements.
Its two additional base-change fields are supplied by the published theorems
`Langlands.AbelianScheme.dualAbelianBaseChange` and
`Langlands.AbelianScheme.polarizationBaseChange`. They are not additional
hypotheses.

`cmSmallLevelFiniteOrder_of_integralPolarizedAutomorphisms` proves the previously
published `CMSmallLevelFiniteOrderStatement` under the first premise. At each
admitted field point p, the map on global sections gives an injection F → Ω,
so characteristic zero of the number field gives characteristic zero of Ω.
The admission supplies the finite étale root-of-unity hypotheses, invertibility
of the torsion indices, pair additivity, and actual dual existence.
For each original fixed compact-level orbit, the polarized integral power-model
constructor therefore gives the same realizing B, exact rational comparison,
and positive even power, with an actual polarization preserved by the integral
automorphism. The assumed integral finite-order theorem applies to that
automorphism. Rationalization, exact conjugation, and the positive-power
finite-order lemma then give finite order of the original rational
endomorphism. The original positive and numerical object tests are retained.

`cmRigidityFromIntegralPolarizedAutomorphisms` composes this result with
`cmSmallLevelRigidity_of_finiteOrder_and_primeFaithfulness`. That published
reduction uses sufficiently small level at a finite prime to make the actual
prime Tate operator the identity, then the explicit one-prime injectivity
premise reflects this to the original self-isogeny.

The provenance is the internal composition of the exact integral power model,
its actual polarization transport, the admitted-base fields, the two proved
base-change theorems, and the published prime-operator rigidity reduction.
This module proves neither geometric premise and is not an unconditional proof
of small-level rigidity. The protected target and its imports are unchanged.
