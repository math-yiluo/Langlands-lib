# Integral duality and normalized induced coefficient tensors

This module constructs the comparison between the tensor of normalized induction
of a representation and its smooth contragredient, and the tensor of normalized
induction with its own smooth contragredient. It retains the integral defining
that comparison and proves an actual integrability assertion for its coefficient
formula. All objects use the existing canonical `SmoothRep`, smooth algebraic
dual and Haar-normalized induction.

## Source and scope

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082:

- I.3, printed p.243, PDF p.9: positive half-modulus covariance, right-translation
  induction, admissibility of induction and the same-parabolic bilinear
  quotient-integral identification with the smooth contragredient.
- V.1, printed p.288, PDF p.54: the two successive identifications of
  `L(ω,P)` with the tensor of the two normalized inductions, and then with
  induction tensored with its smooth dual; evaluation of a pure tensor by its
  matrix coefficient.

The original I.3 and V.1 passages were read directly. The present construction is
a derived prerequisite for those identifications. It uses the Library's proved
compact-quotient integral duality rather than postulating a duality equivalence.
It is stated for actual topological subgroup data. It does not claim a verified
realization of these data for every reductive rational-point group.

The comparison from induction on the product group to the tensor of the two
inductions remains a separate obligation. So do compact pictures, smooth twist
families, stabilizer descent, comparison with all of the manuscript's compatible
Haar normalizations, and the analytic wave-packet and Plancherel assertions.
No irreducibility, including irreducibility of parabolic induction, is assumed.

## Actual data and hypotheses

Let `G` be a locally compact nonarchimedean topological group, and let `P`, `M`
and `U` be actual subgroups. The decomposition
`h : IsSemidirectDecomposition P M U` supplies the actual Levi projection
`h.projection : P →* M`. Assume `U` is closed. Write

`I(A) = (normalizedInductionFunctor h hU).obj A`.

This is the existing induction of
`inducingRepresentation h hU A`, namely inflation of `A` along the projection,
twisted by `HaarModulus.closedHalfCharacter`. Its functions satisfy positive
half-modulus left covariance, and `I(A)(g)f` evaluates at `x` as `f(x*g)`.

For the measure and integral comparison, `G` is additionally Hausdorff with a
Borel measurable structure, `P` is closed and locally compact, and the actual
left quotient `Induction.LeftQuotient P` is compact. Ambient unimodularity is
visible as

`hG : ∀ g : G, Measure.modularCharacter g = 1`.

For integrability of the paired induced functions, assume the displayed modulus
comparison on every `q : P`:

`Measure.modularCharacter q =
  (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0)`.

The duality equivalence additionally requires continuity of the Levi projection
and admissibility of `A`. Admissibility of the induced representation is proved
by the existing compact-quotient induction theorem and is not an extra premise.
The field is `ℂ`; the inducing carrier universe `uV` is independent of the group
universe `uG`. Induction raises the carrier to `max uG uV`.

## One fixed quotient-integration measure

`normalizedInductionBruhatMeasure hP hG` chooses one measure on the top subgroup
of `G` from `Induction.exists_compactQuotient_measure`. The existence proof in
`Induction.CompactQuotientDuality` constructs a compactly supported Bruhat density
and its weighted ambient Haar measure. The exposed specification of the chosen
measure is exactly `normalizedInductionBruhatMeasure_spec`:

- every open neighbourhood of the identity has positive measure;
- if a locally constant scalar function `φ` has left covariance by the modular
  character of `P`, each function `k ↦ φ(k*g)` is integrable and its integral
  equals the integral of `k ↦ φ(k)`.

The measure is fixed before selecting `A`, its vectors or its functionals. It is
not asserted to be ambient Haar or invariant on all functions. The specification
does not determine its absolute scale, identify it with a previously chosen
compact-picture integral, or prove independence of the measure choice. Those
normalization comparisons must be supplied by downstream consumers when needed.

## Integral-characterized same-parabolic duality

`exists_normalizedInductionIntegralDualEquiv` proves existence of an equivariant
complex linear equivalence

`E : I(A)∨ ≃ I(A∨)`

whose defining pairing is

`ℓ(f) = ∫ k, (E ℓ)(k)(f(k)) dμ(k)`.

Here and below the integral variable is in `⊤ : Subgroup G`, `μ` is the measure
just fixed, evaluation means `Induction.eval`, and application of the functional
means `smoothDualPairing A.representation`. This is a complex bilinear pairing,
with no complex conjugation.

The proof first squares the existing closed half-character using
`closedHalfCharacter_mul_self`, then applies the assumed modulus comparison.
Closedness of the Levi follows from `hP` and continuity of the projection;
`compactOpenCofinal_of_isClosed` gives its compact open subgroups.
`smoothInduced_inducingRepresentation_isAdmissible` proves the required induced
admissibility. The positivity and translation law of the fixed measure then
supply all hypotheses of `Induction.exists_integralDualEquiv_of_pos`.
`exists_functorEquiv_of_twistEquiv` transports that proved equivalence to the
bundled functor carriers by identity equivalences, preserving its integral.

`normalizedInductionIntegralDualEquiv` chooses this proved equivalence, and
`normalizedInductionIntegralDualEquiv_pairing` records its integral law.
It is not an assumed representation-theoretic input.

## Tensor comparison and coefficient formula

`NormalizedInductionDualTensor h hU A` is the actual algebraic tensor
`I(A) ⊗[ℂ] I(A∨)`. `normalizedInductionDualTensorAction` gives it the external
`G × G` action, with the first coordinate acting on the first induced factor and
the second on the second factor. `isSmooth_normalizedInductionDualTensorAction`
proves smoothness using product open stabilizers on pure tensors and tensor
induction. These constructions do not require admissibility or the measure.

For admissible `A`, `normalizedInductionDualTensorEquiv` is an equivalence of
these actual product representations with the canonical coefficient-tensor
representation on `NormalizedCoefficientTensor h hU A`. Its pure-tensor law is

`f ⊗ fdual ↦ f ⊗ E⁻¹(fdual)`.

The linear equivalence is `TensorProduct.congr` of the identity and `E.symm`.
Its equivariance follows on pure tensors from the intertwining law of `E.symm`,
then on all tensors by additivity. This uses the actual right-translation
induced representations, not an abstract replacement action.

`normalizedInductionDualCoefficientMap` composes this equivalence with
`normalizedCoefficientMap`. Its values are locally constant functions on `G`.
`normalizedInductionDualCoefficientMap_tmul` proves

`E_P(f ⊗ fdual)(g) = ∫ k, fdual(k)(f(k*g)) dμ(k)`.

The proof applies the defining integral law of `E` to `E.symm fdual` and
`I(A)(g)f`, cancels `E(E.symm fdual)`, and unfolds right translation.
`normalizedInductionCoefficient_integrable` separately proves the displayed
integrand is integrable. It follows from
`normalizedInductionPairing_integrable` applied to the right translate of `f`.
The latter proof uses local constancy of the bilinear pairing,
`Induction.dualPairing_covariant`, the half-character square and the modulus
identity to apply the fixed measure's scalar integration law at the identity.
Neither integrability theorem requires admissibility or continuity of the
Levi projection.

Finally, `normalizedInductionDualCoefficientMap_action` proves, for every tensor
`t` and every `(a,b) : G × G`, the convention

`E_P((a,b)·t)(g) = E_P(t)(b⁻¹*g*a)`.

It transports the product action through the constructed equivalence and applies
the proved canonical coefficient-tensor translation law. This completes the
same-parabolic dual comparison and its tensor coefficient consequence, under
the visible hypotheses and fixed measure choice described above.
