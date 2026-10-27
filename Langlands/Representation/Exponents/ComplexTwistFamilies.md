# Actual complex-twist induced families and opposite Jacquet occurrence loci

Author: Worker 264.

This internal definition unit extends the published real-family packaging
[`RealTwistFamilies`](RealTwistFamilies.md) to complex determinant exponents.
It reuses the published actual induction, the complex product-Levi twist of
[`LeviComplexPower`](../Twist/LeviComplexPower.md), the inverse-conjugation
transport of `CuspidalSupport`, and the opposite Jacquet class-exponent
predicate. It introduces no continuation hypothesis, selected irreducible
quotient, or new induction, conjugation, twist or Jacquet carrier.

All names below are in `Langlands.ComplexTwistFamilies`. The field is the
actual `PadicField p`, in universe `uF`, with compatible `TopologicalData T`.
`B`, `D` and `C` are ordered block shapes of the same ambient rank `n`.
Neither `D` nor `C` is required to refine `B` in the general construction;
the refined specialization adds an actual `BlockRefinement B`.
The inducing carrier has universe `uV`, the candidate carrier has
independent universe `uW`, and the induced family has carrier universe
`max uF uV`. All complex determinant exponents are retained, including
central directions, the one-block case and rank zero. No irreducibility,
admissibility, temperedness, support, chamber, positivity, zero-sum or
tensor-factorization hypothesis is needed to define the families.

## Induced families

For `σ : Rep.{uV} ℂ (B.Levi F.Carrier)` and every `z : Fin B.length → ℂ`,
`induced T B σ z` is the existing upper normalized induction
`CuspidalJacquetMultiplicity.induced T B` of the same-carrier twist
`T.leviComplexPowerTwist B z σ.ρ`. The twisting character is the published

\[
\chi_z((m_i)_i)=\prod_i (|\det(m_i)|_F:\mathbb C)^{z_i}.
\]

The absolute value is the Library's residue-normalized one. Here `z i` is a
determinant exponent. On block scalars `a_i I_(B.size i)` the character has
exponents `(B.size i) * z i`, by the imported
`T.coe_leviComplexPowerCharacter_blockScalar`; these block-size-weighted
scalar values are not the parameters of the family.

`induced_apply` and `induced_representation` identify the bundle and its
action with `T.normalizedParabolicInduced B (T.leviComplexPowerTwist B z σ.ρ)`.
`isSmooth_induced` is the existing smoothness of normalized induction.
`inducedEval` evaluates the actual smooth induced functions, with
`inducedEval_add` and `inducedEval_smul` recording linearity.
`inducedEval_action` proves right translation, `f(x g)`, and
`inducedEval_covariant` proves

\[
 f(p x)=\delta_B(m(p))^{1/2}\,
        \chi_z(m(p))\,\sigma(m(p))f(x),
\qquad p\in P_B,\ m(p)\text{ its Levi projection}.
\]

The half modulus is the existing positive square root of the upper full
block modulus `T.leviModulus B`; the character is the actual
`T.leviComplexPowerCharacter B z`. The smooth-function carrier may depend on
`z`; no common model or analytic trivialization of these carriers is
supplied.

`induced_zero` recovers the ordinary induction of `σ`. `induced_ofReal`
proves that at `z i = (t i : ℂ)` the family is exactly
`RealTwistFamilies.induced T B σ t`.

## Unitary and mixed slices

For arbitrary real `u` and `r`, `unitaryInduced T B σ u` is the family at
`z i = Complex.I * (u i : ℂ)`, and `mixedInduced T B σ r u` is the family
at `z i = (r i : ℂ) + Complex.I * (u i : ℂ)`. `unitaryInduced_apply` and
`mixedInduced_apply` unfold them. `norm_unitaryCharacter` restates the
published norm-one property of the unitary-slice character at every actual
Levi element; it is a character identity, not a temperedness or
unitarizability statement about the induced representation.

`unitaryInduced_zero` recovers the ordinary induction,
`mixedInduced_zero_left` gives the unitary slice at `r = 0`, and
`mixedInduced_zero_right` gives `RealTwistFamilies.induced T B σ r` at
`u = 0`. `leviComplexPowerTwist_mixed` proves that the mixed twist is the
published real twist `T.leviRealPowerTwist B r` of the unitary twist, and
`mixedInduced_eq_realInduced` concludes that the mixed slice is the real
family of the unitary twist `Rep.of (T.leviComplexPowerTwist B (I u) σ.ρ)`,
with equality of the bundled representations.

## Real-indexed complex affine parameter maps

Parameter maps are ordinary Mathlib affine maps
`(ι → ℝ) →ᵃ[ℝ] (κ → ℂ)`: the domain is the real parameter space and the
complex determinant space is viewed as a real affine space. No
complexification of a real affine map is required.
`affine_apply` proves `a u = a 0 + a.linear u`.

`realInclusion ι` and `imaginaryInclusion ι` are the real-linear maps
`v ↦ (v j : ℂ)` and `v ↦ Complex.I * (v j : ℂ)`, coordinatewise.
For a real offset `r : κ → ℝ` and real-linear `L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)`,
`mixedAffine r L` is the constant map `realInclusion κ r` plus the linear map
`imaginaryInclusion κ ∘ L`. `mixedAffine_apply` gives

\[
 a(u)(j)=(r(j):\mathbb C)+i\,(L(u)(j):\mathbb C).
\]

`mixedAffine_zero` gives its value `r` at zero, `mixedAffine_linear` its
linear part, `re_mixedAffine_apply` its constant real part `r j`, and
`im_mixedAffine_apply` its imaginary part `L u j`.

`unitaryAmbient B` is the canonical unitary ambient map `mixedAffine 0 id`
(`unitaryAmbient_eq`), and `unitaryAmbient_apply` gives `u ↦ (i u_i)_i`.
For an actual refinement `S : BlockRefinement B`,
`refinedMixedAffine B S r` is `mixedAffine r` with linear part the published
coarse restriction `RealTwistFamilies.restrictParameter B S`, for arbitrary
real offset `r` on the fine blocks. `refinedMixedAffine_apply` proves

\[
 a(u)(k)=(r(k):\mathbb C)+i\,u\big(\mathrm{parent}(k)\big),
\]

with `parent(k) = ((B.flattenBlockEquiv S).symm k).1`, the existing
refined-Levi convention. This specialization asserts no branch or
occurrence property.

`ofRealAffine a` is `realInclusion ∘ a` for a real-valued affine map `a`,
and `ofRealAffine_apply` gives its coordinates `(a u j : ℂ)`.

## Transported candidates

For an actual permutation `w`, a proof
`hw : CuspidalSupport.ConjugatesLevi D C w` that its permutation matrix
conjugates the embedded `D`-Levi onto the `C`-Levi, an arbitrary
`ω : Rep.{uW} ℂ (D.Levi F.Carrier)` and a real-indexed complex affine map
`a`, `transported T B D C w hw ω a u` complex-twists `ω` at `a u` and then
applies the existing `CuspidalSupport.transport D C w hw`. Its carrier is
exactly that of `ω`, in universe `uW`. Writing
`e = CuspidalSupport.leviConjugation D C w hw`, `transported_action` proves

\[
 m\cdot v=\chi_{a(u)}(e^{-1}m)\,\omega(e^{-1}m)v,
\]

with both the character and the representation evaluated at the actual
inverse Levi conjugation. `transported_apply` unfolds the bundle.
`transported_zero` handles the zero affine map, leaving the ordinary Weyl
transport of `ω`. `transported_one` removes transport by the identity
permutation for any `hw` and any parameter map, using the published
`CuspidalSupport.transport_one`; the identity conjugacy itself is the
published `CuspidalSupport.conjugatesLevi_one`, not reproved here.
`transported_ofRealAffine` proves that the `ofRealAffine` inclusion of a
real affine map gives exactly `RealTwistFamilies.transported`.

## Occurrence

`Occurs T B D C σ w hw ω b a u` uses an ambient map
`b : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin B.length → ℂ)` and a candidate map
`a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℂ)`. At the same real `u`, it
applies `T.IsOppositeJacquetClassExponent C` to the entire induced
representation `induced T B σ (b u)` and to the candidate
`transported T B D C w hw ω a u`. `occurrenceLocus` is its set of real
parameters, and `mem_occurrenceLocus` is the defining membership.
`occurs_iff` exposes exactly the existing candidate irreducibility and
admissibility (with `T.topology`), together with an actual invariant
subspace of the opposite Jacquet module and a surjective intertwiner from it
onto the candidate. These conditions belong only to the predicate, not to
the construction of the families.

The opposite Jacquet bundle is exactly
`CuspidalJacquetMultiplicity.oppositeJacquet T C`: coinvariants under the
actual lower block radical, normalized by the inverse of the upper full
modulus. There is no replacement Jacquet carrier, formal character set,
asymptotic module, or certificate containing an occurrence conclusion.

`occurs_ofRealAffine_iff` proves that the ambient
`ofRealAffine (AffineMap.id ℝ _)` and candidate `ofRealAffine a` give exactly
the published `RealTwistFamilies.Occurs T B D C σ w hw ω a t`, and
`occurrenceLocus_ofRealAffine` gives the corresponding equality of loci.
`occurs_unitaryAmbient_mixedAffine_iff` shows that the canonical unitary
ambient map is directly usable with `mixedAffine r L`: occurrence unfolds to
the class-exponent predicate for `unitaryInduced T B σ u` and the transport
of the twist of `ω` by `r + i L(u)`.
`occurs_unitaryAmbient_refinedMixedAffine_iff` specializes to the identity
permutation on `B.flatten S` and `refinedMixedAffine B S r`, where
occurrence unfolds to the untransported fine-Levi twist by
`r k + i u(parent k)`.

## Provenance, intrinsic proofs, and limits

This is internal packaging of imported Library operations, not a theorem
stated in this form in the literature. It imports
`Langlands.Representation.Exponents.RealTwistFamilies`,
`Langlands.Representation.Twist.LeviComplexPower` and
`Langlands.Representation.CuspidalSupport.LeviAssociation`. Existing
definitions, statements and target dependencies are unchanged.

The normalization is motivated by A. J. Silberger, *The Langlands quotient
theorem for p-adic groups*, Math. Ann. 236 (1978), 95–104, retained at
`literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`
and registered as
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
Printed p.96 (one-based PDF page 2, inspected as an image, since text
extraction drops the imaginary unit) defines
`χ_ν(m) = q^(i⟨ν,H(m)⟩)` and `σ_ν(m) = σ(m)χ_ν(m)`. As in the published
[source note](../../../notes/jacquet/silberger-continuation-parameters.md),
the source parameter `ν` corresponds to Library determinant exponent
`i ν`. Thus `unitaryInduced` with real `u` is the source's `ν = u`,
`mixedInduced` with `r` and `u` is `ν = u - i r`, and the real family at
`t` is `ν = -i t`. These are coordinate conversions only: block-scalar
values still multiply the determinant exponents by block sizes, and no
formalization of the source's general Lie-algebra map is claimed.

Printed p.102 (PDF page 8, inspected as an image) states, inside
Proposition 5.8,
`ω_{i s v₀ + ν''} ∈ 𝔇_{I(P'',σ''_{ν''})}(P,A)` for all `ν''`. The ambient
induction varies by `σ''_{ν''}`; this unit keeps that visible by allowing a
separate ambient map `b`, with `unitaryAmbient` as the canonical choice.
The candidate coordinate `-s v₀ + i ν''`, with the coarse parameter
restricted, has the shape of `refinedMixedAffine B S r` for an offset `r`
that a consumer would still have to identify with `-s v₀`. That
identification, any general compatibility of the character with Weyl
conjugation, and any source-specific shape equality or `flattenedLeviEquiv`
comparison belong to later adapters; none follows from a parameter formula
alone and none is asserted here.

The continuation passages in Lemma 5.6 (p.101), Proposition 5.8 (p.102) and
the proof of Proposition 6.1 (pp.102–103) motivate later consumers but are
not proved or encoded in this pair. This unit proves no analytic
continuation, almost-all-to-zero passage, fixed-label selection, collision
persistence, multiplicity or Hom comparison, arbitrary-quotient extraction,
or classification theorem. Occurrence in the entire induction is distinct
from occurrence in an arbitrary irreducible quotient. The published
[Lemma 5.3 scope audit](../../../notes/jacquet/silberger-lemma53-scope.md)
remains in force; unrestricted Lemma 5.3 and Corollary 5.4 are not used.
No preservation of temperedness or unitarizability is stated.

The intrinsic proofs are as follows. Evaluation, action, the unfoldings of
the bundles, slices and loci, the mixed and refined coordinate formulas,
the transported action and the occurrence unfolding are definitional.
Covariance applies the existing normalized-induction covariance theorem to
the complex twist, and smoothness is the existing induction smoothness.
Zero identities use the published zero-twist law. The real specializations
use the published `leviComplexPowerTwist_ofReal`; the mixed decomposition
combines it with the published addition law `leviComplexPowerTwist_add`.
The unitary norm-one identity is the published imaginary-parameter norm
formula. Identity transport is the published `transport_one`. The affine
formula follows from `AffineMap.map_vadd` at zero, and the remaining
parameter equalities are pointwise arithmetic. These proofs assert no
representation-theoretic continuation or classification result.
