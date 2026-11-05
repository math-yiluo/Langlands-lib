# Haar rescaling of the actual formal degree

This is an internal normalization construction for the actual central-quotient
Schur integral and the existing canonical discrete-series classes. If a Haar
measure is multiplied by a positive finite scalar, the class set is unchanged
and the actual formal degree is divided by that scalar:

\[
E_c:\mathcal E_2(G,A,\mu)\simeq\mathcal E_2(G,A,c\mu),\qquad
d_{c\mu}(E_c\omega)=c^{-1}d_\mu(\omega).
\]

The source for the normalization is Waldspurger (2003),
`waldspurger-2003-plancherel`, III.1 (3), printed p.265 / PDF p.31.
That passage characterizes the positive real formal degree by

\[
\int_{A_G\backslash G}
 \ell_1(\pi(g)v_1)\ell_2(\pi(g^{-1})v_2)\,d\mu(g)
 =d_\mu(\pi)^{-1}\ell_2(v_1)\ell_1(v_2).
\]

The present measure-scaling laws are derived from this characterization; they
are not attributed to a separate scaling proposition in the source. Lean uses
the existing quotient by an explicit normal central subgroup `A`, which has
the same left/right cosets because `A` is central. Identification of `A` and
its measure with the source's split-center quotient remains a separate
specialization.

The common setting is a topological group `G`, a normal subgroup `A` contained
in its center, a measurable Borel quotient `G/A`, and an actual Haar measure
`μ` on that quotient. The scalar is `c : ℝ≥0` with `[NeZero c]`; thus it is
positive and finite, with no extra upper bound. The group and representation
carrier universes are independent. There is no finite-dimensional-carrier,
field-characteristic, splitness or quasisplitness restriction.

`isSquareIntegrableModCentralSubgroup_smul_measure_iff` proves that the existing
square-integrability predicate for `c • μ` is equivalent to that for `μ`.
The predicate includes admissibility, an actual unitary character acting
scalarly on the full center, and `MemLp 2` for every smooth-dual coefficient
norm on `G/A`. The proof retains the same admissibility and character witnesses.
Mathlib's `MemLp.smul_measure` supplies the forward rescaling; applying it with
`c⁻¹` supplies the reverse implication, since `c⁻¹ • (c • μ) = μ`.
No irreducibility or Schur conclusion is required for this comparison.

`isDiscreteSeriesClass_smul_measure_iff` transfers that equivalence to the
existing predicate on the canonical `SmoothDualClass`, by quotient induction.
`discreteSeriesClassHaarScalingEquiv` is consequently the identity on underlying
smooth isomorphism classes between the existing two discrete-series subtypes.
Its inverse is also the identity on these classes. The computation laws
`discreteSeriesClassHaarScalingEquiv_val` and
`discreteSeriesClassHaarScalingEquiv_mk` identify this transport respectively
on underlying classes and on every actual irreducible admissible
representative. No alternate representation quotient is introduced.

The integral comparison `orthogonalityIntegral_smul_measure` is more general.
For two representations with independent carrier universes and the same scalar
character on `A`, it proves

\[
I_{c\mu}(v_1,\ell_1,w_2,\ell_2)
 = (c:\mathbb C)I_\mu(v_1,\ell_1,w_2,\ell_2).
\]

Here both integrals use the existing well-defined quotient lift of the actual
crossed coefficient product. This theorem only requires the measurable quotient
and its measure, along with the group topology used by the smooth duals and
the displayed scalar-action witnesses. It omits normality, centrality, Borel
compatibility and Haar assumptions. It allows `c = 0` and does not require
integrability: Mathlib's Bochner integral scaling law
`integral_smul_nnreal_measure` applies with its total-integral convention.
The real scalar action on the complex integral is then complex multiplication.

The degree comparisons additionally assume inversion invariance of `μ` and
cofinality of compact open subgroups among open subgroups of `G`. They use the
actual formal degree constructed in `FormalDegreeComparisons`, with
irreducibility and square-integrability of the representation. For `c • μ`,
Haar and inversion-invariance instances are constructed locally: nonzero
nonnegative rescaling preserves Haar measure, and mapping the scaled measure
by inversion commutes with scalar multiplication. There are no extra
scaled-measure hypotheses for the caller and no new global instances.

`representationFormalDegree_smul_measure` proves

\[
d_{c\mu}(\rho)=c^{-1}d_\mu(\rho),
\]

where the square-integrability proof on the left is explicitly transported by
the preceding equivalence. The proof restricts the full central character from
the original square-integrability witness to `A`, scales the actual Schur
integral, and applies the existing `formalDegree_unique`. Complex coercion and
inverse identities show that the proposed value has exactly the scaled
crossed-pairing characterization. Schur existence, positivity and uniqueness
are reused; no degree or desired normalization identity is assumed.

Finally, `discreteSeriesFormalDegree_smul_measure` proves the displayed law for
the existing class degree using the canonical transport `E_c`. Quotient
induction and the computation law for every representative reduce it to the
actual representation law. The central subgroup, underlying representations,
quotient and coefficient functions remain the same; the changed measure is
explicit in every comparison.

This construction supplies a measure-normalization comparison toward the
Plancherel program. It does not yet transport the unitary twist-orbit quotient
or its degree. The source split-center and rational-point realizations, compatible
measures on other groups and character orbits, formal-degree comparisons under
changes of quotient, the Fourier and polynomial arguments of III.7, and the
Plancherel transform and inversion remain separate obligations.
