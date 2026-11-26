# Concordant integrals from the two Weyl decompositions

The module `Langlands.BaseChange.ConcordantIntegralComparison` states and proves
`ConcordantIntegralComparisonReductionStatement.{u, v}`: the implication

- `OrdinaryWeylHaarLocalPushforwardsStatement.{u}` (local Haar pushforward identities of
  the ordinary Weyl maps, weighted by the absolute discriminant),
- `TwistedWeylHaarLocalPushforwardsStatement.{u, v}` (the same for the twisted Weyl maps,
  with exact norm lifts),
- `RegularSemisimpleOpenConullStatement.{u}`,
- `SigmaRegularOpenConullStatement.{u, v}`

`→ ConcordantIntegrableIntegralEqualityStatement.{u, v}`.

The conclusion says: for a nonarchimedean local field `F`, a cyclic `F`-algebra
`(E, σ, l)` with its module topology, Haar measures `μF` on `GL_n(F)` and `μE` on
`GL_n(E)`, and integrable functions `φ` on `GL_n(E)` and `f` on `GL_n(F)` that concord
(`AreConcordant`), the integrals `∫ φ dμE` and `∫ f dμF` are equal. The theorem
`concordantIntegralComparisonReduction` proves the implication. No characteristic
hypothesis is made.

## Source

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mém. SMF 124 (2011), II.2.10–II.2.11, printed pp. 70–73.
For a set of representatives `T` of the rational conjugacy classes of maximal tori,
the two Weyl integration formulas of II.2.10 (printed p. 72) read

- formula (1): `∫_{G(E)} φ Θ dg_E = Σ_T |W_T(F)|⁻¹ ∫_{T(E)_{σ-1} \ T(E)} |D_G(N δ)|_F Λ_σ(φ, δ) Θ(δ) dδ_{T,σ}`;
- formula (2): `∫_{G(F)} f θ dg = Σ_T |W_T(F)|⁻¹ ∫_{T(F)} |D_G(γ)|_F Λ(f, γ) θ(γ) dγ_T`.

On printed p. 71 the norm identifies `T(E)_{σ-1} \ T(E)` with the open subgroup
`N(T(E))` of `T(F)` (Hilbert's Theorem 90 gives the kernel), and `dδ_{T,σ}` is the measure
that this identification transports from the Haar measure `dγ_T` restricted to `N(T(E))`.
So formula (1) integrates over the norm image in `T(F)` against restricted torus Haar
measure, while formula (2) integrates over all of `T(F)`. Both summands carry the
reciprocal order `|W_T(F)|⁻¹` of the rational Weyl group. In the Library's decompositions
(`ordinaryWeylIntegralDecomposition`, `twistedWeylIntegralDecomposition`) these become
integrals over the subtypes `T.regularPoints` and `T.regularNormPoints σ l` of the rational
torus, each with the pullback of the same torus Haar measure. The integrands
`WeylTorus.ordinaryOrbitIntegrand` and `WeylTorus.twistedOrbitIntegrand` contain the factor
`(Nat.card T.RationalWeylGroup)⁻¹` and the weight `WeylTorus.discriminantWeight` at the
rational point. The non-regular points form a null set and do not contribute. The first
half of II.2.11 (printed p. 72) applies (1) and (2) to concordant test functions weighted
by the character functions. The comparison proved here is the unweighted form of that
step, for integrable functions. The four premises are the measure-theoretic inputs of the
two formulas in the form the Library states them.

## Proof

1. *Representatives.* Rational conjugacy of `WeylTorus F n` is an equivalence relation
   (`WeylTorus.isConjugate_refl`, `WeylTorus.IsConjugate.symm`,
   `WeylTorus.IsConjugate.trans`). Choosing one element in each class gives a set `S`
   with `WeylTorus.IsRepresentativeSet S` (`WeylTorus.exists_isRepresentativeSet`).
2. *Measures on each torus.* The subgroup `T.val` is closed, being a centralizer
   (`WeylTorus.isClosed_val`), hence locally compact. Its Haar measure is right invariant
   because the torus is commutative (`WeylTorus.isMulRightInvariant_of_isHaarMeasure`).
   Haar measures on `GL_n(F)` and `GL_n(E)` are right invariant
   (`generalLinear_haar_rightInvariant`). Weil's theorem
   `QuotientIntegration.compatibleMeasureExists` then gives a compatible quotient measure
   on `T(F) \ GL_n(F)` (`WeylTorus.exists_ordinaryMeasures`). Base change is a closed
   embedding (`IsCyclicAlgebra.isClosedEmbedding_baseChange`). It identifies `T.val`
   with the closed subgroup `H = T.val.map (baseChange F E n)` of `GL_n(E)` as
   topological groups. The pushforward of the torus Haar measure is a right Haar measure
   on `H` whose image in `GL_n(E)` is the base change of the torus measure. Weil's theorem
   again gives a compatible quotient measure on `H \ GL_n(E)`
   (`WeylTorus.exists_twistedMeasures`).
3. *Decompositions.* The premise on ordinary pushforwards, with these measures, satisfies
   the hypothesis of `ordinaryWeylIntegralDecomposition`. The quotient measures and the
   pullbacks of the torus Haar measures to the regular points are σ-finite: the spaces are
   locally compact and second countable, and the regular points form an open set by the
   openness part of `RegularSemisimpleOpenConullStatement`. The weight
   `WeylTorus.discriminantWeight` is positive and locally constant, because the
   discriminant of a regular semisimple element is a unit (`det_ordinaryWeylDifferential`).
   This gives `∫_{G(F)_reg} f dμF` as the sum over `S` of the torus integrals of
   `WeylTorus.ordinaryOrbitIntegrand`. The premise on twisted pushforwards supplies the
   measurability of the regular norm points and the lifts. With them,
   `twistedWeylIntegralDecomposition` gives `∫_{G(E)_{σ-reg}} φ dμE` as the sum of the
   torus integrals of `WeylTorus.twistedOrbitIntegrand`.
4. *Orbital integrals.* At a regular point `t` of `T`, `glCentralizer t = T.val`
   (`WeylTorus.glCentralizer_eq_of_regularPoint`). At a regular norm point with lift `δ`,
   `sigmaCentralizer σ n δ = H` (`sigmaCentralizer_eq_map_glCentralizer_of_cyclicNorm_eq`).
   `exists_subgroup_transport` moves measures and compatible quotient measures between
   equal subgroups, keeping coset integrals. So the inner integrals of the two
   decompositions are an orbital integral `orbitalIntegral t νγ f` and a σ-orbital integral
   `sigmaOrbitalIntegral σ n δ νδ φ` for compatible measures
   (`WeylTorus.exists_orbitalIntegral_eq`, `WeylTorus.exists_sigmaOrbitalIntegral_eq`).
   The centralizer measures are associated in the sense of `IsAssociatedMeasure` with
   conjugator `1`, since `N(δ)` is exactly the base change of `t`.
5. *Torus terms.* `WeylTorus.twistedTerm_eq_ordinaryTerm` compares the two torus terms.
   Both are set integrals over subsets of `T.val` against the torus Haar measure
   (`integral_subtype_comap`). At a regular norm point the two integrands agree by
   concordance (`ConcordAt`). At a regular point outside the norm image the ordinary
   integrand vanishes: such a point is not a norm (`WeylTorus.mem_normImage_iff_isNorm`),
   so `VanishesOffNorms` applies. The integral over the regular points therefore reduces to
   the regular norm points (`setIntegral_eq_of_subset_of_forall_sdiff_eq_zero`).
6. *Conullity.* The complements of the regular semisimple and σ-regular sets are null
   for every Haar measure. So the two ambient integrals equal the integrals over these
   sets, and the termwise equality of the two sums gives `∫ φ dμE = ∫ f dμF`. The null-set
   premises are stated for the Borel σ-algebra. They are applied to the given Borel
   instance by substituting `BorelSpace.measurable_eq`.
