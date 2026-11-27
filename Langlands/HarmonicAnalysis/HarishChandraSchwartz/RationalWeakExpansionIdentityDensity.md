# The pointwise weighted identity at every orbit point from a dense set of orbit points

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionIdentityDensity`.
The continuity statement is in the namespace `Langlands.HarishChandraSchwartz`; the dense
identity statement and the reduction are in `Langlands.HarishChandraSchwartz.WeakExpansion`.

## Purpose and contents

`WeightedWeakExpansionIdentityStatement` (module `RationalWeakExpansionIdentityInputs`) is the
identity of Waldspurger's proof of Proposition VI.3.1 (printed p.304),

`µ^G(ω) (f_ω)^w_{P'}(m') = Σ_s µ^{M'}(sω) (E^{M'}_{M'∩s·P} Ψ_{s, sω})(m')`,

at **every** point `ω` of the unitary orbit `O` and every `m' ∈ M'(F)`. Proposition V.1.1
(printed p.289), from which the source derives it, is stated only at the `G`-regular points of
`O`. This module isolates the passage from a dense set of orbit points to all of `O`. It contains

- `RationalOrbitWeakTermContinuityStatement`, a Prop-valued definition: the weak constant term
  is continuous on the unitary orbit. This file does not prove it.
- `WeightedWeakExpansionDenseIdentityStatement`, a Prop-valued definition: the identity holds on
  a dense set of orbit points. This file does not prove it.
- `weightedWeakExpansionIdentity_of_dense` (proved): the two statements, for the same data,
  imply `WeightedWeakExpansionIdentityStatement`.
- Private helper lemmas used by the proof: `continuous_lowerWeight`,
  `continuous_lowerCoefficient_comp`, `continuous_lowerWeightedSum` and
  `forall_eq_of_dense_setOf_eq`.

## The continuity statement

**Definition `RationalOrbitWeakTermContinuityStatement`.** Explicit arguments
`hG hi hν I J hKc hPK π C hC mu hsq hA`, the data of `rationalOrbitWeakConstantTerm` (module
`RationalOrbitPositiveConstantTerm`): a connected reductive `G` over a nonarchimedean local field
`F` with maximal split torus `i` and generic `ν`, finite sets `I`, `J` of simple roots, a compact
open `K` with the Iwasawa pair `G(F) = P_∅(F) K`, an irreducible admissible `π` of
`M_I(F) = standardLeviPoints i ν (rootSet I)`, a normal central subgroup `C` of `M_I(F)` with a
measurable structure and a Haar measure `μ` on `M_I(F)/C`, square integrability `hsq` of `π`
modulo `C`, and a compatible split component `hA : IsCompatibleStandardSplitComponent` of
`M' = M_J`. Body: for the Borel structure on `M_I(F)/C` (binder `∀ [BorelSpace (M_I(F) ⧸ C)]`),
every section `Φ ∈ C^∞(O, P)` (`rationalInducedSmoothOrbitSections`) and every `m' ∈ M'(F)`, the
map `ω ↦ rationalOrbitWeakConstantTerm … Φ ω m'`, `ω ↦ (f_ω)^w_{P'}(m')`, is continuous on the
orbit `O = discreteSeriesOrbit C hC mu νM (discreteSeriesClass C hC mu π hsq)`.

**Relation to the Library.** The published `RationalOrbitWeakTermParameterContinuityStatement`
(module `RationalOrbitWeakTermParameterContinuity`, proved there by
`rationalOrbitWeakTermParameterContinuity`) has the same data and the same conclusion, under
additional structural premises: a compact subgroup `K0` with Renard's simultaneous standard basis
(`SimultaneousStandardBasisAt`), the Cartan covering of `M_I(F)`
(`StandardLeviCartanCovering`) and a compact open normal basis `B` of `K0` whose members satisfy
`StandardParabolicBasisMember` for `P' = P_J` and the given split component `hA`.
`RationalOrbitWeakTermContinuityStatement` is that conclusion without these premises, so it
follows from `rationalOrbitWeakTermParameterContinuity` once such `K0` and `B` exist for the given
split component. The published `exists_constantTermPremises_of_joint` (module
`RationalSpecialCompactConstantTermPremises`) gives a `K0` with the basis and the Cartan
coverings from `JointSpecialCompactBasisExistenceStatement`; `SimultaneousStandardBasisAt`
supplies basis members for some compatible split component of each standard Levi, not
necessarily for a prescribed one.

**Meaning.** In the source the continuity of `χ ↦ (E^G_P sp_χ ψ)^w_{P'}(m')` on `Im X(M)` is used
without comment when the identity of p.304 is asserted for every `χ ∈ Im X(M)`.

## The dense identity statement

**Definition `WeightedWeakExpansionDenseIdentityStatement`.** It has exactly the explicit
arguments of `WeightedWeakExpansionIdentityStatement`,
`hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq hRefl hCST PG hA R PM`, with the same section
variables and local instances (those of `RationalWeakExpansionTargets`; see the Markdown of
`RationalWeakExpansionIdentityInputs`, "Data and binders"), and the finite type structure on the
Weyl indices given by `finite_weylIndex`. Body: if `I'` is proper, `IsSpecialVertexCompact ν hi K`,
`LiftsInCompact R` and `hN : SourceCompactNormalization …` hold, then for every section `q`, every
family of extensions `E s : WeightedCExtension … (hN s)`, every family of lower sections
`Ψ s : LowerSections … s` with `IsWeightedCSection … (hN s) (E s) q (Ψ s)` for all `s`, and every
`m' ∈ M'(F)`, the set

`{ω ∈ O | Wπ(ω) · rationalOrbitWeakConstantTerm … q ω (leviRationalPointHomeomorph i ν I' m')
  = Σ_s lowerPlancherelWeight … (PM s) (sω) ·
      DynamicInducedOrbit.inducedOrbitCoefficientMap … (Ψ s) (sω) m'}`

(`sω = lowerOrbitMap … ω`) is dense in `O`. The premises, the types of `q`, `E`, `Ψ` and the two
sides of the identity are written exactly as in `WeightedWeakExpansionIdentityStatement`; the
only difference is that the conclusion "for every `ω ∈ O`" is replaced by "for a dense set of
`ω ∈ O`, which may depend on `q`, `E`, `Ψ` and `m'`".

**Meaning.** The statement is implied by `WeightedWeakExpansionIdentityStatement` (the whole orbit
is dense). It is the form in which Proposition V.1.1 enters: V.1.1 gives
`(E^G_P ψ)^{w,Ind}_{P'} = Σ_s E^{P'}_{M'∩s·P}(c_{P'|P}(s, ω)ψ)` at the `G`-regular points `ω` of
`O`; multiplied by `µ^G(ω)`, and with `µ^G(ω) c_{P'|P}(s, ω) = µ^{M'}(sω) c̃_{P'|P}(s, ω)` where
`µ^{M'}(sω) ≠ 0` (the definition of `c̃` in Corollary V.2.3), it gives the weighted identity at
those points. Any dense set of points at which the weighted identity is
established suffices for the reduction below; the statement does not name the set.

## The proved reduction

**Theorem `weightedWeakExpansionIdentity_of_dense`.** Hypotheses:
`RationalOrbitWeakTermContinuityStatement hG hi hν I I' hKc hPK π CM hCM mu hsq hA` (with
`C = C_M = rationalLeviSplitCenter I sc`) and
`WeightedWeakExpansionDenseIdentityStatement` for the data of the conclusion. Conclusion:
`WeightedWeakExpansionIdentityStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq hRefl hCST PG
hA R PM`.

Proof as implemented. Introduce the premises, `q`, `E`, `Ψ`, the section formulas, `ω` and `m'`,
and generalize `ω` again, so that the goal is `∀ ω, f ω = g ω` for the two sides `f`, `g` of the
identity. `forall_eq_of_dense_setOf_eq` (two continuous complex functions on a topological space
that agree on a dense set agree everywhere, from Mathlib's `Continuous.ext_on`) reduces it to
three goals.

1. `f` is continuous: `µ^G` is continuous on `O` by the published
   `continuous_standardLeviPlancherelWeight`, applied to the fields of the density package `PG`,
   and the weak constant term is continuous by the continuity hypothesis applied to `q` and
   `leviRationalPointHomeomorph i ν I' m'`; their product is continuous.
2. `g` is continuous (`continuous_lowerWeightedSum`): it is a finite sum over the Weyl indices,
   and each summand is the product of `ω ↦ µ^{M'}(sω)` and `ω ↦ (E^{M'} Ψ_{s, sω})(m')`. The lower
   orbit map `ω ↦ sω` is continuous by the published `continuous_lowerOrbitMap` (module
   `RationalWeakExpansionContinuity`). The lower weight `lowerPlancherelWeight (PM s)` is continuous
   by the published `DynamicInducedOrbit.continuous_orbitPlancherelWeight` for the lower
   ambient group `M'`, the conjugated cocharacter and the lower package (`continuous_lowerWeight`).
   The lower coefficient at the fixed point `m'` is continuous on `sO` by the published
   `DynamicInducedOrbit.continuous_inducedOrbitCoefficientMap` (`continuous_lowerCoefficient_comp`
   composes it with the lower orbit map). These are the arguments of the private lemmas of
   `RationalWeakExpansionContinuity`, repeated here because those lemmas are private.
3. The set `{ω | f ω = g ω}` is dense: the dense identity hypothesis applied to the premises, `q`,
   `E`, `Ψ`, the section formulas and `m'`.

The right side and the set of goals 2 and 3 were elaborated in different modules; as Lean
expressions they differ only in the auxiliary proof constants that Lean generates in each module,
whose types coincide, so these goals are closed by `with_reducible exact`. The proof uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the source

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, registered as
`waldspurger-2003-plancherel` (SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`); PDF page = printed
page − 234.

- **Proposition V.1.1 (printed p.289).** "Soient `ω` un élément `G`-régulier de `O` et
  `ψ ∈ L(ω, P)`. On a l'égalité `(E^G_P ψ)^{w,Ind}_{P'} = Σ_{s∈W(M'|G|M)} E^{P'}_{M'∩s·P}(c_{P'|P}(s, ω)ψ)`."
  The identity is asserted at the `G`-regular points only.
- **Proof of Proposition VI.3.1 (printed p.304).** "D'après la Proposition V.1.1 et le
  Corollaire V.2.3, … pour tout `m' ∈ M'` et tout `χ ∈ Im X(M)`, on ait l'égalité
  `µ(ω⊗χ)(E^G_P sp_χ ψ)^w_{P'}(m') = Σ_s µ^{M'}(s(ω⊗χ))(E^{M'}_{M'∩s·P} sp_χ c̃_{P'|P}(s)ψ)(m')`."
  Here the identity is asserted at every `χ ∈ Im X(M)`; the source does not spell out the
  passage from the `G`-regular points.

The reduction of this module supplies that passage by continuity: both sides are continuous on
`O`, and a dense set of points where they agree suffices. The separation into a continuity
statement and a dense identity statement is derived from this argument and is not a step of the
source.

## Imports

`RationalWeakExpansionIdentityInputs` (the identity statement, and through it the targets module
with `WeightedCExtension`, `IsWeightedCSection`, `LowerSections`, `SourceCompactNormalization`,
`LiftsInCompact`, `IsSpecialVertexCompact`) and `RationalWeakExpansionContinuity`
(`continuous_lowerOrbitMap`, and through it `DynamicInducedOrbitCoefficientContinuity`). The
module sets `maxRecDepth` to 8000, as `RationalWeakExpansionContinuity` does; the dense identity
statement raises `maxHeartbeats` to 3000000, as the identity statement does, and the continuity
lemmas and the reduction raise it to at most 5200000, because the terms are large. No `sorry` and
no new axioms.
