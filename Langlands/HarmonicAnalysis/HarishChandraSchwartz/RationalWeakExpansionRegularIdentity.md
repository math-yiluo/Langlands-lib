# The weighted identity at the regular points of the unitary orbit

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionRegularIdentity`,
namespace `Langlands.HarishChandraSchwartz.WeakExpansion`.

## Purpose and contents

`WeightedWeakExpansionDenseIdentityStatement` (module `RationalWeakExpansionIdentityDensity`)
asks for the weighted identity of Waldspurger's proof of Proposition VI.3.1 (printed p.304),

`µ^G(ω) (f_ω)^w_{P'}(m') = Σ_s µ^{M'}(sω) (E^{M'}_{M'∩s·P} Ψ_{s, sω})(m')`,

on some dense set of points `ω` of the unitary orbit `O` of `π`. Proposition V.1.1 (printed
p.289), from which the source derives the identity, is stated at the `G`-regular points of `O`.
This module fixes the dense set: the orbit points `π ⊗ χ` for the unitary unramified characters
`χ` of `M_I(F)` such that `π ⊗ χ` is regular for the literal normalizer of `M_I(F)` in `G(F)`.
It contains

- `regularUnitaryTwists` (definition): this set of characters, for any smooth representation of
  `M_I(F)`;
- `RegularUnitaryTwistDenseStatement`, a Prop-valued definition: the regular unitary twists are
  dense. This file does not prove it;
- `WeightedWeakExpansionRegularIdentityStatement`, a Prop-valued definition: the weighted
  identity holds at every orbit point `π ⊗ χ` with `χ` a regular unitary twist. This file does
  not prove it;
- `dense_orbitMap_image` (proved): the orbit map carries dense sets of characters to dense sets
  of orbit points;
- `weightedWeakExpansionDenseIdentity_of_regular` (proved): the two statements imply
  `WeightedWeakExpansionDenseIdentityStatement`.

The section variables and local instances are those of `RationalWeakExpansionIdentityDensity`
(and of `RationalWeakExpansionTargets`): `F` a nonarchimedean local field, `G` a group scheme over
`F` with affine, locally finite type structure morphism, `i : T ⟶ G`, `ν` a cocharacter, and
`M_I(F) = standardLeviPoints i ν (rootSet i ν I)` as a subtype of `G(F)`. The unramified
characters of `M_I(F)` are those of the rational norm characters `leviRationalNormCharacters i ν I`.

## Regular unitary twists

**Definition `regularUnitaryTwists i ν I σ`.** For a smooth representation
`σ : SmoothRep.{0, u, uV} ℂ M_I(F)`, the set of `χ ∈ unitaryUnramifiedCharacters
(leviRationalNormCharacters i ν I)` such that the twist `σ ⊗ χ` (`SmoothRep.twist` by the
character `χ`, whose kernel is open by `unramifiedCharacter_isOpen_ker`) satisfies
`IsNormalizerRegular` (module `Langlands.Representation.Aubert.General.NormalizerRegularity`): for
every element `g` of the normalizer of the subgroup `M_I(F)` in `G(F)` with `g ∉ M_I(F)`, the
conjugate of `σ ⊗ χ` by `g` is not isomorphic to `σ ⊗ χ`.

**Provenance.** Waldspurger (`waldspurger-2003-plancherel`, printed p.276, before Corollary
III.7.3) calls a square integrable `ω` regular when no nonidentity element of the finite group
`W(G|M)` fixes its class. `IsNormalizerRegular` is the Library's derived form of this
condition for the literal normalizer of `M_I(F)` in `G(F)`; it is the regularity used by the
published `RegularSquareIntegrableJacquetMultiplicityStatement` and
`UnitaryRegularParabolicIrreducibilityStatement`. This module does not compare the two notions.

## The density statement

**Definition `RegularUnitaryTwistDenseStatement i ν I`.** If `G` is connected reductive, `i` is
a maximal split torus and `ν` is generic, then for every smooth representation
`σ : SmoothRep.{0, u, uV} ℂ M_I(F)` with nonzero carrier (`[Nontrivial σ]`) and every character
`c` of the center of `M_I(F)` with `σ.HasCentralCharacter c`, the set
`regularUnitaryTwists i ν I σ` is dense in the topological group of unitary unramified
characters of `M_I(F)`.

**Provenance.** Derived. The published `RegularUnitaryTwistExistenceStatement` (module
`ParabolicRegularUnitaryTwist`, proved by `regularUnitaryTwistExistence`), in the context of a
`ParabolicRootPresentation`, asserts that some regular unitary twist exists, under the same
hypotheses on `σ` (nontrivial, with a central character). Its proof follows the separation of
central characters in the proof of the Theorem of VI.8.5 in Renard
(`renard-2026-representations-groupes-reductifs-padiques`, printed p.194): for every unitary
unramified `ψ` outside a Zariski-closed subset of the real variety `Im X(M)`, the central
characters of `σ ⊗ ψ` and of `w(σ ⊗ ψ)` differ for every nontrivial `w ∈ W(M, M)/W_M` (from the
faithful action of `W(M, M)/W_M ≃ W(A)` on `𝔞*`). The density statement is the topological form
of this: the exceptional set is contained in a finite union of zero sets of nonzero regular
functions, whose complement is dense in the compact torus of unitary unramified characters. Waldspurger uses the regular points of the orbit in IV.3 (printed p.285) and states
V.1.1 at them.

## The identity at the regular points

**Definition `WeightedWeakExpansionRegularIdentityStatement`.** It has exactly the explicit
arguments of `WeightedWeakExpansionDenseIdentityStatement`,
`hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq hRefl hCST PG hA R PM`, with the same section
variables, and the finite type structure on the Weyl indices given by `finite_weylIndex`. Body:
if `I'` is proper, `IsSpecialVertexCompact ν hi K`, `LiftsInCompact R` and
`hN : SourceCompactNormalization …` hold, then for every section `q`, every family of extensions
`E s : WeightedCExtension … (hN s)`, every family of lower sections `Ψ s : LowerSections … s` with
`IsWeightedCSection … (hN s) (E s) q (Ψ s)` for all `s`, every `m' ∈ M'(F)` and every
`χ ∈ regularUnitaryTwists i ν I π.obj`, the orbit point
`ω = discreteSeriesOrbitMap CM hCM mu νM (discreteSeriesClass CM hCM mu π hsq) χ`, the class of
`π ⊗ χ`, lies in the set

`{ω ∈ O | Wπ(ω) · rationalOrbitWeakConstantTerm … q ω (leviRationalPointHomeomorph i ν I' m')
  = Σ_s lowerPlancherelWeight … (PM s) (sω) ·
      DynamicInducedOrbit.inducedOrbitCoefficientMap … (Ψ s) (sω) m'}`

(`sω = lowerOrbitMap … ω`), the set of `WeightedWeakExpansionDenseIdentityStatement`, written
with the same expressions. So the statement is the weighted identity at `ω`.

**Meaning and provenance.** Derived from Waldspurger, Proposition V.1.1 and its proof (printed
pp.289–292): at a `G`-regular `ω`,
`(E^G_P ψ)^{w,Ind}_{P'} = Σ_s E^{P'}_{M'∩s·P}(c_{P'|P}(s, ω)ψ)`, and the operator
`c_{P'|P}(s, ·)` is regular at the `G`-regular points of `O` (printed p.289, from IV.2.2). The
weighted family of Corollary V.2.3 (printed p.294) is `c̃_{P'|P}(s, ·) = µ^G µ^{M'}(s·)⁻¹
c_{P'|P}(s, ·)` as a rational function, so `µ^{M'}(s·) c̃_{P'|P}(s, ·) = µ^G c_{P'|P}(s, ·)`; both
sides are regular at a `G`-regular unitary point (`c̃` is regular on `O` by V.2.3, and the
densities are regular at unitary points), so the values agree there. Multiplying V.1.1 by
`µ^G(ω)` then gives the weighted identity at every `G`-regular `ω`, including the points where
`µ^G(ω)` or `µ^{M'}(sω)` vanishes; no nonvanishing condition is part of the statement. The
statement is the restriction of `WeightedWeakExpansionIdentityStatement` (module
`RationalWeakExpansionIdentityInputs`) to the regular orbit points.

## The proved results

**Theorem `dense_orbitMap_image`.** For a dense set `X` of unitary unramified characters of
`M_I(F)`, the image of `X` under the orbit map
`discreteSeriesOrbitMap CM hCM mu νM (discreteSeriesClass CM hCM mu π hsq)` is dense in `O`.
Proof: the orbit map is an open quotient map (the published
`isOpenQuotientMap_discreteSeriesOrbitMap`), hence surjective, so its range is dense; it is
continuous (`continuous_discreteSeriesOrbitMap`); Mathlib's `DenseRange.dense_image` concludes.

**Theorem `weightedWeakExpansionDenseIdentity_of_regular`.** Hypotheses:
`RegularUnitaryTwistDenseStatement i ν I` (at the universes `u`, `uV` of `π`) and
`WeightedWeakExpansionRegularIdentityStatement` for the data of the conclusion. Conclusion:
`WeightedWeakExpansionDenseIdentityStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq hRefl
hCST PG hA R PM`.

Proof as implemented. Introduce the premises, `q`, `E`, `Ψ`, the section formulas and `m'`.

1. The carrier of `π` is nontrivial: `π` is irreducible (`π.property.1`), so its module over the
   group algebra is simple (Mathlib's `Representation.irreducible_iff_isSimpleModule_asModule`),
   hence nontrivial (`IsSimpleModule.nontrivial`).
2. Square integrability `hsq` contains a `UnitaryCentralCharacter c` of `π`
   (`IsSquareIntegrableModCentralSubgroup`); its field `c.acts` is
   `π.obj.HasCentralCharacter c.character`.
3. The density hypothesis, applied to `hG hi hν`, `π.obj` and `c`, makes
   `regularUnitaryTwists i ν I π.obj` dense; `dense_orbitMap_image` makes its image under the
   orbit map dense in `O`.
4. This image is contained in the set of the dense identity statement: an element of the image
   is the orbit point of some `χ ∈ regularUnitaryTwists i ν I π.obj`, and the regular identity
   hypothesis, applied to the premises, `q`, `E`, `Ψ`, the section formulas, `m'` and `χ`, puts it
   in the set. The two sets were elaborated in different modules and differ only in
   automatically generated auxiliary proof constants, so the final step closes at reducible
   transparency. `Dense.mono` concludes.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, registered as `waldspurger-2003-plancherel`, PDF SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7` (PDF page = printed page −
234): regularity, printed p.276; IV.3, printed p.285; Proposition V.1.1 and its proof, printed
pp.289–292; Corollary V.2.3, printed p.294; the weighted identity in the proof of VI.3.1, printed
p.304.

D. Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026,
registered as `renard-2026-representations-groupes-reductifs-padiques`, PDF SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`: proof of the Theorem of
VI.8.5, printed p.194.
