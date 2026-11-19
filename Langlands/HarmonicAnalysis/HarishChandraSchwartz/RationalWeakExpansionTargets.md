# Targets: the weighted weak-constant-term expansion (Waldspurger V.1.1, V.2.3)

Author: Worker 131, task `b2eba110-082e-4b07-9076-f64b90cd0dc3` (Task 7454, revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionTargets`,
namespace `Langlands.HarishChandraSchwartz.WeakExpansion`.

## Purpose

This module states the four targets of Task 7454 as named Prop-valued definitions:

- `WeightedCRegularityStatement` (Corollary V.2.3);
- `WeightedWeakExpansionStatement` (Proposition V.1.1, in the weighted form used on p.304);
- `WeightedCDecompositionStatement` (the finite decomposition of p.304 into smooth multiples of
  specializations of fixed polynomial (algebraic) lower families);
- `WeightedPacketIdentityStatement` (the packet identity of pp.303–304).

It proves none of them. The definitions they use are in the earlier Task 7454 units:
`RationalWeakExpansionWeyl` and `RationalWeakExpansionLowerGeometry` (`W(M'|G|M)`,
representatives, `s·M`, `M' ∩ s·P`), `RationalWeakExpansionAuxiliaryParabolics`,
`DynamicCommonLeviSquaredModulus`, `DynamicInducedOrbitWavePacket` (sections, coefficients and
wave packets for the dynamic parabolic of a cocharacter), `DynamicOrbitPlancherelWeight` and
`RationalWeakExpansionLowerOrbit` (`sπ`, `sO`, `µ^{M'}`, `χ ↦ sχ`), `RationalWeakExpansionCFamily`
(`c` and `c̃`), and Task 7452 (`rationalOrbitWeakConstantTerm`).

## Data (the common hypotheses of the targets)

- `F`, a nonarchimedean local field of any characteristic (universe `u`); carrier universe `uV`
  independent of `u`. `G` connected reductive (`hG`), not necessarily split or quasisplit;
  `i` a maximal split torus (`hi`), `ν` generic (`hν`).
- `I, I'` finite sets of simple roots; `ζ` (`hζ`) and `ζ'` (`hζ'`) standard cocharacters of `I`
  and `I'`. Properness of `I'` is the hypothesis `∃ α, α ∉ I'` of each target.
- The data of `rationalInducedOrbitCoefficientMap` and of Task 7452: `K`, `hKc`, `hPK` (Iwasawa
  pair for `P_∅`), `π` irreducible admissible on `M_I(F)`, with
  `C_M = rationalLeviSplitCenter I sc` for a split component `sc` (`hs`, `hindex`) and a Haar
  measure `μ` on `M_I(F)/C_M`, exactly as in the published VI.3.1 targets
  (`StandardLeviPlancherelWavePacketSchwartz`). `hA` is the compatible split component of `M'`
  used by the weak constant term of Task 7452.
- **Square integrability of `π` modulo `C_M = A_M(F)` is a premise of all four targets**, as in
  the source, where V.1 (printed p.287) starts from "`(ω_0, E_0) ∈ E_2(M)`" and Corollary V.2.3 and
  the decomposition of p.304 keep this base point. In `WeightedWeakExpansionStatement` and
  `WeightedPacketIdentityStatement` it is the argument `hsq`, which their bodies use (the orbit
  `O`, the weight `µ^G`, the weak constant term and the lower orbit data depend on it). The
  bodies of `WeightedCRegularityStatement` and `WeightedCDecompositionStatement` do not depend on
  it, so there it is the explicit first premise
  `IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu →`, so that it appears
  in their elaborated signatures.
- **`K` is the special maximal compact subgroup of the source** (`IsSpecialVertexCompact ν hi K`,
  a premise of all four targets after the properness premise); see the section "The special
  maximal compact subgroup `K`" below.
- `µ^G`: all hypotheses of the published `standardLeviPlancherelWeight`, bundled in
  `PG : DensityPackage i ζ hRefl hCST hG (π ∘ e)` (its fields are literally those hypotheses), with
  the two global statements `hRefl` and `hCST`. The weight `Wπ` in the targets is
  `standardLeviPlancherelWeight` applied to the fields of `PG`.
- `R : Representatives`, the representative system of `W(M'|G|M)` (Worker 614), and for each `s`
  an explicit lower density package `PM s : LowerDensityPackage` for `M'`, `s·M`, `sπ`. The data of
  `µ^G` do not supply these packages (see `RationalWeakExpansionLowerOrbit`).

No other premise is used. In particular no target assumes regularity of a c-family, an expansion,
a decomposition, a packet identity, a `Ξ` bound, Lemmas VI.2.1–VI.2.3 or the II.1.1 bound.
`IsSpecialVertexCompact` is a property of the fixed compact subgroup only (existence of an
apartment and a special vertex for it); it says nothing about c-families, constant terms or
packets.

`LiftsInCompact R` (a hypothesis of the two identities) says that every normalizer lift
`R.normalizer s` lies in `K`. In the source the representatives of Weyl elements are taken in the
fixed special maximal compact subgroup; see "Representatives" below for why the identities are
false for arbitrary lifts. `SourceCompactNormalization` (a hypothesis of all four targets) says
that for every `s` the condition `CommonCompactNormalization` of `RationalWeakExpansionCFamily`
holds: `PG.K = K` and `(PM s).K = leviSchemeCompact K`, i.e. `µ^G` is formed with `K` and every
`µ^{M'}` with `K ∩ M'(F)` read on the Levi scheme. In the source (I.1, printed p.240) one special
maximal compact `K` normalizes every measure and pairing ("mes(H ∩ K) = 1" for every closed
subgroup `H`), and `E^{M'}` is formed with `K ∩ M'`. This is a normalization of the data, not an
analytic statement; the other data of the packages stay independent. The weighted c-family is
only defined under it (`cWeightedCompactFamily`), because with unrelated compact subgroups its
values differ from the source's by a constant.

## Rational extensions and lower sections (new definitions)

- `WeightedCExtension` (structure), for data satisfying `hN : CommonCompactNormalization` (needed
  by the weighted c-family). Let `D₀ = cWeightedDomain` be the fixed domain of the
  weighted c-family (joint convergence of both integrals, regularity of both densities, nonzero
  value of `µ^{M'}`; module `RationalWeakExpansionCFamily`) and `D₀°` its interior. The fields are:
  `interior_nonempty : D₀° ≠ ∅`; a regular denominator `d` (an element of the published
  `unramifiedRegularFunctions` of `X(M_I)`); a global numerator `N(z)`, a linear map between the
  compact pictures for every `z ∈ X(M_I)`, polynomial in `z` (published
  `IsPolynomialOperatorOn Set.univ`); `clears : N(z) = d(z) c̃(s, π ⊗ z)` on the compact pictures for
  every `z ∈ D₀°`; and `unitary_regular : d(z) ≠ 0` for every unitary `z`.
  `WeightedCExtension.unitaryValue E z = d(z)⁻¹ N(z)` is the value at a unitary `z`.
  `weightedCompactFamily` is `cWeightedCompactFamily` with the lower compact open subgroup `lowerK`.
- `sectionCompactPicture q z`: the compact picture of `q_{π⊗z}` (the published
  `productInducedFamilyRestriction` of the parameter pullback).
- `dynamicSectionCompactPicture`: the same for a section of `C^∞(O, P(χ))` of
  `DynamicInducedOrbitWavePacket`, in its circle coordinates.
- `LowerSectionsAt` / `LowerSections s`: the lower smooth sections `C^∞(sO, M' ∩ s·P)`, i.e.
  `inducedSmoothOrbitSections` for `H = M'`, the lower cocharacter `χ_s`, `sπ` and `lowerK`.
- `lowerK`, `lowerK_isCompact`, `lowerPackage_iwasawa`: the compact open subgroup of the lower
  package and its Iwasawa decomposition for `M' ∩ s·P`, read in `M'(F)`.
- `IsWeightedCSection E q Ψ`: `Ψ` is the lower section `sω ↦ c̃_{P'|P}(s, ω) q_ω`, i.e. for every
  unitary `z`, the compact picture of `Ψ` at `sz` is `E.unitaryValue z` applied to the compact
  picture of `q` at `z`.

**Why an existential extension.** At unitary points the integrals defining `c` usually diverge;
`c̃(s, ω)` for `ω ∈ O` exists only through rational continuation. The targets therefore assert
the existence of a continuation `E` that is regular on `O`, and use its values. Using `∀ E`
instead would make the targets vacuous if no continuation existed.

**Uniqueness (proved: `WeightedCExtension.unitaryValue_eq`).** Two extensions `E = (N, d)` and
`E' = (N', d')` have the same value at every unitary `z`. All extensions refer to the same open set
`D₀°`, on which `N = d c̃` and `N' = d' c̃`, so `d' N = d d' c̃ = d N'` on `D₀°`. The difference
`d' N − d N'` is a polynomial family (applied to each fixed vector) that vanishes on the nonempty
open set `D₀°`, hence vanishes identically (`leviPolynomial_eq_zero_of_isOpen`, below). At a
unitary `z` both `d(z)` and `d'(z)` are nonzero, so `d(z)⁻¹ N(z) = d'(z)⁻¹ N'(z)`
(`leviRationalContinuation_value_eq`). The comparison is between `d' N` and `d N'`, not between the
numerators: `(2N, 2d)` is an extension with the same values. So the values used are those of the
unique rational function `c̃(s, ·)`; the existential only expresses its regularity on `O`.

**Faithfulness of the fields.** In the source `c̃(s, ·)` is a rational function (V.1, printed
p.288, after IV.1) that coincides with the convergent integrals, multiplied by the density
quotient, where these are defined. The field `clears` on all of `D₀°` expresses this coincidence on
the interior of the domain; it is part of what the regularity target asserts, not a premise.
`clears` does not require `d ≠ 0` on `D₀°`. A single denominator for all of `O` is no restriction: if `b_1, …, b_r` are admissible denominators
with no common zero on `O`, then `Σ b_j b_j^*` (with `b^*(z) = conj b(z̄⁻¹)`) is an admissible
denominator that is positive on `O`.

**Identity theorem (proved).** `leviPolynomial_eq_zero_of_isOpen`: a polynomial family of vectors
on `X(M_I)` that vanishes on a nonempty open set vanishes identically. Proof: transport along the
published `unramifiedCharactersHomeomorph` of `leviRationalPointHomeomorph` (the characters of the
literal subgroup `M_I(F)` and of the Levi scheme) with `isPolynomialOn_transport_iff`, then apply
the published `rationalUnramifiedPolynomial_eq_zero_of_isOpen` for the connected reductive Levi
scheme of `I` (`lowerAmbient_isConnectedReductive`).

## The targets

1. `WeightedCRegularityStatement`: if `π` is square integrable modulo `C_M`, `I'` is proper,
   `IsSpecialVertexCompact ν hi K` and `SourceCompactNormalization` hold, then for every `s`,
   `Nonempty (WeightedCExtension … s)`.
   Source, Corollary V.2.3 (printed p.294): "l'application `ω ↦ µ^G(ω)µ^{M'}(sω)^{-1}c_{P'|P}(s,
   ω)` est rationnelle et régulière sur `O`." The definition of "rationnel et régulier sur `O`" is
   that of V.1, printed p.288: "on peut prolonger `A` en un opérateur rationnel sur un ouvert de
   `O_C` contenant `O`". Here the extension agrees with `c̃` on the interior of its convergence
   domain `D₀`, so it is the continuation of the actual integrals.
2. `WeightedWeakExpansionStatement` (for `π` square integrable, argument `hsq`): if `I'` is
   proper and `IsSpecialVertexCompact ν hi K`, `LiftsInCompact R` and `SourceCompactNormalization`
   hold, then for every `q` there are extensions `E_s` and lower sections
   `Ψ_s` with `IsWeightedCSection`, such that for **every** `ω ∈ O` and `m' ∈ M'(F)`
   `Wπ(ω) · (f_ω)^w_{P'}(m') = Σ_s µ^{M'}(sω) · (E^{M'}_{M'∩s·P} Ψ_{s,sω})(m')`.
   Here `(f_ω)^w_{P'}` is `rationalOrbitWeakConstantTerm` of Task 7452, `µ^{M'}` is
   `lowerPlancherelWeight (PM s)`, `sω = lowerOrbitMap ω`, and the coefficient is
   `inducedOrbitCoefficientMap` of `DynamicInducedOrbitWavePacket`. Source, printed p.304:
   "pour tout `m' ∈ M'` et tout `χ ∈ Im X(M)`, on ait l'égalité `µ(ω⊗χ)(E^G_P sp_χ ψ)^w_{P'}(m') =
   Σ_s µ^{M'}(s(ω⊗χ))(E^{M'}_{M'∩s·P} sp_χ c̃_{P'|P}(s)ψ)(m')`", obtained there from Proposition
   V.1.1 (printed p.289), which is stated for G-regular `ω`, and Corollary V.2.3. The target holds
   at every orbit point, as on p.304.
3. `WeightedCDecompositionStatement`: if `π` is square integrable modulo `C_M`, `I'` is proper,
   and `IsSpecialVertexCompact ν hi K` and `SourceCompactNormalization` hold, then for every `q`
   and `s` there are an extension `E`, a number `N`, families
   `ψ'_k : X(s·M) → (lower compact picture)` for `k < N`, where `X(s·M)` is the group of complex
   unramified characters `unramifiedCharacters (leviNormCharacters χ_s)`, and functions `φ_k` on
   `Im X(s·M)`, such that
   - every `ψ'_k` is **polynomial** on all of `X(s·M)` (published
     `UnramifiedOperatorFamily.IsPolynomialOn Set.univ`: `ψ'_k(y) = Σ_i b_i(y) v_i` for finitely
     many fixed vectors `v_i` and elements `b_i` of `unramifiedRegularFunctions`, the algebra
     generated by the evaluations `y ↦ y(m)`);
   - every `φ_k` is smooth in the circle coordinates of `Im X(s·M)` (`IsSmoothFiniteTorusFunction`);
   - for every unitary `z ∈ Im X(M_I)`:
     `E.unitaryValue z (q_{π⊗z}|_{K×K}) = Σ_k φ_k(sz) • ψ'_k(sz)`, where `sz` is
     `lowerCharacterConjugation … z` and `ψ'_k(sz)` its value at the underlying complex character.

   The lower compact picture is the fixed space
   `ProductInducedCompactPicture (decomposition χ_s) (lowerK …) (sπ)` of `I^{M'}_{M'∩s·P}(sπ)` on
   `K' × K'`, `K' = K ∩ M'(F)`; the base point is `ω_0 = π`, and the families and the functions
   depend only on `q`, `s` and `π`; no scalar weight enters.

   Source, printed p.297 (proof of VI.2.1, "comme en IV.1"): "notons `B` l'algèbre des polynômes
   sur `X(M)`, fixons `(ω, E) ∈ O` et introduisons la `B`-famille algébrique `(ω_B, E_B)`", with
   `L(ω_B, P) = I^{G×G}_{P×P}(E_B ⊗ Ě_B)` and the specializations `sp_χ : L(ω_B, P) → L(ω ⊗ χ, P)`.
   Printed p.304: "choisissons des ensembles finis `F_s ⊂ L^{M'}(sω_B, M'∩ s·P)` et pour tout
   `ψ' ∈ F_s`, `ϕ_{ψ'} ∈ C^∞(Im X(s·M))` de sorte que pour tout `χ ∈ Im X(M)`,
   `sp_χ c̃_{P'|P}(s)ψ = Σ_{ψ'∈F_s} ϕ_{ψ'}(sχ) sp_{sχ} ψ'`."

   **Why polynomial families.** The source's factors are specializations `sp_{sχ} ψ'` of fixed
   elements `ψ'` of the algebraic family `L^{M'}(sω_B, M' ∩ s·P)`. Unramified characters are
   trivial on compact subgroups, in particular on `s·M ∩ K'`, so restriction to `K' × K'` identifies `L^{M'}(sω_B, ·)` with `B_s ⊗`
   (the fixed compact picture), `B_s` the regular functions on `X(s·M)`, and `sp_y` with evaluation
   at `y`. The compact pictures of elements of `L^{M'}(sω_B, ·)` are therefore exactly the
   polynomial families `y ↦ Σ_i b_i(y) v_i` of the Lean statement, and `ψ'_k(sz)` is
   `sp_{sz} ψ'_k`. Like the source's `ψ'`, the `ψ'_k` are families on all of `X(s·M)`, not
   sections over `sO`: no covariance under the stabilizer of `sπ` is required.

   **Deviation from the contract wording.** The task contract describes the factors as "fixed
   lower smooth sections `ψ'` over `sO`" and says that "This is the source's
   `sp_χ c̃(s)ψ = Σ_{ψ'} φ_{ψ'}(sχ) sp_{sχ}ψ'`". The review of `eedee470` showed that with smooth
   sections the statement is trivial (a singleton with `φ = 1` works as soon as `sω ↦ c̃(s, ω)q_ω`
   is itself a smooth lower section). The target follows the source formula that the contract
   cites, with the factors specializations of fixed algebraic families.

   **Expected proof (not formalized).** Given an extension `E = (N, d)` from the regularity target,
   `E.unitaryValue z = d(z)⁻¹ N(z)` with `d` nonvanishing on the unitary characters. The compact
   picture of `q` is a finite sum `Σ_j a_j(z) v_j` with smooth `a_j` (p.296:
   `C^∞(O, P) ≅ [C^∞(Im X(M)) ⊗ L_K(ω, P)]^{Stab}`), and each `N(z) v_j` is polynomial in `z`; since
   `z ↦ sz` is an isomorphism of complex tori `X(M_I) → X(s·M)`, one can take constant (hence
   polynomial) families `ψ'` and `φ = a_j d⁻¹ b_{ij}` after the change of variables. So the
   decomposition adds to the regularity target only the smoothness of `q`. It is stated
   separately because p.304 uses it in this form to rewrite the weak function as a sum of lower
   packets.
4. `WeightedPacketIdentityStatement` (for `π` square integrable, argument `hsq`): if `I'` is
   proper and `IsSpecialVertexCompact ν hi K`, `LiftsInCompact R` and `SourceCompactNormalization`
   hold, then for every `q` there are `E_s`, `Ψ_s` with
   `IsWeightedCSection` such that for every `m'`
   `∫_O Wπ(ω) (f_ω)^w_{P'}(m') dω = Σ_s f^{M'}_{Ψ_s}(m')`,
   where `dω` is the published orbit measure for the transported I.1 character measure
   `standardLeviUnitaryUnramifiedCharacterHaar`, and `f^{M'}_{Ψ_s}` is
   `inducedOrbitWavePacket` on `M'` with weight `µ^{M'}` and the measure
   `lowerCharacterMeasure` (the image of the same character measure under `χ ↦ sχ`). Source,
   printed p.303: `f^w_{ϕ,ψ}` is defined by replacing `(E^G_P sp_χ ψ)(g)` in the packet integral
   by `(E^G_P sp_χ ψ)^w_{P'}(m')`; p.304: "`f^w_{ϕ,ψ}(m') = Σ_s ∫_{Im X(s·M)} µ^{M'}(sω ⊗ χ)ϕ(s⁻¹χ)
   Σ_{ψ'} ϕ_{ψ'}(χ)(E^{M'}_{M'∩s·P} sp_χ ψ')(m') dχ`. Autrement dit
   `f^w_{ϕ,ψ} = Σ_s Σ_{ψ'} f^{M'}_{s(ϕ)ϕ_{ψ'},ψ'}`." As in the task, the target is the orbit
   integral of the weighted weak constant terms of `q` itself: the published packets of VI.3
   integrate `w(ω)(E q_ω)` over `O` and carry no separate function `ϕ`. By the decomposition
   target, the compact picture of `Ψ_s` at `sz` is `Σ_k φ_k(sz) ψ'_k(sz)`, which gives the source's
   double sum. The weak function is defined as an orbit integral, so no
   interchange of limits and integrals is involved.

## Why the lower packets live on `M'`, with a semistandard parabolic and a conjugated orbit

The weak constant term along `P'` is a function on `M'`, and V.1.1 expands it into coefficients of
`I^{M'}_{M'∩s·P} sω`. For `s ∈ W(M'|G|M)`, `s·M ⊂ M'` is a Levi of `M'` but `M' ∩ s·P` is in
general only semistandard in `M'`, and the representation is the conjugate `sω` of `ω`, with orbit
`sO` under `Im X(s·M)`. All lower objects are therefore built for the actual dynamic parabolic of
the lower cocharacter `χ_s` in the actual Levi scheme `M'` (the extension of the section,
coefficient and packet constructions to semistandard parabolics, item 2 of the task).

**No transport to standard data is used.** In particular Proposition V.3.1 (printed p.295, the
unitary normalized `°c_{P'|P}(s, ω)` with `E^G_{P'}(°c ψ) = E^G_P ψ`) is not used by any target.
The measures on `Im X(s·M)` are the images under `χ ↦ sχ` (`lowerCharacterMeasure`), which is
exactly the change of variables of p.304; the comparison with the intrinsic I.1 measure of
`Im X(s·M)` is not used.

## Normalizations

One compact open `K`, the special maximal compact subgroup of the source (section "The special
maximal compact subgroup `K`" below), normalizes the measures of all intertwining integrals, `γ(G|M')`
(`RationalSourceGamma`), and the coefficients `E^G_P` (compact probability on `K`). The lower
coefficients and lower compact pictures use `K ∩ M'(F)`. The densities `µ^G` and `µ^{M'}`
are the same published construction `plancherelDensity`, with constant `∏_α γ(M_α|M)²` and the
canonical scalar `j_P`, each relative to the compact subgroup of its package; under
`SourceCompactNormalization` these are `K` and `K ∩ M'(F)`; see also the Markdown of `DynamicOrbitPlancherelWeight`. The constants `c(G|M)` and
`c(M'|s·M)` enter neither the c-families nor the targets; they enter only the norm comparison of
Lemma V.2.2, below.

## The norm comparison of Lemma V.2.2

Source, I.1, printed p.241: `γ(G|M)` is the constant `γ(P)` of the decomposition of the Haar
measure of `G` along `P` with the measures normalized at `K`, and
"`c(G|M) = γ(G|M)⁻¹ ∏_{α∈Σred(P)} γ(M_α|M)`". The same definitions in `M'` give `γ(M'|s·M)` and
`c(M'|s·M)`, with the measures of `M'` normalized at `K ∩ M'(F)`.

Source, V.2, printed p.293. `L(ω, P)` carries the hermitian product
"`(v₁ ⊗ v̌₁, v₂ ⊗ v̌₂) = d(ω)⁻¹ (v₁, v₂)(v̌₁, v̌₂)`" with `(v₁, v₂) = ∫_{P\G} (v₁(g), v₂(g)) dg`, and
`I^{G×G}_{P'×P̄'} L^{M'}(sω, M' ∩ s·P)` the analogous product. "Lemme V.2.2. Soient `ω` un élément
`G`-régulier de `O`, `P ∈ P(M)`, `ψ ∈ L(ω, P)`, `P' = M'U'` un sous-groupe parabolique semi-standard
de `G` et `s ∈ W(M'|G|M)`. On a l'égalité
`c(M'|s·M)² µ^G(ω) ‖c_{P'|P}(s, ω)ψ‖² = c(G|M)² µ^{M'}(sω) ‖ψ‖²`."

The proof (printed pp.293–294) uses exactly the normalizations of this formalization:

- `‖c_{P'|P}(s, ω)(v ⊗ v̌)‖² = d(ω)⁻¹ γ(G|M')⁻² ‖J_{P_s|s·P}(sω)λ(s)v‖² ‖J_{P̃_s|s·P}(sω̌)λ(s)v̌‖²`,
  with the factor `γ(G|M')⁻¹` and the two integrals of `cMap` (module
  `RationalWeakExpansionCFamily`), all at `K`;
- `‖J_{P_s|s·P}(sω)λ(s)v‖² = x ‖v‖²` and `‖J_{P̃_s|s·P}(sω̌)λ(s)v̌‖² = y ‖v̌‖²`, where
  `J_{s·P|P_s} J_{P_s|s·P} = x id` and `J_{s·P|P̃_s} J_{P̃_s|s·P} = y id`, for the same
  `K`-normalized measures as the integrals of `cMap`; by IV.3 (2) and (4) their product is a
  product of rank-one scalars `j_α`, the factors of the canonical scalars `j` of the published
  `plancherelDensity`;
- "`xy = Π j_α(sω)`, où le produit est pris sur `Σ^G_red(s·P) − Σ^{M'}_red(M' ∩ s·P)`", and
  "`γ(G|M')⁻² xy = c(G|M)² µ^{M'}(sω) c(M'|s·M)⁻² µ^G(ω)⁻¹`". In this last identity `µ^G` and
  `µ^{M'}` are the densities `j⁻¹ ∏_α γ(M_α|M)²` of `G` and of `M'`, with the factors `γ(M_α|M)` of
  `c(G|M)` and of `c(M'|s·M)` and the scalars `j_α`, all for measures normalized at `K`, resp.
  `K ∩ M'(F)`. This is why the targets require `SourceCompactNormalization`: with unrelated
  compact subgroups for `µ^G` or `µ^{M'}` the comparison acquires a constant factor.

Lemma V.2.2 is not a separate target here. In the source it is used only in the proof of
Corollary V.2.3 (equation (1), printed p.294: the norm of `C(λ)ψ` in terms of
`µ^G(ω ⊗ χ_λ) µ^{M'}(s(ω ⊗ χ_λ))⁻¹ = Π µ_α(s(ω ⊗ χ_λ))`), whose conclusion is
`WeightedCRegularityStatement`. A proof of that target will need it; the constants `c(G|M)`,
`c(M'|s·M)` are nonzero constants and do not affect regularity.

## The special maximal compact subgroup `K`

Source, I.1, printed p.240: "On fixe un sous-groupe compact maximal `K` de `G`, dont on suppose
qu'il est le fixateur d'un point spécial de l'appartement associé à `A_0` dans l'immeuble de `G`.
On munit tout sous-groupe algébrique fermé `H` de `G` de la mesure invariante par translations à
gauche pour laquelle `mes(H ∩ K) = 1`." All the Haar measures of V.1–V.2 (the intertwining
integrals, `γ(G|M')`, `E^G_P`, `E^{M'}_{M'∩s·P}`, `µ^G`, `µ^{M'}`) are normalized at this one `K`.

**Lean definition.** `IsSpecialVertexCompact ν hi K` (section `Special`) says: there are a
centralizer datum `C` of the maximal split torus `i` and Kaletha–Prasad apartment data
`D : KPApartmentData i (localFieldOrder F)` such that

- `D.SatisfiesApartmentAxioms C` (the axioms V 6 on `Z(F)`, V 7 and AS 2–AS 5 of the Library;
  the Library does not formalize all of the corrected KP Definition 4.1.26) and
  `D.HasBoundedOpenStabilizers` (KP Axiom 4.1.2);
- there is a point `x` of the apartment with `D.IsSpecialApartmentVertex x` (a special point and
  a vertex for the affine roots of `D`);
- the actual subgroup `K_x = D.specialCompactSubgroup x = G(F)^1 ∩ Stab([x])` has the published
  `SpecialCompactProperties F i ν`: `IsBoundedOpenMaximal` (KP Theorem 4.2.15(1)),
  `IsCompactOpenMaximal` (compact, open, maximal among compact subgroups; Renard,
  Théorème V.5.1), `HasWeylRepresentatives` (every relative Weyl element has a representative in
  `K_x`) and `HasParabolicFactorization` (`K_x ∩ P_J = (K_x ∩ M_J)(K_x ∩ U_J)` for every standard
  parabolic);
- `K_x = K` as subgroups of `G(F)`.

The properties of `K_x` are required explicitly because the Library proves none of them from the
apartment data. The apartment is the one of `i`, i.e. of `A_0`, as in the source.

**Satisfiability.** These are exactly the conjuncts of the published existence target
`SpecialMaximalCompactExistence` (`Langlands.BruhatTits.SpecialCompact`), without its additional
clause about standard Levi subgroups. That target asserts, for every connected reductive `G`,
maximal split torus `i` and generic `ν`, the existence of `C`, `D` and `x` with these properties;
since `IsCompactOpenMaximal` includes openness, `K_x` is then an `OpenSubgroup` and a valid `K`.
So the premise does not make the targets vacuous (its existence is that published target, which is
not proved in the Library). The Iwasawa pair `hPK` and compactness `hKc` stay separate data,
because the sections `q` are built with them; `IwasawaExistenceStatement` is the published
existence target for `hPK`.

**Why it is needed (review of the rejected `eedee470`).** Without it the identities fail for
compact subgroups that satisfy all the other hypotheses. Take `G = SL₂(ℚ₃) × SL₂(ℚ₃)`,
`P = P' = B × B`, `M = M' = T × T`, `K₀ = SL₂(ℤ₃)²`, and let `κ` be reduction followed by
`PSL₂(𝔽₃) ≅ A₄ → A₄/V₄ = C₃`. The index-three subgroup `K = {(k₁, k₂) ∈ K₀ : κ(k₁) = κ(k₂)}` is
compact open, satisfies the Iwasawa decomposition, contains the usual Weyl lifts, and has
`K ∩ M' = K₀ ∩ M'`, so `LiftsInCompact` and `SourceCompactNormalization` can hold for it. But
`γ(G|M')` computed at `K` is three times its value at `K₀`, while the quotient intertwiners are
unchanged, so `c_K(s) = c_{K₀}(s)/3` for `s = (w, 1)`, whereas the weak constant term of a
spherical section is unchanged; the identities then hold at `K₀` and fail at `K`. Since
`K ⊊ K₀` is not maximal among compact subgroups, `IsCompactOpenMaximal K` fails, so `K` is not
`K_x` for any `x` as above, and `IsSpecialVertexCompact` excludes it.

`LiftsInCompact R` remains a separate premise of the two identities: `R` is given data, and
`HasWeylRepresentatives` only says that representatives in `K` exist, not that the chosen lifts
`R.normalizer s` lie in `K`.

## Representatives

The targets are stated for a representative system `R : Representatives` (Weyl elements
representing the `W^{M'}`-cosets, and normalizer lifts) and lower packages for `R`. Every object
of the expansion depends on the lift `n_s`, not only on its Weyl class.

- **Lifts of one Weyl element.** Two lifts differ by `a ∈ M_∅(F) = Z_G(T)(F) ⊆ M_I(F)`. Replacing
  `n_s` by `n_s a` multiplies the two factors of `c_{P'|P}(s, ω)` by `δ_P(a)^{-1/2} π(a)^{-1}` and
  `δ_P(a)^{-1/2} π̌(a)^{-1}` (normalized-induction covariance of `λ(s)`). The `π(a)` factors cancel
  in the pairing that defines the lower coefficients, but `δ_P(a)⁻¹` survives: for
  `G = GL₂`, `M = M' = T`, `s = 1`, `a = diag(ϖ, 1)` it is the residue cardinality, and the
  identities would hold for at most one of the two lifts. Hence the identities assume
  `LiftsInCompact R`, as in the source, where the representatives are taken in the special maximal
  compact subgroup `K`. For `a ∈ M_∅(F) ∩ K`, `δ_P(a) = 1`, so the summands do not depend on the
  choice of `K`-lift. Representative systems with lifts in `K` exist whenever `K` has the published
  property `HasWeylRepresentatives` (Renard, Théorème V.5.1(2)), which is one of the conjuncts of
  `IsSpecialVertexCompact`; the premise `LiftsInCompact R` says that the given system `R` is one
  of them.
- **Representatives of a coset.** Replacing `s` by `ws` with `w ∈ W^{M'}` represented by
  `m ∈ M'(F) ∩ K` conjugates all lower data by `m` inside `M'`; the lower coefficients are formed
  with the Haar probability of `K ∩ M'(F)`, which is invariant under `m`, and
  `µ^{M'}(wsω) = µ^{M'}(sω)` (Lemma V.2.1 for `M'`), so the summands are unchanged. This is the reason the source indexes the sum by `W(M'|G|M)`; it is not formalized
  here.
- `WeightedCRegularityStatement` and `WeightedCDecompositionStatement` do not assume
  `LiftsInCompact`. Each concerns the single family `c̃(s, ·)` of one lift, and its content
  (a rational continuation regular on `O`; a finite decomposition into smooth multiples of
  polynomial families) does not compare different summands. A change of lift changes `c̃(s, ·)`
  only by the nonzero constant `δ_P(a)⁻¹` and fixed invertible operators (from `π(a)⁻¹` and
  `π̌(a)⁻¹`), which preserve regularity on `O` and polynomiality of families. They do assume `IsSpecialVertexCompact`, as all
  the objects of the source are formed with that `K`.

## Status

- Imported constructions: `standardLeviPlancherelWeight`, `rationalOrbitWeakConstantTerm`
  (Task 7452), `rationalInducedSmoothOrbitSections`, `productInducedFamilyRestriction`,
  `productInducedOrbitPullback`, `unramifiedRegularFunctions`, `IsPolynomialOperatorOn`,
  `IsPolynomialOn.sub`, `unramifiedCharactersHomeomorph`, `isPolynomialOn_transport_iff`,
  `rationalUnramifiedPolynomial_eq_zero_of_isOpen`, `continuous_rationalValuationImageProjection`,
  `discreteSeriesOrbitMeasure`,
  `standardLeviUnitaryUnramifiedCharacterHaar`, `finite_standardLeviDiscreteSeriesStabilizer`,
  `rationalLeviSplitCenter`, `leviRationalPointHomeomorph`, `IsSmoothFiniteTorusFunction`,
  `finite_weylIndex`, `UnramifiedOperatorFamily.IsPolynomialOn`,
  `IsSquareIntegrableModCentralSubgroup`; for `IsSpecialVertexCompact`: `CentralizerDatum`,
  `KPApartmentData`, `localFieldOrder`, `KPApartmentData.SatisfiesApartmentAxioms`,
  `KPApartmentData.HasBoundedOpenStabilizers`, `KPApartmentData.IsSpecialApartmentVertex`,
  `KPApartmentData.specialCompactSubgroup` and `SpecialCompactProperties` (modules
  `Langlands.Geometry.Building.KPApartmentAxioms`, `Langlands.Geometry.Building.SpecialCompact`,
  `Langlands.BruhatTits.SpecialCompact.Properties`); and from the Task 7454 units listed above.
- New definitions: `WeightedCExtension`, `WeightedCExtension.unitaryValue`, `lowerK`,
  `weightedCompactFamily`, `dynamicSectionCompactPicture`, `sectionCompactPicture`,
  `LowerSectionsAt`, `IsWeightedCSection`, `LowerSections`, `SourceCompactNormalization`,
  `LiftsInCompact`, `IsSpecialVertexCompact`.
- New proved lemmas: `leviPolynomial_eq_zero_of_isOpen`, `leviRationalContinuation_value_eq`,
  `WeightedCExtension.unitaryValue_eq` (uniqueness of the unitary values), `lowerK_isCompact`,
  `lowerPackage_iwasawa` (restatements of package fields).
- New targets (unproved, for proof successors): `WeightedCRegularityStatement`,
  `WeightedWeakExpansionStatement`, `WeightedCDecompositionStatement`,
  `WeightedPacketIdentityStatement`.
- Unresolved obligations: the four targets; nonemptiness of the convergence domains is part of
  them (through `WeightedCExtension`).
- Implementation note: several declarations raise `maxHeartbeats` (to at most 3000000) because the
  types are large. No `sorry`, no new axioms.
