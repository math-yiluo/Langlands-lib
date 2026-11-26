# The pointwise weighted expansion from regularity, lower sections and the identity

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionIdentityInputs`,
namespace `Langlands.HarishChandraSchwartz.WeakExpansion`.

## Purpose and contents

The target `WeightedWeakExpansionStatement` of the module `RationalWeakExpansionTargets`
(Waldspurger, Proposition V.1.1 in the weighted form used on printed p.304) asserts, under its
premises and for every section `q ∈ C^∞(O, P)`, three things at once:

1. for every Weyl index `s`, a rational extension `E_s : WeightedCExtension … s` of the weighted
   c-family `c̃_{P'|P}(s, ·)`, regular on the whole unitary orbit `O`;
2. for every `s`, a lower smooth section `Ψ_s ∈ C^∞(sO, M' ∩ s·P)` with
   `IsWeightedCSection (E s) q (Ψ s)`, that is, `Ψ_s` is the section `sω ↦ c̃_{P'|P}(s, ω) q_ω`;
3. the pointwise identity
   `µ^G(ω) (f_ω)^w_{P'}(m') = Σ_s µ^{M'}(sω) (E^{M'}_{M'∩s·P} Ψ_{s, sω})(m')`
   at every `ω ∈ O` and every `m' ∈ M'(F)`.

Item 1 is the content of the target `WeightedCRegularityBorelStatement` of the same module
(Corollary V.2.3). This module states items 2 and 3 as separate propositions and proves that the
three propositions together give `WeightedWeakExpansionStatement`:

- `WeightedCLowerSectionStatement` (item 2), a Prop-valued definition. This file does not prove it.
- `WeightedWeakExpansionIdentityStatement` (item 3), a Prop-valued definition. This file does not
  prove it.
- `weightedWeakExpansion_of_inputs` (proved): `WeightedCRegularityBorelStatement`,
  `WeightedCLowerSectionStatement` and `WeightedWeakExpansionIdentityStatement` for the same data
  imply `WeightedWeakExpansionStatement`.

## Data and binders

The module repeats the section variables of `RationalWeakExpansionTargets` and uses its local
instances (`targetsAmbientAffine`, `targetsLeviAffineHom`, `targetsLeviAffine`,
`targetsLeviFiniteType` and the canonical-scalar instances), so that its terms are those of the
targets. The data are those described in the Markdown of `RationalWeakExpansionTargets`, section
"Data": `F` a nonarchimedean local field (universe `u`) and the representation carrier universe
`uV`; `G` connected reductive (`hG`) with maximal split torus `i` (`hi`) and generic `ν` (`hν`);
the sets of simple roots `I`, `I'` with standard cocharacters `ζ`, `ζ'` (`hζ`, `hζ'`); the compact
open `K` with compactness `hKc` and Iwasawa pair `hPK`; the split component `sc` (`hs`) of the
Levi scheme of `M_I`, with rational points `C_M`; the irreducible admissible `π` of `M_I(F)`; the
Haar measure `μ` (`mu`) on `M_I(F)/C_M`; the global statements `hRefl` and `hCST`; the upper
density package `PG`; the representative system `R` of `W(M'|G|M)` and the lower density packages
`PM s`; for the identity also square integrability `hsq` of `π` modulo `C_M` and the compatible
split component `hA` of `M'`.

- `WeightedCLowerSectionStatement` takes the explicit arguments of
  `WeightedCRegularityBorelStatement`, `hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hRefl hCST PG R PM`,
  with the instance `[BorelSpace (M_I(F)/C_M)]` as an explicit binder of the definition, as in
  `WeightedCRegularityBorelStatement` (the body does not use it; the overlapping-instance linter is
  switched off for this definition only, because it also counts the omitted section instance).
- `WeightedWeakExpansionIdentityStatement` takes the explicit arguments of
  `WeightedWeakExpansionStatement`,
  `hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq hRefl hCST PG hA R PM`.

The elaborated type of `WeightedCLowerSectionStatement` coincides with that of
`WeightedCRegularityBorelStatement`, and the elaborated type of
`WeightedWeakExpansionIdentityStatement` with that of `WeightedWeakExpansionStatement`: the same
binders with the same binder kinds, in the same order, and the universe parameters `u, uV`
(compared as Lean expressions up to binder names).

## The lower-section statement

**Definition `WeightedCLowerSectionStatement`.** Body: if

- `π` is square integrable modulo `C_M` for `μ`
  (`IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu`),
- `I'` is proper (`∃ α, α ∉ I'`),
- `K` is the special maximal compact subgroup of the source (`IsSpecialVertexCompact ν hi K`), and
- `hN : SourceCompactNormalization …` (`µ^G` at `K`, every `µ^{M'}` at `K ∩ M'(F)`),

then for every Weyl index `s`, every extension `E : WeightedCExtension … (hN s)` and every section
`q : rationalInducedSmoothOrbitSections …` there is `Ψ : LowerSections … s` with
`IsWeightedCSection … (hN s) E q Ψ`.

These premises are literally those of `WeightedCRegularityBorelStatement`, and the extension type
is the one whose nonemptiness that target asserts.

**Meaning.** `IsWeightedCSection E q Ψ` prescribes, for every unitary character `z` of `M_I(F)`,
the compact picture of `Ψ` at the conjugate character `sz` (`lowerCharacterConjugation`, read in
the circle coordinates `leviUnitaryCoordinates` of `Im X(s·M)`): it is
`E.unitaryValue z (sectionCompactPicture q z)`, the value `c̃_{P'|P}(s, π ⊗ z) q_{π⊗z}` on the
compact pictures. Since `lowerCharacterConjugation` and the circle coordinates are bijections,
this prescribes the compact picture of `Ψ` at every point. In the Library the lower sections
`LowerSections … s` are `productInducedSmoothOrbitSections` for `M'`, the lower cocharacter `χ_s`
and `sπ`; by the linear equivalences `productInducedSmoothOrbitFamilyEquiv` (smooth sections and
smooth parameter families, through the parameter pullback) and `productInducedFamilyRestriction`
(restriction to the compact pictures), together with `mem_productInducedSmoothFamilies_iff`, the
statement says that the prescribed family of compact pictures is finite and scalar-smooth in the
circle coordinates of `Im X(s·M)` and is covariant under the unitary stabilizer of the class of
`sπ`.

## The identity statement

**Definition `WeightedWeakExpansionIdentityStatement`.** Body, with the finite type structure on
the Weyl indices given by `finite_weylIndex` as in the target: if `I'` is proper,
`IsSpecialVertexCompact ν hi K`, `LiftsInCompact R` (the normalizer lifts lie in `K`) and
`hN : SourceCompactNormalization …` hold, then for every section `q`, every family of extensions
`E s : WeightedCExtension … (hN s)`, every family of lower sections `Ψ s : LowerSections … s` with
`IsWeightedCSection … (hN s) (E s) q (Ψ s)` for all `s`, and every `ω ∈ O` and `m' ∈ M'(F)`:

`Wπ(ω) · rationalOrbitWeakConstantTerm … q ω (leviRationalPointHomeomorph i ν I' m')
  = Σ_s lowerPlancherelWeight … (PM s) (sω) ·
      DynamicInducedOrbit.inducedOrbitCoefficientMap … (Ψ s) (sω) m'`,

with `sω = lowerOrbitMap … ω`. The premises and the types of `q`, `E` and `Ψ` are those of
`WeightedWeakExpansionStatement`, and the identity is literally the second conjunct of its body
for these `E` and `Ψ`: compared as Lean expressions, the two differ only in the names of the
auxiliary proof constants that Lean generates in each module, whose types coincide. No other
hypothesis enters; in particular the identity is asserted at every orbit point, `G`-regular or
not.

**Universal form.** The identity is required for all extensions and lower sections satisfying the
section formula, not for chosen ones. Once one such pair exists, this is equivalent to the
existential form of the target, because the extensions enter only through the section formula
and the lower section is then determined by `q`: two extensions have the same unitary values
(`WeightedCExtension.unitaryValue_eq`), and by the bijections and linear equivalences listed in
the previous section a lower smooth section is determined by its compact pictures.

## The proved reduction

**Theorem `weightedWeakExpansion_of_inputs`.** Hypotheses: `WeightedCRegularityBorelStatement`,
`WeightedCLowerSectionStatement` and `WeightedWeakExpansionIdentityStatement` for the same data.
Conclusion: `WeightedWeakExpansionStatement` for these data.

Proof as implemented. Introduce the premises of the target (properness, special `K`, lifts in
`K`, the normalization `hN`) and the section `q`. The regularity statement, applied to `hsq`,
properness, special `K` and `hN`, gives `Nonempty (WeightedCExtension … (hN s))` for every `s`;
`Classical.choice` selects `E s`. The lower-section statement, applied to the same premises,
`E s` and `q`, gives `Ψ s` with `IsWeightedCSection (E s) q (Ψ s)`, selected with
`Exists.choose`. These are the witnesses of the target, and the section formulas are its first
conjunct. The identity statement applied to `q`, `E`, `Ψ` and the section formulas gives the
second conjunct; its type differs from the goal only in the auxiliary proof constants, so it is
closed by `with_reducible exact`. The proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Relation to the source

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, registered as
`waldspurger-2003-plancherel` (SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`); PDF page = printed
page − 234.

- **Proposition V.1.1 (printed p.289).** "Soient `ω` un élément `G`-régulier de `O` et
  `ψ ∈ L(ω, P)`. On a l'égalité `(E^G_P ψ)^{w,Ind}_{P'} = Σ_{s∈W(M'|G|M)} E^{P'}_{M'∩s·P}(c_{P'|P}(s, ω)ψ)`."
  This is the unweighted identity, at `G`-regular points only.
- **Corollary V.2.3 (printed p.294).** "l'application `ω ↦ µ^G(ω)µ^{M'}(sω)^{-1}c_{P'|P}(s, ω)`
  est rationnelle et régulière sur `O`." This is `WeightedCRegularityBorelStatement`.
- **Proof of Proposition VI.3.1 (printed pp.302–304).** On p.302 the proof fixes `(ω, E) ∈ O` and
  an element `ψ` of the algebraic family `L(ω_B, P)`. On p.304: "D'après la Proposition V.1.1 et
  le Corollaire V.2.3, pour tout `s ∈ W(M'|G|M)`, il existe une application rationnelle
  `c̃_{P'|P}(s) : L(ω_B, P) → L^{M'}(sω_B, M' ∩ s·P) ⊗_B Frac(B)` telle que `χ ↦ sp_χ c̃_{P'|P}(s)`
  soit régulière sur `Im X(M)` et telle que pour tout `m' ∈ M'` et tout `χ ∈ Im X(M)`, on ait
  l'égalité `µ(ω⊗χ)(E^G_P sp_χ ψ)^w_{P'}(m') = Σ_s µ^{M'}(s(ω⊗χ))(E^{M'}_{M'∩s·P} sp_χ c̃_{P'|P}(s)ψ)(m')`."
  The proof then chooses finite sets `F_s ⊂ L^{M'}(sω_B, M' ∩ s·P)` and functions
  `ϕ_{ψ'} ∈ C^∞(Im X(s·M))` with `sp_χ c̃_{P'|P}(s)ψ = Σ_{ψ'∈F_s} ϕ_{ψ'}(sχ) sp_{sχ} ψ'`.

The Library's statements are formulated for a smooth section `q ∈ C^∞(O, P)` (the objects of the
statement of VI.3.1, p.302) and its value `q_ω` at each orbit point, in place of the
specializations `sp_χ ψ` of a fixed `ψ ∈ L(ω_B, P)`; `c̃_{P'|P}(s, ω)` is the value at `ω` of a
rational extension `E_s`.

- `WeightedWeakExpansionIdentityStatement` is the identity of p.304, at every `ω ∈ O` and every
  `m' ∈ M'(F)`, with `Ψ_{s, sω} = c̃_{P'|P}(s, ω) q_ω` in place of `sp_χ c̃_{P'|P}(s)ψ`.
  Waldspurger derives it from V.1.1, which is stated at the `G`-regular points, and V.2.3.
- `WeightedCLowerSectionStatement` says that `sω ↦ c̃_{P'|P}(s, ω) q_ω` is a smooth section over
  the lower orbit `sO`. The source does not state this separately: on p.304 it is expressed by the
  regularity of `χ ↦ sp_χ c̃_{P'|P}(s)` on `Im X(M)` and the finite decomposition into the smooth
  functions `ϕ_{ψ'}(sχ)` times the specializations `sp_{sχ} ψ'`, which the proof uses to rewrite
  the weak function as a sum of lower wave packets.

The separation of the target into these three statements is derived from the target's own
conjunction and is not a step of the source.

## Imports

`RationalWeakExpansionTargets` (the targets, `WeightedCExtension`, `IsWeightedCSection`,
`LowerSections`, `SourceCompactNormalization`, `LiftsInCompact`, `IsSpecialVertexCompact`). The
identity statement and the reduction raise `maxHeartbeats` to 3000000, as the targets do, and the
reduction raises `maxRecDepth` to 2048, because the terms are large. No `sorry` and no new axioms.
