# Compact induction from the norm kernel preserves supercuspidality

This module proves that the progenerator
`Π_D = ind_{⁰G(F)}^{G(F)} ρ₀` (`CuspidalSupport.rationalNormKernelSummandInduction G ρ₀`)
is supercuspidal when `π` is supercuspidal and `ρ₀` embeds in the restriction of `π`
to the common norm kernel `⁰G(F)` (`Plancherel.rationalCommonNormKernel G`).

It is an internal helper result, not a numbered statement of the book. It was written for the
Lean proof `inducedProgeneratorCenterInclusion` of the centre inclusion `ℨ_Ω ⊂ ℨ_D` (Renard
2026, VI.10.4, second Lemma, printed p. 211, PDF p. 217). Renard proves that Lemma with the
free `ℨ_D`-module structure of `R_Ω` (the first Lemma of VI.10.4) and the generic
irreducibility VI.8.5, so this module is not taken from his proof. The Lean proof applies it
with the Levi subgroup `M` in place of `G`. There it supplies the supercuspidality hypothesis of the kernel vanishing
(`CuspidalSupport/InducedKernelVanishing`), and that hypothesis is used only in one case. In
the support filtration of the geometric lemma for `r_P^G ∘ i_P^G`, a piece whose
intersection parabolic subgroup of `M` is proper consists of values in a proper Jacquet module
of `Π_D`, so supercuspidality makes it zero. The remaining pieces at double cosets `P w P`
with `w ∉ M`, where `w` normalizes `M`, need not vanish. There, maps that commute with
`End(Π_D)` are shown to be zero by a separate argument
(`CuspidalSupport/SelfIntersectionPieceVanishing`), which uses the naturality of
`fullPieceEquiv`, the twisted equivariance of the map and the absence of fixed vectors
(`Induction/OpenNormalSubgroupInduction`).

Supercuspidality is the Library predicate `IsSupercuspidal`
(Exponents/LeviSupercuspidalInductionSupport). It requires the normalized Jacquet module
`jacquetFunctor … A` to be a subsingleton for every actual rational parabolic `P` of `G`
with `P ≠ G`.

## `pointImage_radical_le_rationalCommonNormKernel`

**Statement.** For an actual rational parabolic `p : P ⟶ G` and its geometric unipotent
radical `r : U ⟶ P`, the image `U(F) = pointImage (r ≫ p)` in `G(F)` lies in `⁰G(F)`.

**Proof.** Let `n ∈ U(F)`. By `isLimitOfCompactSubgroups_pointImage_radical`
(Exponents/LeviRadicalCompactSubgroups), the compact set `{n}` lies in a compact subgroup
`K` of `U(F)`. Its image in `G(F)` is compact, since the inclusion is continuous. Every
compact subgroup of `G(F)` lies in `⁰G(F)` by
`Plancherel.compactSubgroup_le_rationalCommonNormKernel`. Hence `n ∈ ⁰G(F)`.

## `isSupercuspidal_rationalNormKernelSummandInduction`

**Statement.** Let `π` be a smooth representation of `G(F)` with `IsSupercuspidal π`. Let
`ρ₀` be a smooth representation of `⁰G(F)`, and `j : ρ₀ ⟶ π|_{⁰G(F)}` an injective
morphism. Then `IsSupercuspidal (rationalNormKernelSummandInduction G ρ₀)`.

**Proof.** Fix a proper actual rational parabolic `P = MU` and write
`U(F) = pointImage (r ≫ p)`.

1. Since `IsSupercuspidal π` holds, the Jacquet module of `π` is a subsingleton. So
   every `w` maps to `0` under `Jacquet.Localization.mk`. By `mk_eq_zero`, every vector
   of `π` lies in the `U(F)`-coinvariant relations of `π`.
2. Let `Π₁ = rationalNormKernelCompactInduction G π`, which is
   `compactInduced ⁰G(F) (π|_{⁰G(F)})`. The subgroup `⁰G(F)` is open
   (`Plancherel.isOpen_rationalCommonNormKernel`) and normal, the restriction of `π` is
   smooth, and `U(F) ≤ ⁰G(F)` by the lemma above. So
   `Induction.compactInduced_restrict_mem_relations`
   (Induction/OpenNormalSubgroupInduction) puts every vector of `Π₁` in the
   `U(F)`-coinvariant relations. By `mk_surjective` and `mk_eq_zero`, the Jacquet module
   of `Π₁` is a subsingleton.
3. The compact induction of `j`,
   `CuspidalSupport.rationalSummandInductionToUniversal G π ρ₀ j : Π_D ⟶ Π₁`, is
   injective (`rationalSummandInductionToUniversal_injective`). The normalized Jacquet
   functor preserves injective maps when `U(F)` is a limit of compact subgroups
   (`normalizedJacquetFunctor_map_injective`, Aubert/General/DirectedUnions;
   `isLimitOfCompactSubgroups_pointImage_radical`). So the Jacquet module of `Π_D`
   injects into a subsingleton, and is therefore a subsingleton.
