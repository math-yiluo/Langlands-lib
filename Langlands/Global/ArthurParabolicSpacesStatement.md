# Comparison of `𝔞_P` and `𝔞_P^*` with the relative root data

Module `Langlands.Global.ArthurParabolicSpacesStatement`, namespace
`Langlands.Global.ArthurParabolicSpaces`. The maps are those of
`Langlands.Global.ArthurParabolicSpaces`.

## Source

J. Arthur, *An introduction to the trace formula* (2005), in the volume registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (PDF page = printed page + 12), §4,
p.22; §5, pp.24–26, (5.1) and the description `𝔞_P = {H ∈ 𝔞_0 : α(H) = 0, α ∈ Δ_0^P}`.
Renard, *Représentations des groupes réductifs p-adiques* (registered as
`renard-2026-representations-groupes-reductifs-padiques`), V.3.13, printed p.112, describes
`𝔞^*_M ⊂ 𝔞^*_∅` as the annihilator of the coroots of `M` for standard Levi subgroups; the
published `StandardLeviCharacterAnnihilatorStatement` (proved) is the Levi form.

## Statement

`ParabolicSpacesComparisonStatement`: for every field `k`, connected reductive `G`
(`hG`), maximal split torus `i : T ⟶ G` (`hi`), generic cocharacter `ν`, integral reflection
data `D` and `S ⊆ Δ_0 = simpleRelativeRoots i ν`:

1. `restrictToTorus k i ν S` is injective;
2. its range is `corootAnnihilator i D S`, the real characters of `T` that vanish on the coroots
   of `S` (Renard's model of `𝔞_P^* ⊂ 𝔞_0^*`);
3. `toCharacterDual k i ν S : 𝔞_0 → Hom(X(P_S), ℝ)` is surjective;
4. its kernel is the real span of the coroots of `S` (`D.realCorootsOf S`), that is `𝔞_0^P`;
5. its restriction to `rootAnnihilator T S = {H : α(H) = 0, α ∈ S}` is bijective.

Items 1–2 say `𝔞_P^* = X(P) ⊗ ℝ ≅ corootAnnihilator i D S` (Arthur's (5.1) and its image in
`𝔞_0^*`); items 3–5 say `𝔞_P = Hom(X(P), ℝ)` is `𝔞_0 / 𝔞_0^P`, realized by the subspace
`{H ∈ 𝔞_0 : α(H) = 0, α ∈ Δ_0^P}`. Items 3–5 follow from 1–2 by duality (the maps are transposes,
`realParameterPairing_toCharacterDual`, and `V T`, `Vstar T` are perfectly paired); they are
stated for convenience.

The statement is over an arbitrary field, as the published Renard V.3 statements are; Arthur's
setting is a number field.

## Proved consequence

`bijective_restrictToTorus_empty`: the statement implies that `restrictToTorus k i ν ∅`
(`X(P_0) ⊗ ℝ → X(T) ⊗ ℝ`) is bijective, because `corootAnnihilator i D ∅` is everything. This is
the hypothesis `hρ` of the truncation operator (`Langlands.Global.ArthurTruncation`).

## Qualifications

The standard parabolic subgroups are the published closed representatives of the standard
functors. The statement does not assume their identification with actual parabolic subgroups;
it asserts the character comparison for these representatives.

## Provenance

Source: Arthur 2005, (5.1) and p.26, for standard parabolic subgroups. The formulation with the
published restriction maps, coroot annihilators and representatives is derived.
