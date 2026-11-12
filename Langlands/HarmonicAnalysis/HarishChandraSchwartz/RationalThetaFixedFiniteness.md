# Finiteness of `Θ^H` for the standard parabolic subgroups of `G(F)` (Remark VIII.1.3)

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalThetaFixedFiniteness`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedFixedOrbits` (Library, this
  author's Unit 29): `inducedDiscreteSeriesFixedOrbits` (`Θ^H` for one parabolic `P = MU`),
  `finite_rationalInducedDiscreteSeriesFixedOrbits` (finiteness for `P_I(F)` given Theorem VIII.1.2
  for `M_I(F)`), `mk_mem_inducedDiscreteSeriesFixedOrbits_of_rationalFourierOrbitSection_ne_zero`
  and `exists_finite_rationalFourierOrbitSection_ne_zero`. Through its imports come
  `rationalFourierOrbitSection` (`ψ_f[O, P_I]`, Unit 23), `RationalSchwartzSpace`,
  `IsRationalLeviTempered`, `UnitaryOrbitRepresentative`, `DiscreteSeriesOrbitClass`,
  `discreteSeriesClass`, `Space.exists_rightInvariant` and `isSemidirectDecomposition_standard`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDiscreteSeriesOrbitFiniteness`
  (Library, this author's Unit 30): `rationalLeviSplitCenter`, `rationalLeviSplitCenter_le_center`
  and `finite_discreteSeriesFixedOrbits_standardLevi` (Theorem VIII.1.2 for `M_I(F)` from the
  published statement). Through its imports comes `RationalDiscreteSeriesOrbitFinitenessStatement`.
- `Langlands.GroupScheme.Rational.StandardCocharacterFiniteness` (Library):
  `finite_simpleRelativeRoots_of_standardCocharacter_exists`.
- `Langlands.GroupScheme.Rational.StandardCocharacterProof` (Library, proved):
  `standardCocharacter : StandardCocharacterStatement`.

From Mathlib: `Set.sigma`, `Set.mem_sigma_iff`, `Set.Finite.sigma`, `Set.finite_univ`.

## Source and provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Printed page numbers; the
PDF page is the printed page minus 234. The author checked the quotations on PDF pages 71 and 87.

- VIII.1, printed p. 321: "Soit `H` un sous-groupe ouvert compact de `G`. Pour `(O, P) ∈ Θ` et
  `(ω, E) ∈ O`, la propriété '`I_P^G E` possède des éléments non nuls invariants par `H`' ne dépend
  pas du choix de `(ω, E) ∈ O`. On note `Θ^H` l'ensemble des `(O, P)` tels que cette propriété soit
  vérifiée pour un (ou pour tout) `(ω, E) ∈ O`."
- Théorème VIII.1.2, printed p. 321: "Pour tout sous-groupe ouvert compact `H` de `G`, `Θ^H_G`
  est fini."
- Remarque VIII.1.3, printed p. 321: "Supposons le Théorème VIII.1.2 vrai pour tout sous-groupe
  de Lévi d'un sous-groupe parabolique semi-standard, resp. et propre, de `G`. Alors (i) `Θ^H`,
  resp. `Θ^H − Θ^H_G`, est fini pour tout sous-groupe ouvert compact `H` de `G`; (ii) pour tout
  `f ∈ C(G)`, l'ensemble des `(O, P) ∈ Θ`, resp. `Θ − Θ_G`, tels que `ψ_f[O, P] ≠ 0` est fini."

Here `Θ` (VI.3, printed p. 305) is the set of pairs `(O, P)` with `P = MU` a semi-standard
parabolic subgroup and `O` an orbit of `Im X(M)` in `E₂(M)`. This module treats the standard
parabolic subgroups `P_I(F)`, indexed by the finite sets `I` of simple roots, and assembles
Units 29 and 30: for each `I`, Unit 29 reduces the finiteness to Theorem VIII.1.2 for `M_I(F)`,
and Unit 30 derives the latter from the published statement for connected reductive group
schemes, applied to the Levi scheme. Pairs `(O, P_I)` are encoded as dependent pairs `⟨I, O⟩`.

## Contents

The setting of Units 19–30: `F` a nonarchimedean local field, `G` a connected reductive group
scheme over `F` (`hG`) with `[IsAffineHom G.X.hom]`, `[LocallyOfFiniteType G.X.hom]`, `i` a maximal
split torus (`hi`), `ν` a generic cocharacter (`hν`), `K` a compact open subgroup of `G(F)` with
`(P_∅(F), K)` an Iwasawa pair (`hKc`, `hPK`). For a finite set `I` of simple roots, `M_I(F)` is the
subtype `𝐌` of `G(F)` and `L = Standard.leviScheme i ν (rootSet i ν I)` the Levi scheme (local
notation `𝐋`); `a : T → L` is a split component of `L` (`ha`), `A_{M_I}(F)` is
`rationalLeviSplitCenter I a` and `μM` a Haar measure on `M_I(F) ⧸ A_{M_I}(F)`. The hypothesis
`hVIII : RationalDiscreteSeriesOrbitFinitenessStatement` is the published statement of Theorem
VIII.1.2.

### One standard parabolic (section `One`)

- **`finite_rationalInducedDiscreteSeriesFixedOrbits_of_statement hG hi hν hKc hPK I a ha μM hVIII
  H`**: for every open subgroup `H` of `G(F)`, the set `inducedDiscreteSeriesFixedOrbits … H` of
  orbits `O` of discrete series of `M_I(F)` modulo `A_{M_I}(F)` with `(O, P_I(F)) ∈ Θ^H` is finite.
- **`exists_finite_rationalFourierOrbitSection_ne_zero_of_statement … hVIII f`**: moreover `ρ`,
  `hρ`, `hKρ` (the height and the Schwartz space `C(G)`), `hM` (Iwasawa pair for `M_I(F)`),
  `[μM.IsInvInvariant]`, `hsw` (square-integrable weight on `G(F)`). For every `f ∈ C(G)` there is
  a finite set `T` of orbits such that the orbit of every discrete series `π` of `M_I(F)` modulo
  `A_{M_I}(F)` (with `hsq`, `hTA`) with `ψ_f[O_π, P_I] ≠ 0` lies in `T`.

### All standard parabolics (section `All`)

Here `T I`, `a I`, `ha I` and `mu I` depend on `I`.

- **`rationalThetaFixed hG hi hν a ha mu H`** (definition, the recorded declaration): the set
  `Set.univ.sigma (fun I => inducedDiscreteSeriesFixedOrbits … (mu I) … H)` of pairs `⟨I, O⟩`,
  that is, Waldspurger's `Θ^H` restricted to the standard parabolic subgroups `P_I(F)`.
- `mem_rationalThetaFixed I O`: `⟨I, O⟩ ∈ rationalThetaFixed … H ↔ O ∈
  inducedDiscreteSeriesFixedOrbits … H`.
- `finite_simpleRoot hG hi hν`: the set of simple roots is finite.
- **`finite_rationalThetaFixed hG hi hν hKc hPK a ha mu hVIII H`**: for every open subgroup `H`,
  `rationalThetaFixed … H` is finite (Remark VIII.1.3 (i) for the standard parabolics).
- **`exists_finite_sigma_rationalFourierOrbitSection_ne_zero_of_statement … hVIII f`**: with `ρ`,
  `hρ`, `hKρ`, `hM : ∀ I, …`, `[∀ I, (mu I).IsInvInvariant]` and `hsw` (for a measure `muG` on
  `G(F)`), for every `f ∈ C(G)` there is a finite set `T` of pairs such that `⟨I, O_π⟩ ∈ T`
  whenever `ψ_f[O_π, P_I] ≠ 0` (Remark VIII.1.3 (ii) for the standard parabolics).

## Proofs

- One parabolic: `finite_rationalInducedDiscreteSeriesFixedOrbits` and
  `exists_finite_rationalFourierOrbitSection_ne_zero` (Unit 29) with the hypothesis `hfin`
  discharged by `finite_discreteSeriesFixedOrbits_standardLevi I hVIII hG hi hν a ha μM` (Unit 30).
- `mem_rationalThetaFixed`: `simp` with `Set.mem_sigma_iff`.
- `finite_simpleRoot`: `finite_simpleRelativeRoots_of_standardCocharacter_exists` with the
  splitness of `i` and the standard cocharacters from `standardCocharacter`.
- `finite_rationalThetaFixed`: `Set.Finite.sigma` over the finite type of index sets `I`, with the
  one-parabolic finiteness for each `I`.
- Sigma version of (ii): `Space.exists_rightInvariant` gives a compact open subgroup `L` under which
  `f` is right invariant; take `T = rationalThetaFixed … L`, finite by `finite_rationalThetaFixed`;
  membership by `mem_rationalThetaFixed` and Unit 29's
  `mk_mem_inducedDiscreteSeriesFixedOrbits_of_rationalFourierOrbitSection_ne_zero`.

## Scope

- Theorem VIII.1.2 is not proved: all results are conditional on the published statement `hVIII`,
  which is open. The source's "resp." variant (Theorem VIII.1.2 only for proper Levi subgroups,
  conclusion for `Θ^H − Θ^H_G`) is available per parabolic through Unit 29's hypothesis `hfin`,
  but is not assembled over all `I` here.
- Only the standard parabolic subgroups `P_I(F)` are treated, not all semi-standard ones.
- The central subgroup of `M_I(F)` is the image of a split component of the Levi scheme.
