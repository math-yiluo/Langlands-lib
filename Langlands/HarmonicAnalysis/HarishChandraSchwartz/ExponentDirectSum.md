# The decomposition `V = ⊕_{χ ∈ 𝓔xp(π)} V_χ` (Waldspurger I.3)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ExponentDirectSum`, namespace
`Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ExponentDecomposition` (Worker 249):
  `jointGenEigenspace T χ` (the simultaneous generalized eigenspace
  `⨅ a, (T a).maxGenEigenspace (χ a)`), `mem_jointGenEigenspace`, `commute_jointFamily`,
  `map_one_of_mem_jointGenEigenspace`, `map_mul_of_mem_jointGenEigenspace` and
  `exists_sum_mem_jointGenEigenspace` (a vector of a finite-dimensional `T`-stable subspace `W`
  is a finite sum of elements of the `W ⊓ Y_χ`);
- `Langlands.Representation.Smooth.FixedVectors.OrderProof`: `fixedVectors_antitone`, and
  through its imports `fixedVectors`, `IsSmoothVector` and `IsAdmissible`
  (`Langlands.Representation.Smooth.Definitions`: smooth, and the vectors fixed by every open
  subgroup form a finitely generated module);
- Mathlib: `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo`,
  `Module.End.mapsTo_maxGenEigenspace_of_comm`,
  `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`, `iSupIndep.disjoint_biSup`,
  `Module.End.pow_restrict`, `Module.End.ker_pow_le_ker_pow_finrank`,
  `Submodule.fg_iff_finiteDimensional`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234.

I.3, printed p. 243 (PDF p. 9; the calligraphic `𝓔` was checked on the rendered page): "Soit
`(π, V)` une représentation admissible de `G`. Pour `χ ∈ Hom(A_G, ℂ^*)`, posons
`V_χ = {v ∈ V; ∃d ∈ ℕ, ∀a ∈ A_G, (π(a) − χ(a))^d v = 0}`. On appelle exposant de `π` un
caractère `χ` tel que `V_χ ≠ 0`. On note `𝓔xp(π)` l'ensemble de ces exposants. On a l'égalité
`V = ⊕_{χ ∈ 𝓔xp(π)} V_χ`."

The source gives no proof. The proof route below (local finiteness from admissibility,
independence of simultaneous generalized eigenspaces) is internal to this project. The
finiteness of `𝓔xp(π)` for finitely generated `π` is a derived statement, not displayed in I.3.

## Relation to the source

- `A` is a commutative group with `j : A →* G` central (`hj : ∀ a g, j a * g = g * j a`); for
  the source, `A = A_G` and `j` the inclusion. The action is `T = ρ.comp j`, i.e.
  `T a = π(j a)`.
- `jointGenEigenspace T χ` is defined for every function `χ : A → ℂ` with the condition
  "`∀ a, ∃ k`"; `mem_jointGenEigenspace_iff_exists_pow_of_isAdmissible` shows that for an
  admissible `ρ` it is the source's `V_χ` with "`∃ d, ∀ a`". The exponents are the `χ` with
  `V_χ ≠ 0` (`exponentSet`); they are characters
  (`map_one_and_map_mul_of_mem_exponentSet`), as in the source's `χ ∈ Hom(A_G, ℂ^*)`.
- `V = ⊕_{χ ∈ 𝓔xp(π)} V_χ` is `DirectSum.IsInternal (jointGenEigenspace (ρ.comp j))` (the
  family over all `χ`; the summands with `χ ∉ exponentSet` are zero, and
  `biSup_exponentSet_eq_iSup` restates the span over `exponentSet`).
- `G` is any group with a topology; `IsAdmissible` is the Library's definition (smooth, and
  `fixedVectors ρ K` finitely generated for every open subgroup `K`).

## Contents

### Abstract statements

`A` is a commutative group, `Y` a complex vector space and `T : A →* Module.End ℂ Y`.

- `exponentSet T` (definition): `{χ : A → ℂ | jointGenEigenspace T χ ≠ ⊥}`.
- `iSupIndep_jointGenEigenspace T`: `iSupIndep (jointGenEigenspace T)`.
- `mapsTo_jointGenEigenspace_of_commute T hg χ hy`: for `g : Module.End ℂ Y` with
  `hg : ∀ a, Commute (T a) g` and `hy : y ∈ jointGenEigenspace T χ`:
  `g y ∈ jointGenEigenspace T χ`.
- `mem_jointGenEigenspace_iff_exists_pow T W hW hy`: for a submodule `W` with
  `[FiniteDimensional ℂ W]`, `hW : ∀ a, ∀ x ∈ W, T a x ∈ W` and `hy : y ∈ W`:
  `y ∈ jointGenEigenspace T χ ↔ ∃ d : ℕ, ∀ a, ((T a - χ a • 1) ^ d) y = 0`.
- `iSup_jointGenEigenspace_eq_top T hloc`: for
  `hloc : ∀ y, ∃ W : Submodule ℂ Y, FiniteDimensional ℂ W ∧ (∀ a, ∀ x ∈ W, T a x ∈ W) ∧ y ∈ W`:
  `⨆ χ, jointGenEigenspace T χ = ⊤`.
- `isInternal_jointGenEigenspace T hloc` (statement with classical decidable equality on
  `A → ℂ`): under `hloc`, `DirectSum.IsInternal (jointGenEigenspace T)`.
- `biSup_exponentSet_eq_iSup T`:
  `⨆ χ ∈ exponentSet T, jointGenEigenspace T χ = ⨆ χ, jointGenEigenspace T χ`.
- `map_one_and_map_mul_of_mem_exponentSet T hχ`: for `χ ∈ exponentSet T`,
  `χ 1 = 1 ∧ ∀ a b, χ (a * b) = χ a * χ b`.
- `exponentSet_finite T W hW 𝒢 h𝒢 hgen`: for `W` with `[FiniteDimensional ℂ W]` and `hW` as
  above, a set `𝒢 : Set (Module.End ℂ Y)` with `h𝒢 : ∀ g ∈ 𝒢, ∀ a, Commute (T a) g` and
  `hgen : Submodule.span ℂ (⋃ g ∈ 𝒢, g '' W) = ⊤`: `(exponentSet T).Finite`.

### Admissible representations

`G` is a group with a topology, `V` a complex vector space, `A` a commutative group,
`ρ : Representation ℂ G V`, `j : A →* G` with `hj : ∀ a g, j a * g = g * j a`.

- `apply_mem_fixedVectors_of_central ρ j hj K a hx` (no topology needed): for a subgroup `K`
  and `x ∈ fixedVectors ρ K`, `ρ (j a) x ∈ fixedVectors ρ K`.
- `mem_jointGenEigenspace_iff_exists_pow_of_isAdmissible hρ j hj`: for `hρ : IsAdmissible ρ`,
  `v ∈ jointGenEigenspace (ρ.comp j) χ ↔ ∃ d : ℕ, ∀ a, ((ρ (j a) - χ a • 1) ^ d) v = 0`.
- `isInternal_jointGenEigenspace_of_isAdmissible hρ j hj` (**I.3**), for any
  `[DecidableEq (A → ℂ)]`: `DirectSum.IsInternal (jointGenEigenspace (ρ.comp j))`.
- `exponentSet_finite_of_isAdmissible hρ j hj S hS`: for a finite set `S : Finset V` with
  `hS : Submodule.span ℂ (⋃ g : G, ρ g '' S) = ⊤` (`ρ` finitely generated):
  `(exponentSet (ρ.comp j)).Finite`.

## Proof

`iSupIndep_jointGenEigenspace`: Mathlib's independence of simultaneous generalized eigenspaces
for a family of endomorphisms each preserving the generalized eigenspaces of the others; here
the `T a` commute (`commute_jointFamily`, `Module.End.mapsTo_maxGenEigenspace_of_comm`).
`mapsTo_jointGenEigenspace_of_commute` is the same mapping property, factor by factor of the
infimum.

`mem_jointGenEigenspace_iff_exists_pow`: for each `a`, `T a − χ(a)` restricts to `W`; its power
`k` kills `y`, hence so does its power `finrank W` (`Module.End.ker_pow_le_ker_pow_finrank`
for the restriction, `Module.End.pow_restrict`). The converse is immediate.

`iSup_jointGenEigenspace_eq_top`: every `y` lies in a finite-dimensional stable `W`, so it is a
finite sum of elements of the `Y_χ` (`exists_sum_mem_jointGenEigenspace`).
`isInternal_jointGenEigenspace` combines the two statements
(`DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`).

`biSup_exponentSet_eq_iSup`: the summands with `Y_χ = ⊥` contribute nothing.
`map_one_and_map_mul_of_mem_exponentSet`: a nonzero vector of `Y_χ` and the corresponding
results of `ExponentDecomposition`.

`exponentSet_finite`: `W` is spanned by a finite set `S`; decomposing each `s ∈ S` gives a
finite set `X` of `χ` with `W ≤ Z := ⨆_{χ ∈ X} Y_χ`. Each `g ∈ 𝒢` maps every `Y_χ` into itself,
hence `Z` into itself, so `Z` contains `g(W)` for every `g ∈ 𝒢` and `Z = ⊤` by `hgen`. For
`χ ∉ X`, `Y_χ ≤ Z` and `Y_χ` is disjoint from `Z` (`iSupIndep.disjoint_biSup`), so `Y_χ = ⊥`.

`apply_mem_fixedVectors_of_central`: `ρ(k) ρ(j a) x = ρ(j a) ρ(k) x = ρ(j a) x`.
`mem_jointGenEigenspace_iff_exists_pow_of_isAdmissible`: apply
`mem_jointGenEigenspace_iff_exists_pow` with `W = fixedVectors ρ K` for an open subgroup `K`
fixing `v` (finite-dimensional by admissibility, stable by the previous result).
`isInternal_jointGenEigenspace_of_isAdmissible`: the same `W` give `hloc`.
`exponentSet_finite_of_isAdmissible`: take `K₀ = ⋀_{s ∈ S} K_s` (`Finset.inf` of open subgroups
fixing the `s ∈ S`), `W = fixedVectors ρ K₀` (`fixedVectors_antitone`) and `𝒢` the range of
`ρ`, which commutes with `ρ(j a)` by centrality.
