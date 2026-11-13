# Irreducible smooth representations separate natural endomorphisms of fixed vectors

Author: Worker 167. Module `Langlands.Representation.Jacquet.FixedVectorIrreducibleSeparation`,
namespaces `Langlands.Jacquet.FixedVectorSeparation` and `Langlands.Jacquet`.

Main result: `fixedVectorsSeparatedByIrreducibles K hK`, for a compact open subgroup `K` of
a topological group `G : Type uG` with `G ⧸ K` countable, proves
`FixedVectorsSeparatedByIrreducibles.{uG, uV} K.toSubgroup` (defined in
`Langlands.Representation.Jacquet.CompressionSeparationBound`) for every carrier universe
`uV`: a natural family of endomorphisms of `K`-fixed vectors of smooth complex
representations that vanishes on every irreducible representation vanishes everywhere.

Provenance: internal support for the bound `b ≤ c(G, K)` of Renard 2026, VI.9.1 (printed
p.197 / PDF p.203; registered source
`renard-2026-representations-groupes-reductifs-padiques`). The argument (maximal left
ideals of the Hecke algebra give maximal subrepresentations of `ℂ[G/K]`, and the Hecke
algebra has zero Jacobson radical) is a standard one and is not Renard's route, which goes
through the families of VI.8.

## Declarations (namespace `FixedVectorSeparation`)

Write `H` for `LevelHeckeAlgebra ℂ K.toSubgroup` and `ℂ[G/K]` for the permutation
representation `permRep ℂ K.toSubgroup` on `G ⧸ K →₀ ℂ`; the `K`-fixed vectors of `ℂ[G/K]`
are definitionally the Hecke space underlying `H`.

* `avg K hK : ℂ[G/K] →ₗ H`, averaging over `K` (`Compact.averageMap`) followed by the
  identification of `K`-fixed vectors with `H`; `coeffs_avg`, and `avg_coeffs`
  (averaging fixes `H`).
* `coeffs_one`: the unit of `H` is the identity-coset vector `δ_{K}`.
* `coeffs_mul_eq_frobenius`: the coefficients of `a * b` are the Frobenius intertwiner of
  `b` applied to the coefficients of `a` (definitional).
* `avg_translate`: `avg(g · i) = avg(g · 1) * i` for `i ∈ H`. Proof: with `R` the Frobenius
  intertwiner of `i` (`R δ_K = i`, Library `frobenius_unitElement`), `g · i = R (g · δ_K)`,
  and averaging commutes with intertwiners (`Compact.averageMap_commute`).
* `coeffs_mul_mem`: a subrepresentation of `ℂ[G/K]` containing `b ∈ H` contains every
  `a * b` (Library `heckeAct_apply` writes `a * b` as a finite combination of translates
  of `b`).
* `unit_generates`: a subrepresentation containing `δ_K` is everything.
* `idealSubrep K hK I`, for a left ideal `I` of `H`: the subrepresentation
  `{v | ∀ g, avg(g · v) ∈ I}`, with `mem_idealSubrep`, and `coeffs_mem_idealSubrep`
  (`I ⊆ idealSubrep I`, by `avg_translate`).
* `isCoatom_idealSubrep`: if `I` is a maximal left ideal, `idealSubrep I` is a maximal
  subrepresentation. It is proper because `δ_K ∉ idealSubrep I` (`avg δ_K = 1 ∉ I`). If
  `U` strictly contains it, pick `x ∈ U` and `g` with `b = avg(g · x) ∉ I`; then
  `b ∈ U` (`U` is stable under translation and averaging,
  `CompactCoefficientSemisimplicity.averageMap_mem`), maximality gives
  `1 = i + c * b` with `i ∈ I`, so `δ_K ∈ U` by `coeffs_mul_mem`, and `U = ⊤`.
* `eq_zero_of_forall_mem_isCoatom_permRep` (`G ⧸ K` countable): an `x ∈ H` lying in every
  maximal subrepresentation of `ℂ[G/K]` is zero. For each maximal left ideal `I`,
  `x ∈ idealSubrep I` gives `avg x = x ∈ I`; then
  `LevelHeckeAlgebra.eq_zero_of_forall_mem_isCoatom` (module
  `Langlands.Shimura.LevelHeckeAlgebraInvolution`) applies.

## Implemented proof of `fixedVectorsSeparatedByIrreducibles`

Let `T` be natural and zero on irreducibles. Use the Library generator
`W = smallFixedVectorGenerator K` (a copy of `ℂ[G/K]` with carrier in `Type uV`, via the
equivalence `E = smallFixedVectorGeneratorEquiv K`) and its unit vector `w₀`.

1. `T W w₀ = 0`. Let `x ∈ H` correspond to `T W w₀` under `fixedVectorsEquiv E`. For a
   maximal subrepresentation `U` of `ℂ[G/K]`, let `S` be its preimage in `W` under `E⁻¹`
   and `Q = W / S` (`SmoothRep.quotient`). The composite `q = mkQ ∘ E` is surjective with
   kernel `U`, so `Q` is irreducible by `Classification.isIrreducible_iff_isCoatom_ker`.
   Naturality for `mkQ : W ⟶ Q` and `T Q = 0` give that `T W w₀` maps to zero in `Q`,
   i.e. lies in `S`; equivalently `x ∈ U`. By `eq_zero_of_forall_mem_isCoatom_permRep`,
   `x = 0`, hence `T W w₀ = 0`.
2. For any `A` and `v ∈ A^K`, the Library intertwiner
   `smallFixedVectorLift K A.representation v : W → A` sends `w₀` to `v`
   (`smallFixedVectorLift_unit`). Naturality gives `T A v = f(T W w₀) = 0`.

The countability of `G ⧸ K` is used only through the rank bound needed by the unital
separation lemma.
