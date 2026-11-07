# Lifts and retractions on an open normal subgroup

Author: Worker 1709. Module
`Langlands.Representation.CompactCoefficient.RestrictedSplitting`, namespace
`Langlands.RestrictedSplitting`.

Internal helper for the proof of Renard VI.3.6 (the Proposition after the
Lemma, printed p.148 / PDF p.154, source
`renard-2026-representations-groupes-reductifs-padiques`). It supplies the
`⁰G`-equivariant sections and retractions of that proof in a generic form. The
route differs from Renard's: Renard uses semisimplicity of the restrictions of
both `π` and `τ` to `⁰G` after reducing to the block of `τ`; here only the
restriction of `τ` is used, through Clifford's theorem and the published
lifting and retraction lemmas for irreducible admissible representations with
compact coefficients. The assembly is derived; no further literature claim is
made.

## Decomposition and projections

`exists_independent_irreducible ρ H hirr hscalar`: for a complex
representation `ρ` of a group `G` (arbitrary universes), a normal subgroup `H`
with `H ⊔ center G` of finite index, `ρ` irreducible and the centre acting by
scalars, there are `m` and `W : Fin m → Subrepresentation (ρ.comp H.subtype)`
with every `(W i).toRepresentation` irreducible, the family
`fun i => (W i).toSubmodule` independent (`iSupIndep`), and supremum `⊤`. The
proof is the universe-general version of
`Cohomology.SupercuspidalRestriction.CompactModCenterProof.exists_independent_irreducible`:
it takes the finite family of atoms of
`FiniteIndexRestriction.exists_finite_atoms` for `H ⊔ center G`, transports it
to `H` by `FiniteIndexRestriction.supCenterOrderIso`, and extracts an
independent subfamily with the same supremum by the published greedy lemma
`CompactModCenterProof.exists_supIndep_subset`.

For such an independent family of subrepresentations of a representation `ρ` of
a group `H`, `proj W hind htop k : V →ₗ[ℂ] (W k).toSubmodule` is the projection
onto `W k` along `⨆ j ≠ k, W j` (`Submodule.projectionOnto`, using
`isCompl_iSup_ne`). Proved: `proj_of_mem`, `proj_of_mem_ne`, `sum_proj`
(`∑ k, proj k x = x`) and `proj_apply` (`proj k (ρ h x) = (W k).toRepresentation h
(proj k x)`). These are universe-general copies of the published projections
in `CompactModCenterProof`.

## Splitting statements

Here `G` is a topological group with `[NonarchimedeanGroup G] [T2Space G]
[LocallyCompactSpace G]`, `H : OpenSubgroup G` with `H.toSubgroup` normal and
`(H.toSubgroup ⊔ center G).FiniteIndex`, and `τ : SmoothRep.{0, uG, uV} ℂ G` is
irreducible, the centre acts on it by scalars, and the restriction
`SmoothRep.restrictSubgroup H.toSubgroup τ` has compactly supported smooth-dual
coefficients (`HasCompactSmoothDualCoefficients`).

- `compact_cofinal H K`: every open subgroup `K` of `H` contains a compact open
  subgroup, from `Hecke.TestFunction.commonCompactOpenBiInvariance` for `H`
  (locally compact since open in `G`).
- `exists_restricted_lift`: for smooth representations `σ`, `ξ` of `G`, a
  surjective intertwiner `p : σ → ξ` and an intertwiner `φ : τ → ξ`, there is a
  linear map `l : τ → σ` with `IsEquivariantOn τ.representation σ H l` and
  `p (l v) = φ v` for all `v`.
  Proof: with the decomposition above, each summand `W k` is smooth, has
  compact coefficients (`hasCompactSmoothDualCoefficients_subrepresentation`)
  and is admissible (`CompactSplitting.isAdmissible_of_compactCoefficients`,
  for the Haar measure on `H`). `CompactSplitting.exists_lift`, applied on `H`,
  lifts `φ` restricted to `W k` along `p` to an `H`-intertwiner `t k`. Then
  `l := ∑ k, t k ∘ proj k` is `H`-equivariant by `proj_apply` and satisfies
  `p ∘ l = φ` by `sum_proj`.
- `exists_restricted_retraction`: for a smooth representation `σ` of `G` and an
  injective intertwiner `j : τ → σ`, there is a linear map `r : σ → τ` with
  `IsEquivariantOn σ τ.representation H r` and `r (j v) = v` for all `v`.
  Proof: take the irreducible family `W` of
  `FiniteIndexRestriction.finite_irreducible_restriction` (independence is not
  needed). By induction over finite sets `s` of indices, construct an
  `H`-equivariant `r` with `r (j w) = w` for `w` in every `W i`, `i ∈ s`. For a
  new index `a`, put `q := id - j ∘ r` (an `H`-equivariant endomorphism of `σ`
  vanishing on `j (W i)` for `i ∈ s`) and let `φ := q ∘ j` on `W a`, an
  `H`-intertwiner. By Schur, `φ` is zero or injective. If zero, then
  `j w = j (r (j w))`, so `r (j w) = w` on `W a` by injectivity of `j`. If
  injective, `CompactSplitting.exists_retraction` on `H` gives `s'` with
  `s' ∘ φ = id`, and `r' := r + (id - r ∘ j) ∘ s' ∘ q` is `H`-equivariant, agrees
  with `r` on `j (W i)` for `i ∈ s` (where `q` vanishes) and satisfies
  `r' (j w) = w` on `W a`. For `s` the full index set, the kernel of
  `r ∘ j - id` contains every `W i`, hence their supremum `⊤`.
