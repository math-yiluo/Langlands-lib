# Artinian test rings realizing a linear form on the conormal module

Module `Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.NecessityRings`, namespace
`Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.NecessityRings`. Author: Worker 5103
(task `14dfbe95-4d4a-46fd-933a-182df994126c`, openness of versality for actual Picard
families). Everything is proved in the file, with no hypotheses beyond those in the
signatures. Internal construction, used for the necessity direction (`Necessity`); no
literature statement is formalized.

## Local Artinian rings

`localArtinian_of_nil`: a noetherian ring `S` with a surjection `χ : S →+* k` onto a field
whose kernel consists of nilpotent elements is local and Artinian. (Elements not killed by
`χ` are units because `a b - 1` is nilpotent for a lift `b` of `χ(a)⁻¹`; the maximal ideal
`ker χ` is finitely generated and nil, hence nilpotent; then
`isArtinianRing_iff_isNilpotent_maximalIdeal`.)

## Setting

Commutative rings `R`, `P`, `A₀` with `R`-algebra structures and a `P`-algebra `A₀`; a field
`k` that is an `R`-, `A₀`- and `P`-algebra with scalar towers `R → A₀ → k` and
`P → A₀ → k`; an `A₀`-module `Q` that is also a `P`-module (tower `P → A₀ → Q`); a
`P`-linear `jQ : Q → P`; an `A₀`-linear form `φ : Q → k`. Notation: `mP P k` is the kernel of
`P → k` and `mA A₀ k` the kernel of `A₀ → k`.

## Artin–Rees

- `vanish_of_mem_smul`: if `jQ` is injective with range `ker (P → A₀)` (`hJ`), then `φ x = 0`
  whenever `jQ x ∈ mP • S` for a submodule `S ≤ ker (P → A₀)` (because `φ(r • y) =
  r • φ(y) = 0` for `r ∈ mP`).
- `exists_pow_vanish` (`P` noetherian): there is `N > 0` with `φ x = 0` whenever
  `jQ x ∈ mP ^ N`. Proof: Mathlib's Artin–Rees lemma `Ideal.exists_pow_inf_eq_pow_smul`
  gives `mP^(n₀+1) ⊓ J = mP • (mP^n₀ ⊓ J)` for `J = ker (P → A₀)`, then
  `vanish_of_mem_smul`.

## The extension ring

Fix `N > 0` and `hjQ0 : ∀ x, jQ x ↦ 0` in `A₀`.

- `smul_eq_zero_of_mem`: `(jQ x + m) • t = 0` in `k` for `m ∈ mP ^ N`.
- `extIdeal`: the ideal `{inl (jQ x + m) - inr (φ x) | x ∈ Q, m ∈ mP ^ N}` of the
  square-zero extension `Thick P k = P ⊕ k` (Library `Algebra.ThickSquareZero`).
- `ExtRing := Thick P k ⧸ extIdeal` (a `P`- and `R`-algebra), and the `P`-linear
  inclusion `ι : k → ExtRing`, `t ↦ [inr t]` (`ι_apply`), with `ι t * ι t' = 0`
  (`ι_mul_ι`).
- `algebraMap_jQ`: `algebraMap P ExtRing (jQ x) = ι (φ x)`.
- `ι_injective`: `ι` is injective when `φ` vanishes on `jQ⁻¹(mP ^ N)` (e.g. by
  `exists_pow_vanish`).

## The base ring and the reduction

- `BaseRing A₀ k N := A₀ ⧸ mA ^ N` and `chiN : A₀ →ₐ[R] BaseRing` the quotient map.
- `map_mP_le`, `map_mP_eq`: the image of `mP` in `A₀` is contained in (and, for `P → A₀`
  surjective, equal to) `mA`.
- `qE : ExtRing →ₐ[R] BaseRing`, `[(p, t)] ↦ p mod mA^N`, with `qE_algebraMap`,
  `qE_ι` (`qE ∘ ι = 0`), `qE_comp` (`qE ∘ (P → ExtRing) = chiN ∘ (P → A₀)`),
  `qE_surjective` and `exists_ι_of_qE_eq_zero` (`ker qE ⊆ range ι`, for `P → A₀` surjective
  and `hJ`).

## Augmentations and Artinian tests

- `augB : BaseRing →ₐ[R] k` induced by `A₀ → k`, with `augB_surjective` (when `A₀ → k` is
  surjective) and `augB_nil` (its kernel is nil).
- `augE := augB ∘ qE : ExtRing →ₐ[R] k`, with `augE_nil` and `augE_surjective`;
  `algebraMap_mem_extIdeal`: `inl p ∈ extIdeal` for `p ∈ mP ^ N`.
- `isNoetherianRing_thick`: `Thick P k` is noetherian for `P` noetherian and `P → k`
  surjective (it is a quotient of `P × P` as a `P`-module).
- `baseRing_localArtinian`, `extRing_localArtinian`: both rings are local Artinian (by
  `localArtinian_of_nil`).
- `baseTest`, `extTest : ArtinianTest R k` (Library `Deformation.ArtinianTests`) with these
  augmentations, and the test arrow `qTest : extTest ⟶ baseTest` given by `qE`
  (`toAlgHom_qTest`).
