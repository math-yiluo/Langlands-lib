# Quasi-coherence and finiteness of the ideal sheaf

Author: Worker 716. This is an internal helper module for
`Langlands.AlgebraicGeometry.Modules.coherentIntegralIdealFiltration`.

## General lemmas

- `isQuasicoherent_of_affine_nbhds`: let `M` be a module on a scheme `Y`. Suppose every point
  has an affine neighbourhood `V` with `M.restrict V.fromSpec` quasi-coherent. Then `M` is
  quasi-coherent. The proof is the Library proof of
  `IsAffineLocallyQuasicoherent.isQuasicoherent`, restricted to the chosen neighbourhoods
  (`isQuasicoherent_over_of_restrict` and `SheafOfModules.IsQuasicoherent.of_coversTop`).
- `exists_pow_smul_killed`: let `X` be noetherian, `Q` quasi-coherent, `W` an affine open
  and `g ∈ Γ(X, W)`. If the restriction of `t ∈ Γ(Q, W)` to `D(g)` is killed by an ideal
  sheaf `J`, then `g ^ E • t` is killed by `J` for some `E`. Each `c ∈ J.ideal W` gives
  `c • t` vanishing on `D(g)`, so it is killed by a power of `g` (quasi-coherence). Since
  `J.ideal W` is finitely generated, the largest of the exponents for the generators works.
  The annihilator of `g ^ E • t` is an ideal containing the generators, and
  `killed_of_affine` concludes.
- `exists_uniform_pow`: let `δ` be a family of sections over the affine opens inside a
  quasi-compact open `O ≤ W`, compatible with restriction. If each member is killed by a
  power of `g`, one power works for all members. Cover `O` by finitely many affine opens
  (every subset of a noetherian space is compact). Take the largest exponent and check
  vanishing locally (`eq_zero_of_local`).

## The ideal sheaf

`w.ival`, `w.imk` and the lemmas `ival_*` pass between sections of `w.I` and admissible
functions. The quasi-coherence criterion is the Library's `QuasicoherentLocal.IsLocalizingAt`
on the affine open `i⁻¹ W` of `Z`, for `W` an affine open of `X`; `i` is affine.

- `isLocalizingAt_I_zero`: a section of `I` vanishing on `D(h)` is killed by a power of `h`.
  This is the corresponding fact for functions on the affine open `i⁻¹ W`
  (`IsLocalization.map_eq_zero_iff`).
- `isLocalizingAt_I_res`: every section `s'` of `I` over `D(h)` becomes the restriction of
  a section over `i⁻¹ W` after multiplication by a power of `h`. Write `h = i.app W g`, so
  that `D(h) = i⁻¹ D(g)`. Admissibility of `s'` gives a killed extension `t` over `D(g)`.
  The proof then proceeds in five steps.
  1. Localization of functions on `Z` gives `s' · h ^ n = a₀|` with `a₀` over `i⁻¹ W`.
  2. Quasi-coherence of `Q` gives `t₁` over `W` with `t₁|_{D(g)} = g ^ m • t`.
  3. `exists_pow_smul_killed` gives a killed `g ^ E • t₁`.
  4. For affine `V ≤ W ⊓ U` consider the defect
     `δ V = (g ^ n • g ^ E • t₁)|_V - mu V ((h ^ (E + m) * a₀)|)`.
     On the basic open `V ∩ D(g)` both terms equal `g ^ (n + E + m) • t`. This uses the
     agreement of `t` and the linearity of `mu`. So each `δ V` is killed by a power of `g`.
     `exists_uniform_pow` on `O = W ⊓ U` gives one exponent `N`.
  5. Then `g ^ N • g ^ n • g ^ E • t₁` is a killed extension of `h ^ (N + E + m) * a₀`, which
     is therefore admissible. Its restriction to `D(h)` is `h ^ (N + E + m + n) • s'`.
- `isQuasicoherent_I`: `I` is quasi-coherent, by `isQuasicoherent_of_affine_nbhds` with the
  neighbourhoods `i⁻¹ W` and `isQuasicoherent_of_isLocalizingAt`.

## Finiteness

- The closed subscheme is locally noetherian (`isLocallyNoetherian_of_affine_cover`). It is
  covered by the `i⁻¹ W`, whose rings are quotients of the noetherian `Γ(X, W)`.
- `hasFiniteAffineSections_I`: `I` has finite affine sections, since it is a submodule of the
  structure sheaf (Library `HasFiniteAffineSections.of_mono`).
- `hasFiniteAffineSections_pushforward`: on an affine `W`, finitely many generators of
  `Γ(I, i⁻¹ W)` over `Γ(Z, i⁻¹ W)` also generate it over `Γ(X, W)`, because `i.app W` is
  surjective.
