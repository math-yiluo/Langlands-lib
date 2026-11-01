# Quasi-coherence over an affine open, in terms of sections

Author: Worker 921.

This helper module is part of the proof of
`Langlands.AlgebraicGeometry.Modules.NoetherianSeparatedQuasicoherentVanishingStatement`. It
translates quasi-coherence of a module over an affine open into a statement about its
sections, in both directions.

## Declarations

Namespace `Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal`, with
`{X : Scheme.{u}}`.

- `structure IsLocalizingAt (M : X.Modules) (V : X.Opens) : Prop`, with two fields. For every
  `h : Γ(X, V)`:
  - `exists_res_eq`: every `s : Γ(M, X.basicOpen h)` satisfies
    `Cech.res (X.basicOpen_le h) t = rres (X.basicOpen_le h) h ^ n • s` for some `n : ℕ` and
    `t : Γ(M, V)`. Here `Cech.res` is restriction of sections and `rres` is restriction of
    functions, from the Library (`Langlands.Cohomology.CechCochains` and
    `Langlands.AlgebraicGeometry.Modules.AffineVanishing.QuasicoherentCech`).
  - `exists_pow_smul_eq_zero`: every `t : Γ(M, V)` whose restriction to `X.basicOpen h` is
    zero satisfies `h ^ n • t = 0` for some `n`.

  So the restriction map `Γ(M, V) ⟶ Γ(M, D(h))` is a localization at the powers of `h`,
  stated without naming the localization.
- `isLocalizingAt_of_isQuasicoherent (hV : IsAffineOpen V) (M : X.Modules)
  [(M.restrict hV.fromSpec).IsQuasicoherent] : IsLocalizingAt M V`.
- `isQuasicoherent_of_isLocalizingAt (hV : IsAffineOpen V) {M : X.Modules}
  (hM : IsLocalizingAt M V) : (M.restrict hV.fromSpec).IsQuasicoherent`.

Here `hV.fromSpec : Spec Γ(X, V) ⟶ X` is Mathlib's open immersion onto `V`, and
`M.restrict hV.fromSpec` is Mathlib's restriction of `M` along it, a module on
`Spec Γ(X, V)`.

## Proofs

Both directions go through Mathlib's characterization of quasi-coherent modules on
`Spec R`: `isQuasicoherent_iff_isIso_fromTildeΓ` together with
`isIso_fromTildeΓ_iff_isLocalizing`. These say that `N` on `Spec R` is quasi-coherent if and
only if, for every `f : R`, the restriction `N(⊤) ⟶ N(D(f))` is `IsLocalizedModule` at the
powers of `f`, for the `R`-module structures of `modulesSpecToSheaf`. The sections of
`M.restrict hV.fromSpec` over an open `U` are the sections of `M` over
`hV.fromSpec ''ᵁ U` (`restrictAppIso`, an identity). The open `hV.fromSpec ''ᵁ ⊤` is `V`
(`image_fromSpec_top`) and `hV.fromSpec ''ᵁ D(f)` is `X.basicOpen f`
(`IsAffineOpen.fromSpec_image_basicOpen`). The `Γ(X, V)`-action on sections of the
restriction is the action of the restricted function (`restrictAppIso_hom_smul`).

- `isLocalizingAt_of_isQuasicoherent` repeats the proofs of the Library lemmas
  `exists_pow_smul_eq_res_aux` and `exists_pow_smul_eq_zero_aux`. The only change is that the
  hypothesis is quasi-coherence of `M.restrict hV.fromSpec` instead of quasi-coherence of `M`.
  These proofs use only the former, through `spec_exists_pow_smul_eq_map` and
  `spec_exists_pow_smul_eq_zero`.
- `isQuasicoherent_of_isLocalizingAt` checks the three fields of `IsLocalizedModule` for each
  `f : Γ(X, V)`:
  - Units: `f` acts invertibly on sections over `D(f)` by Mathlib's
    `Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen`.
  - Surjectivity: a section `y` over `D(f)` is transported to `X.basicOpen f`. There
    `exists_res_eq` gives `t : Γ(M, V)` with `res t = f ^ n • y`, and `t`, transported back
    to `hV.fromSpec ''ᵁ ⊤`, is the required preimage.
  - Equal images: if two sections over `⊤` agree on `D(f)`, their difference restricts to
    zero on `X.basicOpen f`. `exists_pow_smul_eq_zero` then kills the difference by a power of
    `f`.

  Each transport is a restriction along an equality of opens, and the identities
  `Cech.res_res` and `Cech.res_self` remove it.

## Provenance

This is internal infrastructure, with no separate literature source. The mathematical content
is the standard description of quasi-coherent modules on affine schemes: sections over `D(h)`
are the localization at `h` of sections over the affine open. The proofs here only unpack
Mathlib's `IsLocalizing` criterion through the open immersion `hV.fromSpec`.
