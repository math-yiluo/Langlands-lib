# Čech exactness of quasi-coherent modules on standard affine covers

Author: Worker 727.

This module proves that a quasi-coherent `𝒪_X`-module has exact ordered Čech complex (module
`Langlands.Cohomology.CechCochains`) in every positive degree for every standard open covering
of an affine open. It is a helper for the proof of
`Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingStatement`.
It contains no `sorry` and no new axioms.

## Main result

In namespace `Langlands.AlgebraicGeometry.Modules.AffineVanishing`, for `X : Scheme.{u}`, an
open `W : X.Opens`, a type `ι` and `g : ι → Γ(X, W)`:

- `cover g : ι → X.Opens` (abbreviation) sends `i` to the basic open `X.basicOpen (g i)`, the
  locus in `W` where `g i` is invertible.
- `exactAt_cover`:

  ```lean
  theorem exactAt_cover (M : X.Modules) [M.IsQuasicoherent] (hW : IsAffineOpen W) [Finite ι]
      (hg : Ideal.span (Set.range g) = ⊤) (p : ℕ) : Cech.ExactAt M.presheaf (cover g) p
  ```

  (argument order in Lean: `g M hW hg p`). If `W` is affine and finitely many `g i` generate
  the unit ideal of `Γ(X, W)`, then every `(p + 1)`-cocycle of the ordered Čech complex of `M`
  for the family `D(g i)` is a coboundary.

## Provenance

This is Stacks Lemma 01X9 (`lemma-cech-cohomology-quasi-coherent-trivial`, `coherent.tex`
lines 44-135 of the registered source `stacks-flasque-affine-vanishing-kunneth-a04446e5`,
Stacks commit `a04446e57ec1fbc252a871afcec7752fb2807b14`): for a quasi-coherent `F` and a
standard open covering `U = ⋃_{i=1}^n D(f_i)` of an affine open (the `f_i` generate the unit
ideal), `Ȟ^p(𝒰, F) = 0` for all `p > 0`. Stacks uses all ordered tuples, as
`Cech.C` does. The finite index type `ι` replaces `{1, …, n}`; repetitions in `g` are allowed.

The Stacks proof localizes the extended Čech complex at a prime and writes down a contracting
homotopy. The Lean proof uses a different, standard argument with a partition of unity by
powers of the `g i`, described below. It needs two localization facts on affine opens, which
are taken from Mathlib's description of quasi-coherent modules on `Spec R`.

## Proof

**Localization on affine opens.** Let `V` be an affine open of `X`, `h ∈ Γ(X, V)` and
`D(h) = X.basicOpen h`.

1. Every section `s` of `M` over `D(h)` becomes, after multiplication by a large power of `h`,
   the restriction of a section over `V` (`eventually_exists_res_eq_pow_smul`).
2. A section of `M` over `V` that vanishes on `D(h)` is killed by a large power of `h`
   (`eventually_pow_smul_eq_zero`).

On `Spec R` these are `spec_exists_pow_smul_eq_map` and `spec_exists_pow_smul_eq_zero`.
Mathlib's instance `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent` with
`isIso_fromTildeΓ_iff_isLocalizing` shows that, for a quasi-coherent module `N` on `Spec R`,
the restriction `Γ(N, ⊤) ⟶ Γ(N, D(f))` is a localization at the powers of `f`
(`IsLocalizedModule`); the two facts are its surjectivity and kernel conditions. For a
general `X` they are transported along the open immersion
`hV.fromSpec : Spec Γ(X, V) ⟶ X` with image `V`. The module `M.restrict hV.fromSpec` is
quasi-coherent, its sections are those of `M` over image opens (`restrictAppIso`), and its
scalar action matches the one of `M` through `appIso` and `ΓSpecIso`
(`restrictAppIso_hom_smul`). Mathlib's `IsAffineOpen.fromSpec_image_basicOpen` identifies the
image of `PrimeSpectrum.basicOpen h` with `X.basicOpen h`.

**Exactness.** Write `U_σ` for `Cech.inter (cover g) σ`. Each `U_σ` is affine
(`isAffineOpen_inter`, by induction on the length of `σ` using `IsAffineOpen.basicOpen`), and
`U_{(k, σ)}` is the basic open of the restriction of `g k` to `U_σ` (`basicOpen_inter_cons`).
Let `z` be a `(p + 1)`-cocycle.

1. By fact 1 on the affine `U_σ`, there are `N` and `p`-cochains `t k` such that
   `t k σ` restricts on `U_{(k, σ)}` to `g k ^ N • z (k, σ)`. Since `ι` and the tuples
   `Fin (p + 1) → ι` are finite, one `N` serves for all `k` and `σ` (`Filter.eventually_all`).
2. Let `e k = d (t k) - g k ^ N • z`. On `D(g k) ⊓ U_τ`, the cocycle condition at `(k, τ)`
   (`Cech.res_eq_sum_of_d_eq_zero`) shows `e k τ = 0`. By fact 2 on the affine `U_τ`, there
   is `N'` with `g k ^ N' • e k τ = 0` for all `k` and `τ`.
3. The powers `g k ^ (N + N')` still generate the unit ideal (`Ideal.span_pow_eq_top`), so
   `1 = ∑ k, a k * g k ^ (N + N')` for some `a`. Let `y = ∑ k, a k * g k ^ N' • t k`.
   Multiplication by functions on `W` commutes with the Čech differential (`d_csmul`), so
   `d y τ = ∑ k, a k * g k ^ N' • (e k τ + g k ^ N • z τ) = ∑ k, a k * g k ^ (N + N') • z τ =
   z τ`.

## Auxiliary results

- `rres h : Γ(X, V) →+* Γ(X, U)` for `h : U ≤ V`: restriction of functions, with `rres_rres`,
  `rres_self` and `basicOpen_rres` (`X.basicOpen (rres h r) = U ⊓ X.basicOpen r`).
- `res_smul M h r x`: restriction of sections of `M` is semilinear along `rres h`.
- `image_fromSpec_le`, `image_fromSpec_top`: images of opens under `hV.fromSpec` lie in `V`,
  and the image of `⊤` is `V`.
- `ΓSpecIso_inv_map_appIso_inv`, `appIso_inv_map_ΓSpecIso_inv`: the function `r ∈ Γ(X, V)`,
  viewed on `Spec Γ(X, V)`, restricted to `U` and moved back to `X`, is `rres _ r`.
- `exists_pow_smul_eq_res_aux`, `exists_pow_smul_eq_zero_aux`: facts 1 and 2 with a single
  exponent; `eventually_exists_res_eq_pow_smul_of_exists` passes from one exponent to all
  larger ones.
- `inter_le`, `inter_cons_le`, `basicOpen_inter`: the intersections `U_σ` lie in `W`, and
  `X.basicOpen (rres _ (g k)) = D(g k) ⊓ U_σ`.
- `csmul g M r c`: multiplication of a Čech cochain by `r ∈ Γ(X, W)`, componentwise through
  `rres`.
