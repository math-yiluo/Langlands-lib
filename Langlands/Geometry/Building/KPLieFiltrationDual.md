# Periodicity, real indices and the dual Moy–Prasad lattices

This module continues `Langlands.Geometry.Building.KPLieFiltration`. That
module defines the lattices `𝔤_{x,r} = L.lieFiltration x r` for supplied data
`L : P.LieFiltrationData` and `r ≥ 0` (`r : NNReal`). This module formalizes the
rest of KP 13.3.1:

- the periodicity `𝔤_{x,r+1} = 𝔪 • 𝔤_{x,r}`, as a predicate;
- the extension of `𝔤_{x,r}` to real `r`, with `𝔤_{x,r+}`;
- the dual lattices `𝔤*_{x,r}` and `𝔤*_{x,r+}`.

Notation: `F` is the nonarchimedean local field, `𝒪 = 𝒪[F]` its ring of
integers and `𝔪 = 𝓂[F]` its maximal ideal (Mathlib's `ValuativeRel`
notations). `𝔤 = GenericLie 𝒪[F] G` is the Lie algebra of `G` viewed as an
`𝒪`-module, and `𝔤* = Module.Dual F 𝔤` is its `F`-linear dual. All
declarations are in the namespace
`Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData`, with
`L : P.LieFiltrationData` and `x : P.Apartment`.

## Periodicity

- `IsPeriodic L` (a `Prop`) says that
  `L.lieFiltration x (r + 1) = 𝔪 • L.lieFiltration x r` for all `x` and all
  `r ≥ 0`. The building data of the Library use the normalized valuation
  `localFieldOrder F`, with `ord(Fˣ) = ℤ`, so the shift by `1` corresponds to
  the maximal ideal.
- `smul_lieFiltration_le hL x k t`: under `hL : L.IsPeriodic`,
  `𝔪^k • 𝔤_{x,t} ≤ 𝔤_{x,t+k}`. The proof is by induction on `k`, using
  `pow_succ`, `Submodule.mul_smul` and `hL`.

## Real indices

- `indexShift r = ⌈-r⌉₊` is the least natural number `n` with `r + n ≥ 0`.
  `add_indexShift_nonneg` proves `r + n ≥ 0`. `shiftedIndex r : NNReal` is
  `r + n`. `indexShift_coe` and `shiftedIndex_coe` say that `n = 0` and
  `shiftedIndex r = r` for `r ≥ 0`.
- `lieFiltrationReal x r` is the lattice `𝔤_{x,r}` for real `r`. With
  `n = indexShift r`, it is
  `⨅ a ∈ 𝔪^n, (𝔤_{x,r+n}).comap (a • id)`, the set of `X` with `a • X ∈ 𝔤_{x,r+n}`
  for all `a ∈ 𝔪^n` (`mem_lieFiltrationReal`). In other words,
  `𝔪^n X ⊆ 𝔤_{x,r+n}`.
- `lieFiltrationReal_coe`: for `r ≥ 0` this is the original
  `L.lieFiltration x r`, because `n = 0` and `𝔪^0 = 𝒪`. No hypothesis is
  needed.
- `lieFiltrationReal_antitone hL x`: under periodicity, `r ≤ s` implies
  `𝔤_{x,s} ≤ 𝔤_{x,r}`. Write `n_r = n_s + k`. An element `b ∈ 𝔪^{n_r}` is a
  sum of products `a c` with `a ∈ 𝔪^{n_s}` and `c ∈ 𝔪^k`
  (`Submodule.mul_induction_on`). For `X ∈ 𝔤_{x,s}`,
  `(a c) • X = c • (a • X)` lies in `𝔪^k • 𝔤_{x,s+n_s}`. That is contained in
  `𝔤_{x,s+n_s+k}` by `smul_lieFiltration_le`, and then in `𝔤_{x,r+n_r}` by
  `lieFiltration_antitone`, since `r + n_r ≤ s + n_s + k`.
- `lieFiltrationPlusReal x r` is `𝔤_{x,r+}`, defined as the supremum of the
  submodules `𝔤_{x,s}` for real `s > r`. `lieFiltrationPlusReal_antitone`
  needs no hypothesis. `lieFiltrationReal_le_lieFiltrationPlusReal` gives
  `𝔤_{x,s} ≤ 𝔤_{x,r+}` for `r < s`. Under periodicity,
  `lieFiltrationPlusReal_le` gives `𝔤_{x,r+} ≤ 𝔤_{x,r}`.
- `mem_biSup_lt_of_antitone` is a general helper: for an antitone family `f`
  of submodules indexed by `ℝ` (over any semiring), `X` lies in the supremum
  of the `f s` over `s > r` if and only if `X ∈ f s` for some `s > r`. The
  proof rewrites the supremum over the subtype `{s // r < s}` (`iSup_subtype'`)
  and applies `Submodule.mem_iSup_of_directed`; the family is directed because
  `f s` and `f s'` are both contained in `f (min s s')`.
- `mem_lieFiltrationPlusReal hL`: under periodicity, `X ∈ 𝔤_{x,r+}` if and
  only if `X ∈ 𝔤_{x,s}` for some real `s > r`. So `𝔤_{x,r+}` is KP's union
  `⋃_{s>r} 𝔤_{x,s}`. This is the helper applied to
  `lieFiltrationReal_antitone hL x`. Without a hypothesis making the real
  family decreasing, the supremum can be strictly larger than the union, so
  the union description is not claimed for arbitrary supplied data.

## Dual lattices

- `maximalIdealSubmodule` is `𝔪`, viewed as an `𝒪`-submodule of `F` (the
  image of `𝓂[F]` under `Algebra.linearMap 𝒪[F] F`).
- `dualPairingSubmodule X`, for `X ∈ 𝔤*`, is the `𝒪`-submodule of the
  `Y ∈ 𝔤` with `X(Y) ∈ 𝔪`. `mem_dualPairingSubmodule` states this as
  `∃ m ∈ 𝓂[F], (m : F) = X Y`.
- `dualLieFiltration x r : Submodule 𝒪[F] (Module.Dual F 𝔤)` is the lattice
  `𝔤*_{x,r}`. It consists of the `X` with
  `𝔤_{x,(-r)+} ≤ dualPairingSubmodule X`. Closure under sums and under
  `𝒪`-scalars holds because `𝔪` is an ideal. `mem_dualLieFiltration` says:
  `X ∈ 𝔤*_{x,r}` if and only if `X(Y) ∈ 𝔪` for every real `s > -r` and every
  `Y ∈ 𝔤_{x,s}`. So taking the supremum instead of the union in
  `𝔤_{x,(-r)+}` makes no difference here.
- `dualLieFiltration_antitone`: `𝔤*_{x,s} ≤ 𝔤*_{x,r}` for `r ≤ s`. No
  hypothesis is needed.
- `dualLieFiltrationPlus x r` is `𝔤*_{x,r+}`, defined as the supremum of the
  submodules `𝔤*_{x,s}` for `s > r`. `dualLieFiltrationPlus_le` gives
  `𝔤*_{x,r+} ≤ 𝔤*_{x,r}`.
- `mem_dualLieFiltrationPlus`: `X ∈ 𝔤*_{x,r+}` if and only if
  `X ∈ 𝔤*_{x,s}` for some `s > r`, so `𝔤*_{x,r+}` is KP's union
  `⋃_{s>r} 𝔤*_{x,s}`. No hypothesis is needed: this is the helper applied to
  `dualLieFiltration_antitone`.

## Comparison with Kaletha–Prasad

KP 13.3.1 (printed p. 470; PDF p. 501) reads: "Let `𝔤_{x,r}` be the Lie
algebra of this group scheme, it is an `o`-lattice in the `k`-vector space
`𝔤(k)`. Let `𝔪` denote the maximal ideal of `o`. For `n ∈ ℕ` the identity
`𝔤_{x,r+n} = 𝔪^n · 𝔤_{x,r}` holds by Proposition 8.5.16. Therefore, we may
extend the definition of `𝔤_{x,r}` to all `ℝ` via this relation. … Recalling
the convention of §1.6, this filtration extends to `ℝ̃` by
`𝔤_{x,r+} = ⋃_{s>r} 𝔤_{x,s}`. For any real number `r`, we define the lattice
`𝔤*_{x,r}` in `𝔤*` as follows:
`𝔤*_{x,r} = {X ∈ 𝔤* | X(Y) ∈ 𝔪 for all Y ∈ 𝔤_{x,(-r)+}}`."

KP Proposition 8.5.16 (printed p. 319; PDF p. 350) reads: "For any integer
`n ⩾ 0`, the `n`th congruence group scheme `(𝒢_{x,f})_n` equals
`𝒢_{x,f+n}`."

How the module relates to this:

- `IsPeriodic` is the identity `𝔤_{x,r+n} = 𝔪^n · 𝔤_{x,r}` for `n = 1`. The
  case of general `n` follows by induction. For supplied data it is a
  hypothesis, not a theorem, because the models `𝒢_{x,r}` of Proposition
  8.5.16 are not constructed.
- For `r < 0`, KP define `𝔤_{x,r}` as the lattice `M` with
  `𝔪^n M = 𝔤_{x,r+n}`. `lieFiltrationReal` uses the explicit choice
  `n = ⌈-r⌉₊` and takes `M = {X | 𝔪^n X ⊆ 𝔤_{x,r+n}}`. When `𝔪 = ϖ𝒪` is
  principal, as for a local field, `M = ϖ^{-n} 𝔤_{x,r+n}`, and then
  `𝔪^n M = 𝔤_{x,r+n}`. The module does not prove this last identity, nor that
  the result does not depend on the choice of `n`.
- KP's §1.6 convention forms `𝔤_{x,r+}` as a union over a decreasing family.
  `lieFiltrationPlusReal` is the supremum of submodules; it agrees with the
  union under periodicity (`mem_lieFiltrationPlusReal`), because periodicity
  makes the real family decreasing. For arbitrary supplied data the real
  family need not be decreasing, and the supremum can be larger than the
  union. An example (worked by hand, not formalized; it was pointed out in
  the review of the first version of this module): for the split torus
  `G_m²` with Lie coordinates `e₁, e₂` and a uniformizer `ϖ`, take
  `𝔤_{x,t} = 𝒪²` for `0 ≤ t ≤ 1/2` and `𝔤_{x,t} = 𝒪e₁ ⊕ ϖ²𝒪e₂` for
  `t > 1/2`, which is a decreasing family on `t ≥ 0` but not periodic. At
  `r = -1/4`, every `s` with `r < s < 0` gives `ϖ⁻¹𝒪e₁ ⊕ ϖ𝒪e₂`, and every
  `s ≥ 0` gives a submodule of `𝒪²`. The vector `ϖ⁻¹e₁ + e₂` lies in the
  supremum but in none of the `𝔤_{x,s}`, `s > r`.
- The definition of `𝔤*_{x,r}` is KP's, with the union `𝔤_{x,(-r)+}` replaced
  by the supremum of submodules. `mem_dualLieFiltration` shows that this gives
  the same membership condition with no hypothesis, because the `Y` with
  `X(Y) ∈ 𝔪` form an `𝒪`-submodule.
- `𝔤*_{x,r+}` is KP's union `⋃_{s>r} 𝔤*_{x,s}` with no hypothesis
  (`mem_dualLieFiltrationPlus`).

The corrections of 1 November 2024 have no entry for §13.3 or §8.5. Their
Chapter 8 entries stop at §8.4, and their Chapter 13 entries are 13.5.2,
13.6.2 and 13.8.5.

## Provenance

Derived. The predicate and the definitions transcribe KP 13.3.1 for the
supplied lattices of `KPLieFiltration`. The explicit choice
`n = ⌈-r⌉₊` and the formulation of `𝔪^{-n}` through `𝔪^n X ⊆ 𝔤_{x,r+n}`
(which avoids choosing a uniformizer) are internal. The Lean code uses
`LieFiltrationData.lieFiltration` and `lieFiltration_antitone` (module
`KPLieFiltration`), `GenericLie`, Mathlib's `ValuativeRel`
notations `𝒪[F]` and `𝓂[F]`, `Module.Dual`, `Submodule.mul_induction_on`,
`Submodule.mul_smul`, `Submodule.smul_mem_smul`, `iSup_subtype'` and
`Submodule.mem_iSup_of_directed`. The helper `mem_biSup_lt_of_antitone`
follows the pattern of `mem_filtrationPlus` in the Library module
`KPRootFixerPlus`. No external code is adapted.

## Not claimed

- Periodicity is a hypothesis. Proposition 8.5.16 and the models `𝒢_{x,r}`
  are not formalized.
- The identity `𝔪^n · 𝔤_{x,r} = 𝔤_{x,r+n}` for negative `r`, and the
  independence of `lieFiltrationReal` from the choice of `n`, are not proved.
- That `𝔤_{x,r}` and `𝔤*_{x,r}` are `𝒪`-lattices (finitely generated, spanning)
  is not proved. Nor is the separatedness of the filtration, or any duality
  between `𝔤_{x,r}` and `𝔤*_{x,-r}`.
- The equality of `𝔤_{x,r+}` with KP's union is proved only under
  periodicity (`mem_lieFiltrationPlusReal`); for arbitrary supplied data it can
  fail.
- The actions of `𝒢_x^0` and `Gred_x` on these lattices and on
  `𝔤_{x,r}/𝔤_{x,r+}` and `𝔤*_{x,r}/𝔤*_{x,r+}` (KP 13.3.4) are not treated.
