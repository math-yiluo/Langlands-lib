# Clauses 4, 6 and 7 of the groups `G(K)_{x,r}` at depth zero and at every depth

Helper module for Task 6191 (`LocalMoyPrasadGroupPropertiesStatement`). It proves the
depth-zero cases of clause 4 (`LocalMoyPrasadRootIntersection`), clause 6
(`LocalMoyPrasadLeviIntersection`) and clause 7 (`LocalMoyPrasadCentralizerIntersection`)
from two depth-zero intersection facts, which are taken as explicit hypotheses. It then
combines them with the positive-depth results of the companion modules
`KPLocalMoyPrasadIntersectionRoot` and `KPLocalMoyPrasadIntersectionLevi` to obtain the
three clauses at every depth. The module introduces no definitions.

Fix building data `B` over `K = F^ur` with `Z = Z_G(S)` a torus (`hZ`). Write
`j : Z → G` for the centralizer inclusion, `Z(K)_r` for `centralizerTorusFiltration`,
`U_Ψ` for `rootGroupSpan Ψ`, `U_{Ψ,x,r}` for `rootFiltrationSpan x Ψ r`, `M_ν` for
`pairingLeviSpan ν` and `Φ⁰(ν)` for `zeroPairingRoots ν`.

## The hypotheses

The two hypotheses are, word for word, the two clauses of the published
proposition `Langlands.Geometry.Building.MaximalUnramified.LocalMoyPrasadDepthZeroStatement`
(module `KPLocalMoyPrasadDepthZeroStatement`) at `F, H, B, hZ`. This module does not import
that proposition; it takes the two clauses as separate hypotheses.

- `hDZa`: for every point `x` and every generic integral cocharacter `μ`,
  `U_{Φ⁺(μ)} ⊓ G(K)_{x,0} = U_{Φ⁺(μ),x,0}`.
  This is Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
  Proposition 7.3.12, at `f = 0`.
- `hDZb`: for every point `x` and every `ν ∈ V`,
  `M_ν ⊓ G(K)_{x,0} ≤ j(Z(K)_0) ⊔ U_{Φ⁰(ν),x,0}`.
  This is KP Lemma 8.5.19 at depth zero.

The positive-depth results use the sign product cover `hPC`: for every `x`, every `r > 0`
and every generic integral cocharacter `μ`,

`G(K)_{x,r} = U_{Φ⁺(-μ),x,r} · j(Z(K)_r) · U_{Φ⁺(μ),x,r}` (as sets).

This is exactly the conclusion of the statement of Task 6542.

## Small lemmas

- `zeroPairingRoots_tmul_eq_empty`: if `μ` is a generic integral cocharacter, then no
  relative root vanishes on `1 ⊗ μ ∈ V`, so `Φ⁰(1 ⊗ μ) = ∅`. The pairing of `b` with
  `1 ⊗ μ` is the integer `⟨b, μ⟩` cast to `ℝ`, and genericity says it is nonzero.
- `rootFiltrationSpan_empty`: `U_{∅,x,r} = 1`, since the defining supremum is empty.

## Depth zero

- `rootIntersection_zero_of_depthZero` (**clause 4 at `r = 0`**, from `hDZa`). Let `Ψ` be a
  closed set of roots and `ν ∈ V` with `⟨b, ν⟩ > 0` for all `b ∈ Ψ`. Then
  `U_Ψ ⊓ G(K)_{x,0} = U_{Ψ,x,0}`.

  *Proof.* `⊇`: `U_{Ψ,x,0} ≤ U_Ψ` (`rootFiltrationSpan_le_rootGroupSpan`, Cell module) and
  `U_{Ψ,x,0} ≤ G(K)_{x,0}` (`rootFiltrationSpan_le_moyPrasad`, Levi module). `⊆`: by
  `exists_sign_and_generic` (Levi module), choose a generic `μ` that is positive on every
  `ν`-positive root, so `Ψ ⊆ Φ⁺(μ)`. Let `g ∈ U_Ψ ⊓ G(K)_{x,0}`. Then
  `g ∈ U_{Φ⁺(μ)} ⊓ G(K)_{x,0}`, which is `U_{Φ⁺(μ),x,0}` by `hDZa`. Now
  `mem_rootFiltrationSpan_of_mem_rootGroupSpan` (Root module, with `r = 0 ≥ 0`) turns
  `g ∈ U_Ψ ⊓ U_{Φ⁺(μ),x,0}` into `g ∈ U_{Ψ,x,0}`.
- `leviIntersection_zero_of_depthZero` (**clause 6 at `r = 0`**, from `hDZb`). For every
  `ν` and `x`, `M_ν ⊓ G(K)_{x,0} = j(Z(K)_0) ⊔ U_{Φ⁰(ν),x,0}`.

  *Proof.* `≤` is `hDZb`. `≥`: the right side lies in `M_ν`
  (`leviFiltration_le_pairingLeviSpan`) and in `G(K)_{x,0}` (`leviFiltration_le_moyPrasad`),
  both from the Levi module.
- `comap_moyPrasad_zero_of_depthZero` (**clause 7 at `r = 0`**, from `hDZb`). For every `x`,
  `j⁻¹(G(K)_{x,0}) = Z(K)_0`.

  *Proof.* `⊇` is the Library's `map_mem_moyPrasad`. `⊆`: let `z ∈ Z(K)` with
  `j(z) ∈ G(K)_{x,0}`. Choose a generic integral `μ` (`exists_genericCocharacter`, Levi
  module) and put `ν = 1 ⊗ μ`. Then `j(z) ∈ M_ν`, because `M_ν` is defined as
  `j(Z(K)) ⊔ U_{Φ⁰(ν)}`. By `hDZb`, `j(z) ∈ j(Z(K)_0) ⊔ U_{Φ⁰(ν),x,0}`. Here `Φ⁰(ν) = ∅`
  and `U_{∅,x,0} = 1`, so `j(z) = j(z')` with `z' ∈ Z(K)_0`. Since `j` is injective on
  `K`-points (`centralizer_map_injective`, Cell module), `z = z' ∈ Z(K)_0`.

## Every depth

Each of the following splits `r : ℝ≥0` into `r = 0` and `r > 0`. The case `r = 0` is the
depth-zero theorem above. The case `r > 0` is the positive-depth theorem from `hPC`.

- `rootIntersection_of_covers`: `hPC` and `hDZa` imply `LocalMoyPrasadRootIntersection B hZ`
  (clause 4). The positive-depth case is `rootIntersection_of_productCover` (Root module).
- `leviIntersection_of_covers`: `hPC` and `hDZb` imply `LocalMoyPrasadLeviIntersection B hZ`
  (clause 6). The positive-depth case is `leviIntersection_of_productCover` (Levi module).
- `centralizerIntersection_of_covers`: `hPC` and `hDZb` imply
  `LocalMoyPrasadCentralizerIntersection B hZ` (clause 7). The positive-depth case is
  `comap_moyPrasad_eq_of_productCover` (Levi module).

This module keeps the product cover and depth-zero facts as explicit hypotheses.
The final composition in `KPLocalMoyPrasadGroupPropertiesProof`, through
`KPLocalMoyPrasadGroupPropertiesReduction`, supplies them using the published
`localMoyPrasadPositiveProduct` and `localMoyPrasadDepthZero` theorems and S1.
