# Levi decomposition of the groups `G(K)_{x,r}` at positive depth

Helper module for Task 6191 (`LocalMoyPrasadGroupPropertiesStatement`). It proves
clauses 5 and 8, and clauses 6 and 7 for `r > 0`. Every result assumes the sign product
cover described below. No new definitions are introduced. Every result is a theorem about
the published objects `BuildingData.moyPrasad`, `BuildingData.rootGroupSpan`,
`BuildingData.rootFiltrationSpan`, `BuildingData.pairingLeviSpan`,
`BuildingData.centralizerTorusImage` and `BuildingData.centralizerTorusFiltration`, and the
sets of roots `zeroPairingRoots`, `positivePairingRoots` and `negativePairingRoots` of a real
cocharacter `ν`.

Sources: Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023).
- Proposition 7.3.12(5): the Iwahori factorization `G_{x,f} = U^-_{x,f} · M_{x,f} · U^+_{x,f}`.
- Lemma 7.3.16: `G_{x,f} ∩ T(K) = T(K)_{f(0)}`.
- Lemma 8.5.19 (PDF p. 350): for a Levi subgroup `M ⊇ S`, `M(K)_{π(x),f} = M(K) ∩ G(K)_{x,f}`.

KP prove Lemma 8.5.19 with the fixed-point scheme of `A_M` acting on the integral model
`G_{x,f}`. The Lean proofs below take a different route. They regroup the sign product
cover along a generic cocharacter and use the Library's algebraic open-cell injectivity
for `U(-λ) × P(λ)`. That injectivity gives unique Levi factors.

## Integral cocharacters with prescribed signs (any field `k`)

`exists_cocharacter_sign_eq`. Suppose the relative roots are finite and `ν` is a real
cocharacter. Then some integral cocharacter `λ` has the same signs as `ν` on every root:
`0 < ⟨b, λ⟩ ↔ 0 < ⟨b, ν⟩` and `⟨b, λ⟩ < 0 ↔ ⟨b, ν⟩ < 0`.

*Proof.* Apply the Library's `RootFaceCone.exists_int_sign_realization` to the finite set of
roots and their negatives. The positivity equivalence for `-b` is the negativity
equivalence for `b`.

`exists_genericCocharacter_refining`. Let `S` be a split torus and `G` locally of finite type.
Then every integral cocharacter `λ` is refined by a generic integral cocharacter `μ`:
roots positive (negative) on `λ` stay positive (negative) on `μ`.

*Proof.* Take a generic `ν₀`, which exists by `IsSplitTorus.exists_genericCocharacter`. Let
`M = 1 + Σ_b |⟨b, ν₀⟩|` over the finite set of roots and put `μ = M · λ + ν₀`. If
`⟨b, λ⟩ ≠ 0`, the term `M⟨b, λ⟩` dominates `|⟨b, ν₀⟩| < M`. If `⟨b, λ⟩ = 0`, then
`⟨b, μ⟩ = ⟨b, ν₀⟩ ≠ 0`.

## Uniqueness of Levi factors (any field `k`, affine `G`)

`rootGroupPoints_le_dynamicCentralizer`. If `⟨a, λ⟩ = 0`, the root group `U_a(k)` lies in
the dynamic centralizer `Z_G(λ)(k)`. The root group centralizes the kernel of `a`
(`RelativeRoot.subgroup_le_kernelCentralizer`). That kernel centralizer lies in `Z_G(λ)`
when `⟨a, λ⟩ = 0` (`kernelCentralizer_le_dynamicCentralizer_of_pairing_eq_zero`).

`leviTripleProduct_injective`. Let `U⁻ ≤ U(-λ)(k)`, `M ≤ Z_G(λ)(k)` and `U⁺ ≤ U(λ)(k)` be
subgroups. Then `(u, m, v) ↦ u · m · v` is injective on `U⁻ × M × U⁺`.

*Proof.* `Z_G(λ)` and `U(λ)` both lie in the parabolic `P(λ)`. The Library's opposite-cell
injectivity for `U(-λ) × P(λ)` (`hasInjectiveOppositeCellMultiplication_of_isAffine`)
separates `u` from `m · v`. Next, `λ(t) m v λ(t)⁻¹` has limit `m` as `t → 0`
(`Dynamic.hasLimit_of_mem_centralizer` and `HasLimit.mul`). Limits are unique, so `m` is
determined by `m · v`, and `v` follows by cancellation. This copies the Library's
`unipotentTripleProduct_injective`, with an arbitrary subgroup of `Z_G(λ)` in place of the
torus image.

## Building data over `K`: roots and normalizers

Fix building data `B` over `K = F^ur` with `Z = Z_G(S)` a torus (`hZ`).

- `finite_relativeRoots`, `exists_genericCocharacter`: the relative roots are finite, and a
  generic integral cocharacter exists. Both use the maximal split torus of `B` and the
  smoothness of the connected reductive group.
- `exists_sign_and_generic`: for every real `ν` there are an integral `λ` with the signs
  of `ν` and a generic `μ` that is positive (negative) on the `ν`-positive (`ν`-negative)
  roots. This combines the two results above.
- `rootFiltrationSpan_mono`, `rootGroupSpan_mono`, `rootFiltrationSpan_union`,
  `rootFiltrationSpan_le_moyPrasad`: elementary lattice properties of the spans. A span over
  roots lies in `G(K)_{x,r}` because each `U_{b,x,r}` does (`filtration_le_moyPrasad`).
- `nonopposite_of_eval`: if `⟨b, ν⟩ = 0 ≠ ⟨c, ν⟩`, then `c` is not a negative multiple of `b`.
- `rootFiltrationSpan_le_normalizer`: let `r ≥ 0` and `Ψ₀, Ψ ⊆ Φ`. Assume no `c ∈ Ψ` is a
  negative multiple of any `b ∈ Ψ₀`, and every root `p b + q c` (`p, q > 0`) lies in `Ψ`.
  Then `U_{Ψ₀,x,r}` normalizes `U_{Ψ,x,r}`.

  *Proof.* The Library's commutator estimate `filtration_commutator_le` puts
  `[U_{b,x,r}, U_{c,x,r}]` in the span of the `U_{pb+qc, x, pr+qr}`. These lie in
  `U_{pb+qc,x,r}` by antitonicity. A group whose commutators with the generators of a span
  stay in the span normalizes it (`subgroup_le_normalizer_closure_of_commutators`).
- `zeroPairing_le_normalizer_positive` / `_negative`: the roots with `⟨b, ν⟩ = 0`
  normalize `U_{Φ⁺(ν),x,r}` and `U_{Φ⁻(ν),x,r}`. The positive-integer combinations
  `p b + q c` keep the sign of `⟨c, ν⟩`.

## Regrouping and uniqueness over `K`

`exists_levi_mul_of_mul`. Suppose `μ` is positive on `Φ⁺(ν)` and negative on `Φ⁻(ν)`. Let
`u ∈ U_{Φ⁺(-μ),x,r}`, `z ∈ Z(K)_r` and `v ∈ U_{Φ⁺(μ),x,r}`. Then
`u · j(z) · v = n' · m · n` with `n' ∈ U_{Φ⁻(ν),x,r}`,
`m ∈ j(Z(K)_r) ⊔ U_{Φ⁰(ν),x,r}` and `n ∈ U_{Φ⁺(ν),x,r}`.

*Proof.* `Φ⁺(μ)` is the disjoint union of `Φ⁰(ν) ∩ Φ⁺(μ)` and `Φ⁺(ν)`. The first part
normalizes `U_{Φ⁺(ν),x,r}`, so the join of the two spans is their product set
(`Subgroup.coe_mul_of_left_le_normalizer_right`). Hence `v = h · n`. Symmetrically
`u = n' · h'` with `h' ∈ U_{Φ⁰(ν) ∩ Φ⁺(-μ),x,r}`. Take `m = h' · j(z) · h`.

`pairingLeviSpan_le_dynamicCentralizer`. If `⟨b, λ⟩ = 0` for every `b ∈ Φ⁰(ν)`, then
`M_ν ≤ Z_G(λ)(K)`. Here `j(Z(K))` lies in the torus centralizer
(`map_mem_centralizerPoints`, `torusCentralizer_le_dynamicCentralizer`), and the root
groups lie in `Z_G(λ)(K)` by `rootGroupPoints_le_dynamicCentralizer`.

`levi_eq_of_mul_eq_mul`. Suppose `λ` has the signs of `ν` on the roots. If
`u · m · v = u' · m' · v'` with `u, u' ∈ U_{Φ⁻(ν)}`, `m, m' ∈ M_ν` and
`v, v' ∈ U_{Φ⁺(ν)}`, then `u = u'`, `m = m'` and `v = v'`. Apply
`leviTripleProduct_injective` for `λ`. `U_{Φ^∓(ν)}` lies in `U(∓λ)(K)` by
`rootGroupSpan_le_dynamicUnipotent` (module `KPLocalMoyPrasadIntersectionCell`).

`leviFiltration_le_pairingLeviSpan`, `leviFiltration_le_moyPrasad`:
`j(Z(K)_r) ⊔ U_{Φ⁰(ν),x,r}` lies in both `M_ν` and `G(K)_{x,r}`.

## Clauses 5–8 from the sign product cover

The hypothesis `hPC` of the final lemmas below says: for every apartment point `x`, every
`r > 0` and every generic integral `μ`,

```
G(K)_{x,r} = U_{Φ⁺(-μ),x,r} · j(Z(K)_r) · U_{Φ⁺(μ),x,r}
```

as sets. This is word for word the conclusion of `LocalMoyPrasadPositiveProductStatement`
(Task 6542, the positive-depth form of KP Lemma 7.3.11 and Proposition 7.3.12). It is an
inline premise of these helper lemmas only. The final proof of Task 6191 will discharge it
with that published theorem, not assume it.

- `exists_mul_of_productCover`: the elementwise form of the cover.
- `exists_levi_mul_of_productCover`: for `r > 0` there is an integral `λ` with the signs of
  `ν` such that every `g ∈ G(K)_{x,r}` is `n' · m · n` as in `exists_levi_mul_of_mul`. Take
  `λ, μ` from `exists_sign_and_generic`, cover `g` along `μ`, and regroup.
- `iwahoriFactorization_of_productCover`: **clause 5** (`LocalMoyPrasadIwahoriFactorization`).
  Let `v' · m · v ∈ G(K)_{x,r}` with `r > 0`. Regroup it as `n' · m₀ · n`.
  `levi_eq_of_mul_eq_mul` gives `v' = n'`, `m = m₀` and `v = n`, and each of these lies in
  `G(K)_{x,r}`.
- `leviIntersection_of_productCover`: **clause 6 for `r > 0`**,
  `M_ν ⊓ G(K)_{x,r} = j(Z(K)_r) ⊔ U_{Φ⁰(ν),x,r}`. For `⊆`, compare `1 · g · 1` with the
  regrouping `n' · m₀ · n` of `g`; uniqueness gives `g = m₀`. `⊇` is the pair of inclusions
  above.
- `comap_moyPrasad_eq_of_productCover`: **clause 7 for `r > 0`**,
  `j⁻¹(G(K)_{x,r}) = Z(K)_r`. This is `comap_moyPrasad_eq_of_cover` (module
  `KPLocalMoyPrasadIntersectionCell`) along one generic `μ`.
- `separated_of_productCover`: **clause 8** (`LocalMoyPrasadSeparated`). This is
  `iInf_moyPrasad_eq_bot_of_cover` along one generic `μ`, which uses the cover at every
  `r > 0`.

The case `r = 0` of clauses 6 and 7 is not covered here. `G(K)_{x,0}` contains Weyl
representatives, so the sign product cover fails at depth zero.
