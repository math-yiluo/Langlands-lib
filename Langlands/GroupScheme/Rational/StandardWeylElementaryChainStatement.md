# Factorization into elementary Weyl elements (Renard VI.5.4, Lemma; Bernstein–Zelevinsky Lemma 2.17): statement

Module `Langlands.GroupScheme.Rational.StandardWeylElementaryChainStatement`.
Namespace `Langlands.GroupScheme`. Universe parameter `u`.
The module contains one **statement**, the `Prop`-valued definition
`StandardWeylElementaryChainStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read the end of the proof of the Theorem of VI.5.4, printed p.175 /
PDF p.181:

> Soit `w ∈ W(L, M)`. On dit que `w` est élémentaire s'il existe un sous-groupe
> parabolique standard `T = SV` de `G` contenant `P` et `Q`, tel que `w ∈ W_S` et
> tel que `l(M) = 2` en tant que sous-groupe de Levi standard de `S`. […]
>
> **Lemme.** Soient `M` et `L` des sous-groupes de Levi standards de `G` et
> `w ∈ W(L, M)`. Alors il existe une suite de sous-groupes de Levi standards de `G`
> `L = L_0, L_1, …, L_m = M` et pour chaque `i = 1, …, m`, `w_i ∈ W(L_{i-1}, L_i)`
> élémentaire, tels que `w = w_m w_{m-1} ⋯ w_1`.

Renard cites [5], Lemma 2.17. That is Bernstein–Zelevinsky, *Induced representations
of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. Worker 1222
read the original: 2.16(2) and Lemma 2.17 on journal pp.449–450 (PDF pp.10–11), and
the proof in 6.5 on journal pp.469–470 (PDF pp.30–31). In BZ, `w : M → N` is
elementary if there is a standard `L` with `M, N < L`, `w ∈ W_L` and `l(M) = 2`
inside `L`.

The other notation is from V.4.3–V.4.4 (printed p.119 / PDF p.125):
`W(L, M) = {w ∈ W_G | w·L = M}`, `W(M, ∗) = ⋃_L W(M, L)` over the standard Levi
subgroups `L`, and `l(M) = |W(M, ∗)/W_M|`.

The operator approved this unit on 11 November 2026, on the actual algebraic-group
objects of the framework and with no separate Weyl data.

## The statement

The setting and objects are those of the companion V.4.6 statement
`StandardWeylMinimalRepresentativesStatement`: a connected reductive `G` over a
nonarchimedean local field `k`, a maximal split torus `i`, a generic cocharacter `ν`,
`W_G = relativeWeylGroup i`, `W_I = standardRelativeWeylGroup i ν (rootSet i ν I)`,
and the standard subgroups `levi i ν I` and `parabolic i ν I` of `G(k)`. A standard
Levi subgroup is given by its index set `I ⊆ Δ`, and `w·H` is `H.map (MulAut.conj n)`
for a representative `n : normalizerPoints i` of `w`. Inside the statement:

- `WLM IL IM` is `W(L, M)`: the `w` with a representative `n` such that
  `n L n⁻¹ = M`.
- `ell IS IM` is `l(M)` computed in `S = L_{IS}`: the number of cosets `v W_M`
  (in `W_G / W_M`) of the elements `v ∈ W_S` with `v·M` a standard Levi subgroup of
  `S`, that is `v ∈ W(M, L_K)` for some `K ⊆ IS`.
- `IsElementary IL IM w` holds when `w ∈ W(L, M)` and some `IS` satisfies
  `P_L ≤ P_S`, `P_M ≤ P_S`, `w ∈ W_S` and `ell IS IM = 2`.

For all index sets `IL` and `IM` with `IL ≠ Δ` (some simple root is not in `IL`),
and every `w ∈ W(L, M)`, there are `m : ℕ`, index sets `Ls 0, …, Ls m` with
`Ls 0 = IL` and `Ls m = IM`, and elements `ws 0, …, ws (m-1)` such that each
`ws j` is elementary from `Ls j` to `Ls (j+1)` and `w = ws (m-1) ⋯ ws 0`. The
product is `((List.ofFn ws).reverse).prod`.

## Formalization choices

- **Added hypothesis `L ≠ G`.** The literal lemma is false for `L = M = G` and
  `w ≠ 1`. Then `W(G, G) = W_G`. An elementary element out of `G` needs a standard
  `S` with `P_S ⊇ G`, so `S = G`, and `l_G(G) = |W_G / W_G| = 1 ≠ 2`. So no chain
  has `m ≥ 1`, and the chain with `m = 0` gives only `w = 1`. Bernstein–Zelevinsky's
  proof starts with "one may assume that `w ∈ W̄(M, N)`", the minimal
  representatives modulo `W_M`. That reduction needs every `u ∈ W_L` to be
  elementary, which holds exactly when `L ≠ G`. In the application (VI.5.4,
  Theorem (iii)) only `w·ρ` matters, and `u·ρ ≃ ρ` for `u ∈ W_L`, so the excluded
  case is not used. When `L ≠ G` the lemma holds as stated, with no quotient by
  `W_L`. When `L = G` the only statement that remains true is `w = 1`, so the
  hypothesis loses no true content beyond that trivial case.
- **Source or target in `l(·) = 2`.** Renard requires `l(M) = 2` in `S` for the
  target `M`. Bernstein–Zelevinsky require `l(M) = 2` in `L` for the source. The
  two agree: `w ∈ W_S` conjugates the source to the target inside `S`, and `l_S` is
  constant on `S`-conjugacy classes of standard Levi subgroups (V.4.4). The
  statement follows Renard.
- **`l_S(M)` as a coset count.** `W_M ⊆ W_S`, so the cosets `v W_M` of elements of
  `W_S` in `W_G / W_M` correspond to the cosets in `W_S / W_M`. The standard Levi
  subgroups of `S` (relative to `S ∩ P_∅`) are the `L_K` with `K ⊆ IS`.
- **"Contains `P` and `Q`".** The parabolic subgroups in Renard's definition are the
  standard parabolic subgroups of the source and target Levi subgroups. The order of
  `P_L` and `P_M` does not matter.
- **Inline sets.** `W(L, M)`, `l_S(M)` and "elementary" are `let`-bound inside the
  statement. The Library has no named `W(L, M)` on the actual relative Weyl group.

## Why the statement is true

The implemented proof is a separate obligation. Bernstein–Zelevinsky's route (6.5)
works in the relative root system. Write `Γ = Π ∩ L`. Assume first `w(Γ) ⊆ Π`
(minimal representative). Induct on the length `l(w)`. If `w ≠ 1`, pick a simple
root `α ∉ Γ` with `w(α) < 0`. Put `Γ' = Γ ∪ {α}`, `S = L_{Γ'}`,
`ŵ = s_S s_L` (longest elements) and `L' = ŵ(L)`. Then `ŵ` is elementary from `L`
to `L'` (6.5(3)), `w ŵ⁻¹` is a minimal representative from `L'` to `M`, and
`l(w ŵ⁻¹) < l(w)` (6.5(2)). For general `w ∈ W(L, M)`, write `w = w̄ u` with `w̄`
minimal and `u ∈ W_L`. If `L ≠ G`, choose `α ∉ Γ` and `S = L_{Γ ∪ {α}}`. Then `L`
is a maximal Levi subgroup of `S`, so `l_S(L) = 2` (V.4.8), and `u` is elementary
from `L` to `L`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement` | `relativeWeylGroup`, `standardRelativeWeylGroup`, `normalizerPoints` (through its imports) |
| `Langlands.Representation.Aubert.General.RationalPointFamily` | `SimpleRoot`, `rootSet`, `parabolic`, `levi` |
