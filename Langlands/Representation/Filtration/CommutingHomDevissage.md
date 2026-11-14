# Commutation of all maps out of a filtered functor value, piece by piece

Module `Langlands.Representation.Filtration.CommutingHomDevissage`, namespace
`Langlands.RepFunctorFiltration`.

This module is an internal helper. It is not a result of the literature. It supports the Lean
proof `bernsteinInvariantCenterInclusion` of Renard 2026, VI.10.4, `ℨ_D^{W(D)} ⊂ ℨ_Ω`
(`CuspidalSupport/BernsteinBlockCenterFunctionsInvariantCenterProof`). That proof's route
differs from Renard's. Renard filters the bimodule `R_Ω` and applies the filtered-bimodule
Lemma. The Lean proof applies the dévissage below to the maps out of the support filtration of
`r_P(i_P Π_D)`. Only the vanishing of the comparison maps between distinct pieces is used,
which plays the role of Renard's step `Hom(Q_w, Q_{w'}) = 0`.

## Setting

`F : C ⥤ Rep R G` is a functor to representations of a monoid `G` over a commutative ring
`R`. `s : RepFunctorFiltration F n` is a finite increasing filtration of `F` by subfunctors,
with steps `s.step k` (`k : Fin (n + 1)`, step `0` zero, step `n` everything) and graded pieces
`s.graded i` (`i : Fin n`). The piece `i` is the quotient of step `i.succ` by step
`i.castSucc`. Fix an object `X`, a representation `Y`, `z : X ⟶ X` and `z_Y : Y ⟶ Y`. The
module uses the published API of `Filtration/HomVanishingFiltration`: `homVanishing s X Y k` is
the additive group of maps `F X ⟶ Y` vanishing on step `k`, and `gradedDescent` descends such
a map to the piece `k`.

## Declarations

- `comp_mem_homVanishing`: if `h` vanishes on step `i`, so does `h ≫ β`.
- `commutator_mem_homVanishing`: if `h` vanishes on step `i`, so does the commutator
  `F(a) ≫ h - h ≫ β`, for all `a : X ⟶ X` and `β : Y ⟶ Y`.
- `gradedDescent_commutator`: the descent of `F(a) ≫ h - h ≫ β` to the piece `j` is
  `gr_j(a) ≫ d - d ≫ β`, where `d` is the descent of `h`. Both sides agree on the classes of
  vectors by definition.
- `commutator_commutator`: if `a ≫ z = z ≫ a` and `β ≫ z_Y = z_Y ≫ β`, then
  `δ(F(a) ≫ h - h ≫ β) = F(a) ≫ δh - δh ≫ β`, where `δh = F(z) ≫ h - h ≫ z_Y`. The proof
  expands the composites, uses `F(z) ≫ F(a) = F(a) ≫ F(z)` (functoriality) and closes with
  `abel`.
- `map_comp_eq_comp_of_graded` (the dévissage). Assume:
  - (`hA`) every map `g : gr_i X ⟶ Y` satisfies `gr_i(z) ≫ g = g ≫ z_Y`;
  - (`hB`) for `j < k`, a map `d : gr_k X ⟶ Y` is zero as soon as `gr_k(a) ≫ d = d ≫ β`
    holds for every pair `(a, β)` with `a ≫ z = z ≫ a`, `β ≫ z_Y = z_Y ≫ β` and
    `gr_j(a) ≫ g = g ≫ β` for all `g : gr_j X ⟶ Y`.

  Then every `h : F X ⟶ Y` satisfies `F(z) ≫ h = h ≫ z_Y`.

## Proof of the dévissage

Write `δh = F(z) ≫ h - h ≫ z_Y`. The claim `P k` says that `δh` vanishes on step `k` for every
`h`. It is proved by induction on `k` (`Fin.induction`). Step `0` is zero
(`homVanishing_zero`). At the end, `P n` and `homVanishing_last` give `δh = 0`.

For the step `k → k + 1`, a second claim `C m` (for `m ≤ k`) says: if `h` vanishes on step
`k - m`, then `δh` vanishes on step `k + 1`. It is proved by induction on `m`, and `C k`
applied to any `h` gives `P (k + 1)`.

- `m = 0`: `h` vanishes on step `k`, so `δh` does too, and its descent to the piece `k` is
  `gr_k(z) ≫ d - d ≫ z_Y` by `gradedDescent_commutator`. This is zero by `hA`. By
  `gradedDescent_eq_zero_iff`, `δh` vanishes on step `k + 1`.
- `m + 1`: `h` vanishes on step `j = k - (m + 1) < k`. By `P k`, `δh` vanishes on step `k`;
  let `d` be its descent to the piece `k`. Apply `hB` to `j`, `k` and `d`. Let `(a, β)` be a pair
  as in `hB`. The commutator `h' = F(a) ≫ h - h ≫ β` vanishes on step `j`. Its descent to the
  piece `j` is `gr_j(a) ≫ d_h - d_h ≫ β = 0`, so `h'` vanishes on step `j + 1 = k - m`. By
  `C m`, `δh'` vanishes on step `k + 1`. By `commutator_commutator`, `δh'` is the commutator of
  `δh` with `(a, β)`, so its descent to the piece `k`, `gr_k(a) ≫ d - d ≫ β`, is zero. Hence
  `d` satisfies the premise of `hB`, so `d = 0`, and `δh` vanishes on step `k + 1`.

Steps are indexed as `⟨k - m, _⟩ : Fin (n + 1)`; the identities `k - 0 = k` and
`k - m = (k - (m + 1)) + 1` are checked with `omega`.
