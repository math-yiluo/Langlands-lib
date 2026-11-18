# The rank-one central cover from a root cell

Author: Worker 919.

Module `Langlands.GroupScheme.Reductive.RankOneCoverOfRootCell`. This is an internal
supporting unit for Task 7586 (target `Langlands.GroupScheme.RankOneCentralCoverStatement`).
It proves the assembly step: a root cell of `G` with pairing `2` gives the target's
conclusion. It assumes the root cell and does not construct it.

## Main theorem (namespace `Langlands.GroupScheme`)

```
theorem rankOneCentralCover_of_rootCell {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    {i : T.toGrp ⟶ G} {α : characterLattice T} {αv : cocharacterLattice T}
    {xp xm : RootCell.Ga k ⟶ G} (D : RootCell.IsRootCell i α αv xp xm)
    (h2 : latticePairing T α αv = 2) :
    ∃ (C : CommGroupScheme (Spec (CommRingCat.of k))), IsSplitTorus C.toGrp ∧
      ∃ (f : SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k) ⊗ C.toGrp ⟶ G)
        (t : CommGroupScheme.prod
          (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin 1))) C ⟶ T),
        IsCentralIsogeny f ∧ IsIsogeny (CommGroupScheme.groupHom t) ∧
        (SpecialLinear.FinSucc.diagonalTorus 1 (CommRingCat.of k) ⊗ₘ 𝟙 C.toGrp) ≫ f =
          CommGroupScheme.groupHom t ≫ i
```

The conclusion is word for word the conclusion of `RankOneCentralCoverStatement`. The
field `k` need not be algebraically closed. No maximality of `i` and no hypothesis on the
set of roots is used. `IsCentralIsogeny` keeps its full meaning: a finite, flat, surjective
isogeny that is locally of finite presentation and has central scheme-theoretic kernel.

## Supporting results (namespace `Langlands.GroupScheme.RankOneCoverOfRootCell`)

Notation from `SpecialLinearTensorCell`: `G₀ C = SL₂ × C`, `T₀ C = 𝔾ₘ × C`, the cell map
`cell₀ C`, the point isomorphism `ptEquiv`, `dg s = diag(s, s⁻¹)`, `up`, `lo` and `wy`.
`Dynamic.tripleCellMultiplication xm i xp` is the cell map of `G`.

- `dg_mul_comm`: if `s² = 1`, then `dg s` commutes with every matrix of `SL₂`, since it is
  the scalar `s`. `cell_zero_zero`: `lo 0 · (dg s · up 0) = dg s`.
- `exists_cell₀_of_isUnit`: a point of `SL₂ × C` whose upper left entry is a unit is
  `cell₀` of a cell point (via `eq_cell`).
- `ptEquiv_comp_apply`: the matrix entries of points are natural in the test scheme.
- `wPt C Z` is the Weyl point `(wy, 1)`. `wPt_conj`:
  `wPt · xp₀(a) · wPt⁻¹ = xm₀(−a)`. `wPt_mul_apply`: the `(0, 0)` entry of `wPt · x` is the
  `(1, 0)` entry of `x`.
- `mono_cell`: the cell map of a root cell is a monomorphism, because it is an open
  immersion.
- In the next three results, `φ : G₀ C ⟶ G` satisfies three hypotheses. They are
  `cell₀ C ≫ φ = powerCell t 1 ≫ (cell map of G)`,
  `xp₀ ≫ φ = gaPower 1 ≫ xp` and `xm₀ ≫ φ = gaPower 1 ≫ xm`.
  - `one_eq_zero_of_isUnit` (Weyl step): let `x` be a kernel point of `φ` and
    `j : W ⟶ Z` a test scheme on which the entry `x₁₀` becomes a unit. Then
    `Γ(W, 𝒪) = 0`.
  - `kernel_isUnit`: the entry `x₀₀` of a kernel point is a unit.
  - `kernel_ptEquiv` (also assuming `t ≫ α = χ₀ C`): a kernel point is `(dg s, c)` with
    `s² = 1`. `kernel_mem_center`: kernel points are central.
- `locallyOfFinitePresentation_of_isIsogeny`: an isogeny into a connected reductive group
  over a field is locally of finite presentation.

## The implemented proof

1. `RankOneCoverTorus.exists_torusIsogeny` gives a split torus `C` and an isogeny
   `t : 𝔾ₘ × C ⟶ T` with `t ≫ α = χ₀ C` and `χv₀ C ≫ t = αv`.
2. `SL₂ × C` is connected reductive (`DirectProduct.isConnectedReductive_tensor`,
   `SpecialLinear.isConnectedReductive`, `IsSplitTorus.isConnectedReductive`).
   `SpecialLinearTensorCell.isRootCell₀` is its root cell. `RootCell.exists_powerIsogeny`
   with `p = ringExpChar k` and `e = 0` gives an isogeny `φ : SL₂ × C ⟶ G`. It satisfies
   `i₀ ≫ φ = t ≫ i`, and it carries the cell, `xp₀` and `xm₀` of `SL₂ × C` to those of `G`.
   The powers are `p⁰ = 1`, so the power maps are identities on coordinates. Then
   `f = φ`, and the torus square is `i₀ ≫ φ = t ≫ i`.
3. *Local finite presentation.* `φ` is finite, and `G` is smooth over `k`, hence locally
   Noetherian. So `locallyOfFinitePresentation_of_isIsogeny` applies.
4. *Centrality of the full kernel* (`isCentral_kernelι_iff`). Let `x` be a point of `SL₂ × C`
   over a test scheme `Z` with `φ(x) = 1`, and let `g` be its matrix.
   - *Weyl step.* Restrict to a test scheme `W` on which `b = g₁₀` is a unit, and set
     `y = wPt · x`. Its entry `y₀₀ = b` is a unit, so `y = cell₀(c)`. Since `φ(x) = 1`,
     `φ(wPt) = φ(y)` is the cell point `(m, τ, p)` of `G`. Apply `φ` to `wPt_conj` with
     `a = 1`. This gives
     `xm(m) i(τ) xp(p) · xp(1) = xm(−1) · xm(m) i(τ) xp(p)`, an equality of the cell points
     `(m, τ, p + 1)` and `(m − 1, τ, p)`. The cell map of `G` is a monomorphism, so
     `m = m − 1` in `Γ(W, 𝒪)` and hence `1 = 0`.
   - *Upper left entry.* `det g = 1` gives `g₀₀ g₁₁ − g₀₁ g₁₀ = 1`. At any point `z` of `Z`
     the stalk is local. So either the germ of `g₀₀` is a unit, or the germ of `g₁₀` is.
     In the second case `z` lies in the basic open `D(g₁₀)`. That open is then a nonempty
     scheme on which `g₁₀` is a unit, and the Weyl step makes its global functions zero,
     which is impossible. So `g₀₀` is a unit at every point, hence a unit.
   - *Shape of `x`.* Now `x = cell₀(m, τ, p)`. So `φ(x)` is the `G`-cell point
     `(m, t(τ), p)`, while `1` is the cell point `(0, 1, 0)`. Injectivity of the cell gives
     `m = p = 0` and `t(τ) = 1`. Hence `χ₀(τ) = α(t(τ)) = 1`, i.e. `s² = 1` for
     `s = tc τ`, and `g = dg s` (`cell_zero_zero`).
   - *Centrality.* `dg s` with `s² = 1` is a scalar matrix, and `C` is commutative. So `x`
     commutes with every point after any base change.
