# Heisenberg chart points of a multipliable root group

Module `Langlands.GroupScheme.Rational.RootHeisenbergChartPoints`.

## Setting

`k` (or `K`) is a field, `S` a commutative group scheme over `Spec k` with an embedding
`i : S ⟶ G`, `a` a character, `U = U_a` and `U₂ = U_{2a}` group schemes representing the
root subgroups for `a` and `2a`, `C` a double-root commutator pairing with quotient
`V = U / U₂` (`C.q : U ⟶ V`), and `N : HeisenbergNormalForm C` a Heisenberg normal form:
the inclusion `N.inclusion : U₂ ⟶ U`, a scheme section `N.sec : V ⟶ U` of `C.q` and its
cocycle `N.cocycle : V × V ⟶ U₂` (published in
`Langlands.GroupScheme.Rational.RootHeisenbergNormalForm` and
`Langlands.Geometry.Building.RootUnitaryHeisenbergAssembly`). The vector coordinates
`e T : (T ⟶ V) ≃* Multiplicative (Fin d → Γ(T, 𝒪))` and
`e' T : (T ⟶ U₂) ≃* Multiplicative (Fin m → Γ(T, 𝒪))` are given for every test scheme `T`
over `Spec k`.

## Definitions

- `rationalVectorCoordinates e : rationalPoints V ≃* Multiplicative (Fin n → K)`: the
  coordinates on the identity test scheme `Over.mk (𝟙 (Spec K))`, followed coordinatewise by
  the ring isomorphism `Γ(Spec K, 𝒪) ≅ K` (`Scheme.ΓSpecIso`).
- `HeisenbergNormalForm.chartPoint N e e' x w : rationalPoints U`: the rational point
  `incl(w) * sec(x)`, where `w ∈ K^m` is read as a rational point of `U₂` and `x ∈ K^d` as a
  rational point of `V` through `rationalVectorCoordinates`.
- `HeisenbergNormalForm.testChartPoint N e e' T w x : T ⟶ U`: the same point
  `incl(w) * sec(x)` over an arbitrary test scheme `T`, with `w, x` vectors of global
  sections of `T` (note the order: the `U₂`-coordinate `w` comes first).
- `HeisenbergNormalForm.chartCocycle N e e' T x y`: the cocycle `N.cocycle` evaluated at the
  `T`-points with coordinates `x`, `y` and read in the coordinates `e'`.

These are internal (derived) definitions: they write the published Heisenberg normal form of
a unipotent group of class at most two in explicit coordinates. `rationalVectorCoordinates` and
`chartPoint` are the interface used by `UnitaryChartUpgradeStatement` (module
`Langlands.GroupScheme.Rational.RootHeisenbergUnitaryChart`).

## Results

- `testChartPoint_comp_q`: `incl(w) * sec(x)` maps to the point with coordinates `x` in `V`.
- `testChartPoint_mul` (the Heisenberg law):
  `(w, x) · (w', x') = (w + w' + chartCocycle T x x', x + x')`. Proof: `incl(w')` commutes
  with `sec(x)` because the commutator of `U` lands in the central `U₂`
  (`commute_of_comp_q`), and `sec(x) sec(x') = incl(β(x, x')) sec(x + x')` (`N.sec_mul`).
- `testChartPoint_injective`: the coordinates are determined by the point (compose with
  `C.q`, then cancel the monomorphism `N.inclusion`).
- `exists_testChartPoint_eq`: every `T`-point of `U` is a chart point
  (`N.exists_eq_mul_sec`).
- `chartPoint_eq_testChartPoint`: the rational chart point is the chart point over the
  identity test scheme with coordinates read through `(ΓSpecIso K).inv` (definitional).
- `comp_symm_ofAdd_of_isNatural`, `comp_testChartPoint`: for natural vector coordinates,
  pulling a chart point back along `f : T' ⟶ T` applies `f.left.appTop` to its coordinates.
- `chartCocycle_eq_coordinatePairing`: the coordinate cocycle over `T` is the published
  `coordinatePairing` of `N.cocycle` over the relative global sections of `T`
  (`coordinatePairing_global`).
