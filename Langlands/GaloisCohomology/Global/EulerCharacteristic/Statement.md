# The global Euler characteristic formula: statement

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Statement.lean`, namespace `Langlands.GaloisCohomology`.

For a number field `K`, a separable closure `Ω`, a finite set `S` of finite places of `K`,
`G_S = Gal(K_S/K)` and a finite smooth `G_S`-module `M` whose order is a unit outside `S`, Tate's
global Euler characteristic formula is
`#H⁰(G_S, M) · #H²(G_S, M) / #H¹(G_S, M) = ∏_{w real} #H⁰(K_w, M) / (#M)^{#∞}`,
`#∞` the number of infinite places of `K` (`GlobalEulerCharacteristicStatement`; the left side is
`eulerCharacteristic M`). It is proved in
`Langlands.GaloisCohomology.Global.EulerCharacteristic.Proof`.

```lean
def GlobalEulerCharacteristicStatement : Prop
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.GlobalEulerCharacteristicStatement : Prop
```

## Outline of the proofs

A definition.

- `GlobalEulerCharacteristicStatement`: **Tate's global Euler characteristic formula** for `G_S`: for every finite smooth module `M` whose order is invertible outside `S`, `χ(G_S, M) = ∏_{w real} #H⁰(K_w, M) / (#M)^{#∞}`.

## Declarations

`GlobalEulerCharacteristicStatement`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), (8.7.4), p. 505.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed. (BookSurge 2006), I §5, Theorem 5.1, p. 67.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/GlobalEulerFormulaInf.lean` lines 1–88. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).

Renamings (source → Library): `GlobalEulerFormula` → `GlobalEulerCharacteristicStatement`, `GlobalEulerFormulaInf` → `GlobalEulerCharacteristicStatement`.
