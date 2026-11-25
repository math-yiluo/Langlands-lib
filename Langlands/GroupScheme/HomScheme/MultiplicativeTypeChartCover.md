# The multiplicative-type window charts cover the field points

Module `Langlands.GroupScheme.HomScheme.MultiplicativeTypeChartCover`, namespace
`Langlands.GroupScheme.HomScheme.MultiplicativeTypeChart`.

This is an internal module for the chart construction in the proof of
`MultiplicativeTypeEtaleLiftStatement`. It assembles the window
charts of `MultiplicativeTypeChartConstruction` / `MultiplicativeTypeChartOpen` into a chart
cover. The output is `finiteTypeChartCover_of`, which proves
`MultiplicativeTypeSubgroupModuli.FiniteTypeChartCoverStatement` from three inputs: the fppf
splitting hypothesis, smoothness of coordinate Hopf algebras, and smoothness of the
representing algebras `W`. The module follows the Library module `HomScheme.TorusChartCover`.
The new ingredient is a normal form for finitely generated commutative groups, which brings
the character group of each piece of an fppf splitting to the shape `ℤ^c × F`.

## Results

- `exists_lift_Bf` (arbitrary coordinate algebra `A`): a field point `y` of `W_f` at which `N`
  does not vanish extends to a point of `B_f` along `uS`.
- `Carrier k`: the type `ULift (Fin k)` as a plain `def`, with its `Fintype` instance and
  no other structure. It carries the finite part of a character group in the chart index.
  `ULift (Fin k)` itself already has an addition, so putting a different group structure on
  it would create conflicting instances.
- `exists_normalForm Λ'`: a finitely generated commutative group `Λ'` (`AddGroup.FG`) is
  isomorphic to `(ULift (Fin c) → ℤ) × Carrier k` for some `c, k` and some commutative group
  structure `s` on `Carrier k`. Proof: Mathlib's structure theorem
  `AddCommGroup.equiv_free_prod_directSum_zmod` gives
  `Λ' ≃+ (Fin c →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)`. The direct sum is finite, so it is in
  bijection with `Fin k`. Its group structure is transported to `Carrier k` along this
  bijection (`Equiv.addCommGroup`, `Equiv.addEquiv`). The free part is identified with
  `ULift (Fin c) → ℤ`.
- `exists_window_point`: let `bk : Spec C → T` be a piece of an fppf splitting, on which `i`
  is the closed subgroup of a Hopf point `fk` of `D(Λ')`, and let `x' : C → K` be a field
  point. Then there are a standard lattice `ℤ^c × Carrier k`, a window datum `dw` on it, and a
  point `yK` of `B_f` such that the chart evaluated at `yK` equals the evaluation of `i` at
  `specMap x' ≫ bk`. Proof: transport `fk` along the normal form `T₀` of `Λ'`, apply
  `MixedChartExistence.exists_windowDatum` to the transported Hopf point over `K`, extend the
  resulting point to `B_f` (`exists_lift_Bf`), and compare ranges (`range_twist_eq`,
  `evaluate_comp_of_eq_range`, `evaluate_iS_specMap`, `evaluate_j_comp_pOver`).
- `exists_window_of_field` (needs `hP3 : FppfSplitStatement`): every closed
  multiplicative-type subgroup `i` over a field point `Spec Fld → Spec R` is the evaluation of
  some window chart at a point of the chart. Split `i` by `hP3`, take a residue field `K` of a
  piece over the unique point, and apply `exists_window_point`. Then use the openness locus
  `V'` of `isOpen_affine`: it contains the image of `Spec K`, hence the whole one-point space
  `Spec Fld`, so the identity of `Spec Fld` admits a parameter.
- `WindowIndex R G gen V δ N₀`: the index type
  `Σ (c n : ℕ) (m : ℕ+) (k : ℕ) (s : AddCommGroup (Carrier k)), WindowDatum … (ULift (Fin c)) (Carrier k) m …`
  of all window charts on standard lattices. It lies in `Type u` because the finite part is
  encoded by `k` and `s`. `indexU`, `indexK` and `indexJ` are the chart, the subgroup family
  and its inclusion for an index.
- `coversFieldPoints` (needs `hP3`): the window charts satisfy
  `MultiplicativeTypeSubgroupModuli.CoversFieldPoints`. This is `exists_window_of_field`,
  repackaged with the index.
- `finiteTypeChartCover_of` takes three hypotheses: `hP3`, `hsm` (smooth affine groups have
  smooth coordinate Hopf algebras) and `hW` (`W R A L` is smooth for smooth `A` and finite
  `L`). It concludes `MultiplicativeTypeSubgroupModuli.FiniteTypeChartCoverStatement`. Proof:
  over a finitely generated `ℤ`-algebra `R`, choose a finite subcomodule `V₀` generating
  `O(G)` (`FiniteSubcomodule.exists_fg_isRightSubcomodule_adjoin_eq_top`), its coaction `δ`,
  generators `gen` and a bounded presentation `N₀`
  (`HopfPointWindowExtension.exists_isBoundedPresentation`). The charts indexed by
  `WindowIndex` are open charts: `isOpenChartOnAffines` combined with
  `MultiplicativeTypeSubgroupModuli.isOpenChartOfAffines`. They cover the field points by
  `coversFieldPoints`.

## Provenance

Internal infrastructure, ported from the Library module `HomScheme.TorusChartCover`. It
assembles the charts of the proof of SGA 3, Exp. XI, Théorème 4.1, for subgroups of
multiplicative type over noetherian affine bases. The normal form of finitely generated
commutative groups is the structure theorem as stated in Mathlib.
