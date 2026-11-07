# The window charts cover the field points

Author: Worker 1421.

This is an internal module for task `45ac6e52-a4d8-4414-91f1-03c3be35223e`. It
assembles the window charts into a chart cover over every affine base
`Spec R` of finite type over `ℤ`. Its main theorem, `finiteTypeChartCover_of`,
proves the Library's `TorusSubgroupModuli.FiniteTypeChartCoverStatement`
from three hypotheses:

- the étale splitting statement `EtaleSplitStatement`
  (`TorusChartOpen`);
- smoothness of the coordinate Hopf algebra of every smooth affine group over
  an affine base;
- smoothness of every representing algebra `W R A r m` of homomorphisms
  `μ_m^r → Spec A`, for `A` a smooth Hopf algebra.

The final module `SmoothTorusSubgroupRepresentabilityProof` discharges all
three with Worker 950's published results.

## Lemmas

- `exists_fieldPoint`: an algebra with a prime ideal has a point with values
  in a field (its residue field).
- `exists_lift_Bf`: let `y` be a field point of `W_f` at which `N` does not
  vanish. Then `y` extends to `B_f = (W_N)_f` along `uS`. Factor through `W_N`
  and then through its localization at `f`.
- `stdLattice I : ℤ^I ≅ ℤ^{ULift (Fin |I|)}`, the identification of the
  character lattice of a finite type with a standard lattice (through
  `Fintype.equivFin`). Standard lattices keep the index type of the charts in
  universe `u`.
- `exists_window_point`: let `bk : Spec C → T` be a piece of an étale
  splitting of `i`, on which `i` is the closed split torus of a Hopf point
  `fk` of rank `I`, and let `x' : C → K` be a field point. Then there is a
  window datum on the standard lattice of rank `|I|`, and a point `yK` of its
  `B_f`, at which the chart's evaluation equals the evaluation of `i` at
  `specMap x' ≫ bk`. Proof:
  1. Push `fk` to `K`, and transport it to the standard lattice by
     `stdLattice`. This gives a closed-immersion Hopf point `α₀` over `K`.
  2. `TorusChartExistence.exists_windowDatum` gives a window datum `dw` and a
     point `y` of `W_f` with `y N ≠ 0` specializing `dw.α` to `α₀`.
     `exists_lift_Bf` extends `y` to `yK`.
  3. Compare the evaluations: `evaluate_j_comp_pOver`,
     `evaluate_iS_specMap`, `evaluate_comp_of_eq_range` and `range_twist_eq`
     (for the transport along `stdLattice`).
- `exists_window_of_field` (needs `hP3`): for every field point
  `x : Spec F → Spec R` and every closed relative-torus subgroup `i` of `G`
  over `Spec F`, some window chart has a point `a : Spec F → U` with
  `evaluate j a = range i`. Proof:
  1. Split `i` étale-locally by `hP3`, choose a piece through the unique
     point of `Spec F`, and a field point `x'` of that piece
     (`exists_fieldPoint`).
  2. `exists_window_point` gives a chart parameter over `Spec K` matching `i`
     pulled back along the piece.
  3. By openness (`TorusChartOpen.isOpen_affine`), the open set `V'` where
     `i` is an evaluation of the chart contains the image of `Spec K`. This
     image is the unique point of `Spec F`, so `V'` is everything, and `i`
     itself is an evaluation (`evaluate_id`).

## Assembly

- `WindowIndex R G gen V δ N₀`: the type of all window data on standard
  lattices, `Σ (c n : ℕ) (m : ℕ+), WindowDatum … (ULift (Fin c)) m gen n V δ N₀`.
  It lies in universe `u`.
- `coversFieldPoints` (needs `hP3`): the charts `j G d` indexed by
  `WindowIndex` satisfy the Library's `TorusSubgroupModuli.CoversFieldPoints`.
  This is `exists_window_of_field`.
- `finiteTypeChartCover_of (hP3) (hsm) (hW)`:
  `FiniteTypeChartCoverStatement.{u}`. Let `R` be of finite type over `ℤ` and
  `G` a smooth group over `Spec R` with affine structure map. Then:
  1. `G` is affine (`isAffine_of_isAffineHom`), and its coordinate Hopf
     algebra `A` is smooth by `hsm`, hence finitely presented. `R` is
     noetherian (`Algebra.FiniteType.isNoetherianRing`).
  2. Choose a finitely generated right subcomodule `V₀ ⊆ A` generating `A` as
     an algebra (`FiniteSubcomodule.exists_fg_isRightSubcomodule_adjoin_eq_top`),
     with its coaction `δ` (`HopfPointWeightWindow.exists_coaction`).
  3. Take a finite generating set `s` of `V₀`. The elements of `s` generate
     `A` as an algebra and lie in `V₀`, and they form a bounded presentation
     of some degree `N₀ ≥ 1`
     (`HopfPointWindowExtension.exists_isBoundedPresentation`).
  4. Index the charts by `WindowIndex`. Each chart is an open chart: it is an
     open chart on affine tests by `TorusChartOpen.isOpenChartOnAffines`
     (with `hW` providing smoothness of `W`), and the Library's
     `TorusSubgroupModuli.isOpenChartOfAffines` upgrades this. The charts
     cover the field points by `coversFieldPoints`.
