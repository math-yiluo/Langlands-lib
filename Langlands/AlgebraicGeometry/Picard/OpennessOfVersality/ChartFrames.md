# Framed covers and lifted transition functions over a square-zero thickening

Module `Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.ChartFrames`, namespace
`Langlands.AlgebraicGeometry.Picard.OpennessOfVersality`. Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`, openness of versality for actual Picard
families). Everything is proved in the file, with no hypotheses beyond those in the
signatures. Internal construction; no literature statement is formalized.

The module produces the chart data used by `exists_lift` (`Sufficiency`),
`hasBaseLiftingForAt_of_HOneVanishes` (`BaseLifting`) and `exists_versal_basicOpen`
(`ChartOpenness`) from an arbitrary line bundle.

## Relative spaces of nilpotent thickenings

For `f : X ⟶ Spec R` and an `R`-algebra map `q : A →ₐ[R] B` (relative spaces
`relSpace f A = Spec A ×_R X`, Library `RelativeAffineSections`):

- `isClosedImmersion_relMap` (q surjective): `relMap f q` is a closed immersion (base
  change of `Spec B ⟶ Spec A`).
- `exists_open_preimage_le` (q surjective): every open neighbourhood `T` of a point `y` of
  `relSpace f B` contains `relMap f q ⁻¹ᵁ T'` for an open neighbourhood `T'` of the image
  of `y` (the complement of the image of the closed set `Tᶜ`).
- `surjective_relMap_of_isNilpotent` (q surjective, `ker q` nilpotent): `relMap f q` is
  surjective.
- `exists_frameCover_relMap` (same hypotheses, `relSpace f A` compact): for a line
  bundle `L` on `relSpace f B` there is a finite ordered affine cover `K` of
  `relSpace f A` such that `L` has a frame on each `relMap f q ⁻¹ᵁ K.U i`. The proof
  follows the Library's `BiCech.exists_frameCover`: the affine opens of `relSpace f A`
  whose preimages carry frames form a basis (by the two previous lemmas and
  `exists_isFrameOn_of_isLocallyFreeRankOne`), and compactness gives a finite subcover.
- `exists_units_lift`: for an affine open `V` of `relSpace f A`, every unit of the
  sections of `relSpace f B` over `relMap f q ⁻¹ᵁ V` is the image of a unit over `V`
  (sections form a pushout, `isPushout_sections`; the map is surjective with nilpotent
  kernel, `nilpotentSurjective_of_isPushout`; units lift, `unitsMap_surjective`).

## Chart data

For an `R`-algebra `P`, a `P`-algebra `A₀` (with `IsScalarTower R P A₀`) and an ordered
affine cover `K` of `relSpace f P`:

- `isAffineOpen_cover_inf` (`f` separated): `K.U i ⊓ K.U j` is affine.
- `secMap_defect_eq_zero`: if the family `g` of units on the pairwise intersections of `K`,
  pushed to `relSpace f A₀` (`pushUnits f K (relMap f ι₀) (testCover f K A₀).U _ g`), is a
  cocycle, then the base change (`secMap`) of `defect f K g s` (the multiplicative
  coboundary minus one, published `Obstruction`) vanishes for every `s : K.Idx 2`.
- `exists_chartFrames` (`f` separated, `relSpace f P` compact, `algebraMap P A₀`
  surjective with nilpotent kernel): for every line bundle `L₀` on `relSpace f A₀` there
  are a finite ordered affine cover `K` of `relSpace f P`, frames `e i` of `L₀` on the
  pieces `(testCover f K A₀).U i`, and units `g i j` on `K.U i ⊓ K.U j` such that
  `CocycleGluing.IsTransition e (pushUnits … g)` (the frames have the pushed units as
  transition functions) and `defect f K g s ∈ (ker (algebraMap P A₀)).map
  (structureHom f P (K.inter s))` for all `s`.

  Proof: take `K` from `exists_frameCover_relMap` and the frames from it; lift the
  transition functions `CocycleGluing.frameCocycle e he i j` with `exists_units_lift`;
  the pushed family then equals `frameCocycle`, so it is a transition family
  (`isTransition_frameCocycle`) and a cocycle (`isCocycle_of_isTransition`); the defect
  lies in the extension of the kernel by `ker_appLE_eq_map` (Library) and
  `secMap_defect_eq_zero`.
