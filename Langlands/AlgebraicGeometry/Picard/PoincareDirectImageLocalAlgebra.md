# Local algebra for the Poincaré direct image

Author: Worker 975.

Module `Langlands.AlgebraicGeometry.Picard.PoincareDirectImageLocalAlgebra`, namespace
`Langlands.AbelianScheme.PoincareDirectImage`. This is an internal helper module for the proof
of `Langlands.AbelianScheme.AlgClosedFieldPoincareDirectImageStatement`. It contains only
commutative algebra and homological algebra of module complexes; it imports no
algebraic geometry. Everything is proved in the file, with no hypotheses beyond the
signatures. The results are standard facts, derived here from Mathlib; no literature
statement is formalized. All rings and modules live in one universe `u`.

## First-order thickenings are dual numbers

Let `R` be a local ring that is an algebra over a field `K`, and let `J` be an ideal with
`m² ≤ J ⋖ m`, where `m` is the maximal ideal of `R`.

- `dualNumberHom J e he` is the `K`-algebra map `K[ε] ⟶ R ⧸ J` sending `ε` to the class of
  `e`, for `e` with `e * e ∈ J`. It is built with Mathlib's `DualNumber.lift`, and
  `dualNumberHom_apply` gives its value on `a + bε`.
- `nonempty_dualNumber_algEquiv`: if `algebraMap K (ResidueField R)` is bijective, then
  `R ⧸ J ≅ K[ε]` as `K`-algebras. The proof picks `e ∈ m ∖ J`. Since `J ⋖ m`, this gives
  `m = J ⊔ (e)`. The map `dualNumberHom J e` is injective: reducing modulo `m` kills the
  constant term, and a nonzero multiple of `e` would put `e` in `J`. It is surjective:
  write `r ≡ a` modulo `m`, then `r - a ∈ J + (e)`, and replace the coefficient of `e` by
  its residue, using `m² ≤ J`.

## Residue fields of localizations

- `algebraMap_residueField_surjective_of_isLocalization`: if `S` is the localization of
  `B` at a maximal ideal `p`, every element of the residue field of `S` comes from `B`.
  For `r / u`, choose `v` with `v u ≡ 1` modulo `p`; then `r / u ≡ r v`.
- `bijective_algebraMap_residueField`: let `κ : K →+* B` have a retraction `ev` with
  kernel `p`, and let `S` be a `K`-algebra through `B`. Then `K` maps bijectively onto the
  residue field of `S`, since every `b` is congruent to `κ (ev b)` modulo `p`.

## Supports and annihilators

- `exists_pow_smul_eq_zero`: if every element of a finite module is killed by some power
  of `f`, one power kills the whole module (take the largest exponent over a finite
  generating set).
- `exists_pow_le_annihilator`: over a noetherian ring, if each `f ∈ m` acts nilpotently
  on each element of a finite module `M`, then `m^N` kills `M` for some `N`. This is
  Mathlib's `Ideal.exists_pow_le_of_le_radical_of_fg`.
- `map_annihilator_le`: the image of the annihilator of `M` under `φ : B →+* S` kills the
  scalar extension `S ⊗_B M`.
- `exists_smul_eq_zero_of_isZero` and `exists_pow_smul_eq_zero_of_isZero`: if the scalar
  extension of `M` to a localization at a submonoid `T` (respectively to `B_f`) vanishes,
  every element of `M` is killed by an element of `T` (respectively a power of `f`). The
  proof views `M ⟶ A ⊗_B M` as a localization map with Mathlib's
  `isLocalizedModule_iff_isBaseChange`.
- `isZero_of_pow_le_annihilator`: let `m` be maximal and `R` the localization at `m`. A
  module killed by `m^N` whose localization at `m` vanishes is zero. For each element,
  its annihilator contains `m^N` and an element outside `m`, so it is the whole ring.
- `nonempty_iso_quotient_of_pow_le_annihilator` (with the generic version
  `nonempty_iso_quotient_of_pow_le_annihilator'`): a module killed by `m^N` whose
  localization at `m` is isomorphic to the residue field is isomorphic to `B ⧸ m`.
  Elements outside `m` act invertibly on such a module, so `M ⟶ R ⊗_B M` is bijective.
  The residue field of `R` is `B ⧸ m` as a `B`-module.

## Homology of complexes

Here `baseChange` is the Library's degreewise scalar extension
`Langlands.Cohomology.ModuleComplex.baseChange`.

- `nonempty_baseChange_homology_iso_of_flat`: for a flat ring map `φ`, the homology of
  `φ`-extended complexes is the `φ`-extension of the homology. The proof uses Mathlib's
  `ModuleCat.preservesFiniteLimits_extendScalars_of_flat` and
  `ShortComplex.mapHomologyIso`; scalar extension is a left adjoint, so it also preserves
  finite colimits.
- `finite_homology`: over a noetherian ring, a strictly perfect complex has finite
  homology modules.
- `exists_pow_le_annihilator_homology`: let `Kc` be strictly perfect over a noetherian
  ring `B`. Suppose the homology of `Kc ⊗ B_f` vanishes for every `f ∈ m`. Then a power
  of `m` kills every homology module of `Kc`.
  `exists_pow_le_annihilator_homology_localization` gives the same conclusion for
  `Kc ⊗ R`, with `R` the localization at the prime `m` and the maximal ideal of `R` in
  place of `m`.
