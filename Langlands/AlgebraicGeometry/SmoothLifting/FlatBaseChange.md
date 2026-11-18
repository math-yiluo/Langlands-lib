# Flat base change of modules of lifts

Namespace `Langlands.AlgebraicGeometry.SmoothLifting`.

- `isBaseChange_of_isLocalized_span` says that base change is local. It
  is pure algebra. The data are:
  - an `R`-algebra `B`, an `R`-module `M`, and an `R`-linear map
    `φ : M → N` into a `B`-module `N`;
  - a set `s ⊆ R` spanning the unit ideal;
  - for each `r ∈ s`, a localization `B_r` of `B` at `r` and a
    `B`-linear map `ℓ_r : N → N_r` that localizes `N` at the powers of
    `r`.

  If every `ℓ_r ∘ φ` is a base change to `B_r`, then `φ` is a base change
  to `B`. The proof uses Mathlib's `bijective_of_isLocalized_span` for the
  map `B ⊗[R] M → N`.
- `isLift_bc_iff`: base-change the data first to `R'` and then to an
  `R'`-algebra `T`. Lifts of this data on `T` are exactly lifts of the
  original data on `T`.
- `LiftModule.isBaseChange_resLin` (assumes `[Smooth f]`): for square-zero
  data over `C`, a base lift `e`, and a flat `C`-algebra `B`,
  `IsBaseChange B (LiftModule.resLin B hI e)`.

  Proof. Take a finite chart cover with elements `gᵢ` spanning `C`, and
  set `r = gᵢ`.
  - On the `C` side, `LiftModule.isLocalizedModule_resLin` makes
    restriction to `C[1/r]` a base change.
  - `Chart.isBaseChange_resLin` applies to the chart `gᵢ`, base-changed to
    `C[1/r]`, where `gᵢ` is a unit. It gives the base change from
    `C[1/r]` to `B[1/r]`, which is flat over `C[1/r]`.
  - Composing and transporting with `LiftModule.equivOfIff`
    (via `isLift_bc_iff`) gives the required localized base change.
  - On the `B` side, restriction to `B[1/r]` is again
    `isLocalizedModule_resLin`, applied to the base-changed data.

  The proof sets `maxHeartbeats 1600000` because elaborating the
  application of the abstract lemma is slow.

Provenance: internal to Task 6989 (Worker 496). The geometric content is
that lifts form a quasi-coherent module, locally `Hom(ω, I)` with `ω`
finitely presented (compare Stacks 02H6). Such a module commutes with flat
base change.
