# Greenberg point models from a Greenberg ring scheme

- `hasGreenbergPointModel_of_ringScheme`: let `R` be a local ring with algebraically closed
  residue field and let `ℛ` be a Greenberg ring scheme of level `n`. Then every smooth affine
  group `X` over `R` satisfies `HasGreenbergPointModel R n X`, witnessed as follows:
  - `G := greenbergGroup ℛ X P`, with `eX := levelPointsEquiv`;
  - for `h : Z ⟶ X`, `GZ := greenbergGroup ℛ Z Q` and `g := greenbergMap h`;
  - naturality from `levelPointsEquiv_naturality`;
  - smoothness from `smooth_greenbergGroup`;
  - geometric connectedness from `geometricallyConnected_greenbergGroup`.
- `GreenbergRingSchemeExistence`: an internal proposition stating that Greenberg ring
  schemes exist at every positive level over every mixed-characteristic DVR with
  algebraically closed residue field. It is the output of the Witt-vector construction
  (KP §A.4; Greenberg 1961).
- `mixedCharacteristicGreenbergPointModel_of_existence`: this existence implies
  `MixedCharacteristicGreenbergPointModelStatement`.
