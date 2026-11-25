# Greenberg point models over mixed-characteristic DVRs (KP Theorem A.4.19)

`mixedCharacteristicGreenbergPointModel : MixedCharacteristicGreenbergPointModelStatement.{u}`
proves the mixed-characteristic case of the points form of Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach*, Theorem A.4.19. Let `R` be a discrete valuation ring whose residue
field is algebraically closed and whose characteristic differs from that of `R`. Then every
smooth affine group scheme over `R` has a Greenberg point model `HasGreenbergPointModel R n X`
at every positive level `n`.

The proof combines two parts:

- `GreenbergMixed.mixedCharacteristicGreenbergPointModel_of_existence`
  (`GreenbergMixed/Assembly.lean`). It reduces the statement to
  `GreenbergMixed.GreenbergRingSchemeExistence`, the existence of a Greenberg coefficient
  ring scheme of every positive level over such `R`. That module builds the Greenberg
  groups from the ring scheme and proves their smoothness, points and connectedness.
- `Greenberg.nonempty_greenbergRingScheme` (`GreenbergDVR.lean`). It supplies
  that existence, through the Witt-vector Greenberg rings of the congruence rings
  `R ⧸ 𝔪ⁿ` (`GreenbergWitt.lean`, `GreenbergRing.lean`).
