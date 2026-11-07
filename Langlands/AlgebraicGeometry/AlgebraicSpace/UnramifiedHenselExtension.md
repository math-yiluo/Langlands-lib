# Henselian monic extensions of complete local rings

Author: Worker 105.

Helper module (pure algebra) for the proof of Conrad's Proposition 5.2,
`Langlands.Global.AdelicSpaceLevelPointsStatement`. It contains no statement from the
literature. Conrad uses unramified extensions of the local integer rings (printed p.14); this
module supplies their henselianity for any complete local ring. Its general lemmas require
only irreducible reduction and assert locality, completeness and henselianity; they do not
assert étaleness. The application in `ProductPointsLocalLift` lifts a separable residue
extension, but uses only the finite free basis, henselianity and residue-field surjection.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.UnramifiedHensel`.

For an `O`-algebra `S` with a finite basis `b`:

- `mem_map_iff`: `x ∈ I.map (algebraMap O S)` iff every coordinate of `x` lies in `I`. One
  direction uses `Ideal.smul_top_eq_map` and induction on `I • ⊤`; the other writes `x` in the
  basis.
- `mem_pow_map_iff`: the same for `(I.map) ^ n`, via `Ideal.map_pow`.
- `isAdicComplete`: if `O` is `I`-adically complete, then `S` is complete for `I.map`.
  Congruences modulo `(I.map)^n` are coordinatewise congruences modulo `I^n`. So Hausdorffness
  and limits of Cauchy sequences are taken coordinatewise.

For a local ring `O` and a monic `m ∈ O[X]` whose reduction `reduction m` modulo the maximal
ideal is irreducible:

- `isMaximal_map`: `𝔪 · O[X]/(m)` is maximal. The quotient is `κ[X]/(m̄)` (Mathlib's
  `AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot`), a field.
- `isLocalRing`: `O[X]/(m)` is local. It is finite over `O`, so every maximal ideal lies over
  `𝔪` (`Ideal.isMaximal_under_of_isIntegral_of_isMaximal`) and contains `𝔪 · O[X]/(m)`.
- `maximalIdeal_eq`: its maximal ideal is `𝔪 · O[X]/(m)`.
- `henselianLocalRing`: if moreover `O` is complete for `𝔪`, then `O[X]/(m)` is henselian. It
  is complete for its maximal ideal by `isAdicComplete` (power basis of `AdjoinRoot`), and
  complete rings are henselian (Mathlib's `IsAdicComplete.henselianRing`).
