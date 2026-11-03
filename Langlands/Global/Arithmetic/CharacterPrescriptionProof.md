# Finite-order Hecke-character prescription with doubled exponent

Authors: Worker 53 and Worker 1232.

`Langlands.Global.finiteOrderCharacterPrescription_proof.{u}` proves the
unchanged proposition
`Langlands.Global.FiniteOrderCharacterPrescriptionStatement.{u}` from
`Langlands.Global.Arithmetic.CharacterPrescriptionStatement`.
For every number field `K : Type u`, finite set `S` of its actual finite
places, and positive common exponent `n`, continuous prescribed characters
of the selected completion unit groups and of the whole infinite idele
factor extend to an actual continuous Hecke character killed by `2 * n`.
Every finite component and the entire infinity component agree exactly
with the input. The field universe is arbitrary; no compatibility condition
is imposed.

The source is Artin and Tate, *Class Field Theory* (AMS Chelsea, 2009),
Chapter X, Section 2, Theorems 4 and 5 and their proofs, printed pp.79–80
(one-based PDF pp.88–89), with the half-power input from Chapter IX,
Section 1, Theorem 1, printed pp.65–66 (PDF pp.74–75).
The registered source is `artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The generic separation and local-product formulations are internal
deductions implementing this argument. The paired helper Markdown explains
their precise provenance and proofs.

## Arithmetic and finite-quotient construction

`prescriptionFiniteQuotient_proof.{u}` discharges the last premise of
`prescriptionFiniteQuotient_of_halfPower` using the proved
`almostEverywherePowerHalfStatement.{u}` imported from
`Langlands.Global.Arithmetic.AlmostEverywherePowerHalfProof`.
The reduction already imports the proved
`ideleClassPowerQuotientProfinite_proof.{u}` from
`Langlands.Global.Arithmetic.IdeleClassPowerQuotientProfiniteProof`.
Both are unconditional theorems about the actual number-field objects,
with their proof routes documented in their own paired Markdown.

Write `A` for the whole infinite idele factor times the selected finite
completion unit groups, and `C` for the actual idele classes. The inserted
local product maps continuously to `C`. The coordinate retraction and
half-power descent show that the preimage of `C^(2*n)` lies in `A^n`.
The quotient `A/A^(2*n)` is finite, including the real sign factors.
The quotient `C/C^(2*n)`, with its actual quotient topology, is Hausdorff,
compact and totally disconnected by the imported topology theorem.

Consequently the image of `A` in this profinite quotient is finite. For
any open finite-index subgroup `U` of `A` containing `A^n`, the generic
finite-image separation theorem constructs an open finite-index subgroup
`N` of `C` containing `C^(2*n)` whose preimage is exactly `U`. This is
`PrescriptionFiniteQuotientStatement`. The proof uses the product topology
on `A` directly and needs no identification with an image-induced topology.

## Character construction and identities

The final theorem applies
`finiteOrderCharacterPrescription_of_finiteQuotient` from
`CharacterPrescriptionAssembly`. Multiply the prescribed characters to
obtain a continuous character `θ` of `A`. Since `θ^n = 1` with `n > 0`,
its kernel `U` is open and has finite index: the character is locally
constant and factors through the finite group of complex `n`th roots
of unity.

Apply the arithmetic finite-quotient theorem to this `U`. Exact preimage
ensures that `θ` factors through the image of `A` in `C/N`. The proved
finite abelian character-extension theorem extends that character to
all of `C/N`. Since `N` is open, this finite quotient is discrete and
the extended character is continuous. Pulling it back to `C` gives an
actual Hecke character `χ`. Every `(2*n)`th power belongs to `N`, so
`χ^(2*n) = 1`.

The pullback of `χ` to `A` is exactly `θ`. Evaluation on a single finite
factor gives each prescribed finite component. Evaluation on the whole
infinite factor gives the prescribed infinity component, retaining every
real sign coordinate.

The final theorem has no arithmetic premise. Its construction uses
proved arithmetic, subgroup-separation and character-extension results,
and only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
It proves the finite-order prescription target; local arbitrary
ramification and ramified twist isolation are separate assertions.
