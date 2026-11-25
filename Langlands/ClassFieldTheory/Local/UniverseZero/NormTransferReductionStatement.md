# The transfer equation from norm compatibility

This module defines one closed proposition,
`Langlands.LocalClassField.UniverseZero.NormCompatibleTransferStatement`, with universe
parameters `u`, `v`, `w`. It imports only the Library's
[`FiniteReciprocityStatement`](../FiniteReciprocityStatement.lean), which it
does not change. It is a statement target, not a proof, and it constructs no
reciprocity map.

## Exact content

The binders are exactly the binders of the Library proposition
`Langlands.LocalClassField.FiniteAbelianNormTransfer`, in the same order:

- every prime `p` (with `Fact p.Prime`);
- `F : PadicField.{u} p`, `E : PadicField.{v} p`, `L : PadicField.{w} p`;
- the three algebra structures `F → E`, `F → L`, `E → L`, the three scalar
  towers over `Padic p` and the tower `F → E → L`;
- finite dimension of `E/F`, `L/F` and `L/E`, and `IsAbelianGalois F L`;
- arbitrary supplied `TF : F.TopologicalData` and `TE : E.TopologicalData`.
  Their topologies, `TF.topology` and `TE.topology`, give the quotient
  topologies on the two norm quotients, exactly as in `FiniteAbelianNormTransfer`.

The proposition then quantifies over **every** pair of continuous multiplicative
equivalences

- `rF : Fˣ ⧸ range (Units.map (Algebra.norm F (S := L))) ≃ₜ* Gal(L/F)`,
- `rE : Eˣ ⧸ range (Units.map (Algebra.norm E (S := L))) ≃ₜ* Gal(L/E)`.

These are the types of the two existential witnesses of `FiniteAbelianNormTransfer`. The proposition
asserts an implication. Suppose the pair satisfies its norm clause: for
every `a : Eˣ`,

`rF [N_{E/F}(a)] = (rE [a]).restrictScalars F`,

where `N_{E/F}` is `Units.map (Algebra.norm F (S := E))`. Then it satisfies
the transfer clause of `FiniteAbelianNormTransfer`: for every `a : Fˣ`,

`(rE [a_E]).restrictScalars F = (rF [a]) ^ Module.finrank F E`.

Here `a_E` is `Units.map (algebraMap F E).toMonoidHom a`, `[·]` is
`QuotientGroup.mk`, and `restrictScalars F` is the inclusion
`Gal(L/E) → Gal(L/F)`. Both clauses are copied verbatim from
`FiniteAbelianNormTransfer`: the same norm range, the same `Units.map`
expressions, the same scalar restriction and the same degree
`Module.finrank F.Carrier E.Carrier`.

The two maps go in opposite directions. The norm goes from `Eˣ` to `Fˣ` and
corresponds to the inclusion of Galois groups. Scalar inclusion goes from `Fˣ`
to `Eˣ`; once the result is pushed into `Gal(L/F)`, it corresponds to the
`[E:F]`-th power, which is the transfer of an abelian ambient group. The
proposition does not identify the transfer with a restriction map.

## Purpose and use

This proposition and a proof of it reduce the Library's norm/transfer target to its norm clause.
Suppose a proof of `FiniteAbelianNormTransferTypeZeroStatement` (that is,
`FiniteAbelianNormTransfer.{0, 0, 0}`) supplies the named NYLL quotient
equivalences and proves their norm clause. Then this proposition, at universes
`0, 0, 0`, gives the transfer clause for the same pair. No new witness is chosen.
The proposition is stated with independent universes so that the arbitrary-universe
assembly can also use it.

The proposition says nothing about how `rF` and `rE` are obtained. It does
not assert that any such pair exists. It does not assert the norm clause, a
normalization, an inertia property or uniqueness, and it does not compare
with `geometricReciprocityOfCup` or any cohomological transfer. Its hypotheses
`TF`, `TE`, the scalar towers over `Padic p` and `IsAbelianGalois F L` are
kept only so that the binders match the Library proposition exactly; the
proof in `NormTransferReductionProof` does not use the abelian hypothesis or the valuation data.

## Provenance

This is a derived internal target, a step of the universe-zero norm and
transfer compatibility: the norm of an included scalar, `a` raised to
`Module.finrank F.Carrier E.Carrier`, establishes the Library's transfer equation
after restricting scalars. This proposition states exactly that step. The
mathematical fact behind it is elementary: for a finite extension `E/F` and
`a ∈ F`, `N_{E/F}(a) = a^{[E:F]}`, which is Mathlib's
`Algebra.norm_algebraMap`. Apply the norm clause to the included unit `a_E`, then
use that `QuotientGroup.mk` and `rF` are multiplicative. This gives the
transfer clause.

The source correspondence of the two clauses is recorded in the
[companion Markdown](../FiniteReciprocityStatement.md) of `FiniteReciprocityStatement`. It cites Serre,
*Local Fields* (1979), registered as `serre-1979-local-fields`, XIII.4
Proposition 10(a)–(b) for the norm/inclusion and inclusion/transfer diagrams,
and VII.8 Propositions 7–8 for the abelian transfer power formula; those
passages were read for that pair. This module adds no new
source claim and makes no reading of its own. The implication as an
interface statement is an internal formalization choice and is not attributed
to Serre.

## Dependencies

The only import is `Langlands.ClassFieldTheory.Local.FiniteReciprocityStatement`,
which is published. Mathlib supplies `Algebra.norm`, `Units.map`,
`QuotientGroup.mk`, quotient topologies, `ContinuousMulEquiv`,
`AlgEquiv.restrictScalars` and `Module.finrank`. The checks used
Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. A development check
of this module succeeds with no diagnostics and reports a `Prop`-valued
definition with universe parameters `u`, `v`, `w`.
