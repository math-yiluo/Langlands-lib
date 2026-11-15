# Renard IV.3.2: failure of the criterion without irreducibility

Author: Worker 1222. This statement unit defines
`Langlands.Renard.CompactRepresentation.NonirreducibleSquareIntegrabilityCounterexampleStatement`.
It supplies no counterexample construction or proof.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, IV.3.2, Remark, printed p.100 / PDF p.106. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original IV.3.1–IV.3.2 passage, printed pp.99–100 / PDF pp.105–106, was read
directly for this unit.

After asserting that one nonzero square-integrable smooth matrix coefficient
suffices for an irreducible smooth representation with unitary central
character, Renard explicitly says that this fails without irreducibility. He
leaves the proof of the Remark to the reader. This second assertion is a
separate source obligation from the positive irreducible criterion.

IV.3.1 assumes a unimodular t.d. group and uses a bi-invariant Haar measure on
its actual quotient by the center. The statement retains the Hausdorff, locally
compact, totally disconnected group hypotheses. A Borel Haar measure `ν` on
`G` that is also right invariant explicitly witnesses the ambient
unimodularity. The coefficient condition uses a separate bi-invariant Borel
Haar measure `μ` on the actual quotient, as in the published single-coefficient
statement. No normalization relates the two measures.

## Exact proposition

The Lean proposition negates the following universal implication. For every
group `G` with these topology hypotheses and a bi-invariant Borel Haar
measure `ν`, every Borel Haar measure `μ` on `G / Z(G)` that is also right
invariant, every bundled smooth complex
representation `π` that is not irreducible, and every actual unitary central
character `c`, if some smooth matrix coefficient is nonzero as a function on
`G` and its descended norm belongs to `L²(μ)`, then
`π.IsSquareIntegrableModuloCenter μ`.

Classically this is the existence assertion that such data can be chosen with
a nonzero square-integrable coefficient but with
`¬ π.IsSquareIntegrableModuloCenter μ`. The conclusion uses the published
source predicate, which does not contain admissibility or irreducibility.
Thus its failure concerns coefficient integrability itself.

The central character includes the actual scalar action of the center, an open
kernel and unit norm. The function tested by `MemLp` is
`c.coefficientNorm ℓ x : G / Z(G) → ℝ`, the norm of the actual smooth matrix
coefficient. The coefficient itself need not descend for a nontrivial central
character. `MemLp` with exponent `2` includes almost-everywhere strong
measurability as well as finiteness of the L² seminorm. To prove failure of the
all-coefficients predicate, a bad coefficient for one central-character datum
suffices: `UnitaryCentralCharacter.coefficientNorm_eq` proves independence
from that choice.

Both the group and representation carrier lie in `Type 0`. This is an
existence assertion requiring one ordinary small counterexample; it does not
restrict the independent universes of any universal representation theorem.
The carrier has no topology. There are no admissibility, reductivity,
finite-dimensionality, finite-length or countability hypotheses.

## Dependencies and status

The unit imports the published smooth representation category, smooth dual,
matrix coefficients, actual central quotient, unitary central characters and
raw square-integrability predicate through
`Langlands.Representation.MatrixCoefficient.SmoothSquareIntegrability`.
It introduces no replacement objects or additional assumed mathematical laws.

The positive proposition
`Langlands.Renard.CompactRepresentation.SingleCoefficientSquareIntegrabilityStatement`
and its exact proof Task 6678 (`cf5dbeda-85bf-4ad9-8db5-f2f1445f4dc8`) remain
separate and unchanged. This statement does not prove that positive proposition
or its own counterexample assertion. Independent statement review and
publication, followed by a separate exact proof task, remain required.
