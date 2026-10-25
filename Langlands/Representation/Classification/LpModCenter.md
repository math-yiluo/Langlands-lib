# A fixed real exponent for coefficients modulo the center

Authors: Worker 403 and Worker 158, who agreed the shared interface for the
block tensor comparisons.

This module adds two predicates. `Langlands.IsLpModCenter ρ μ r` means that
`ρ` is admissible and admits a smooth unitary central character `c` such that
every descended absolute matrix coefficient `c.coefficientNorm ℓ v` belongs to
`MemLp` at exponent `ENNReal.ofReal r` for the supplied Haar measure `μ`.
Here `ℓ` ranges over the actual smooth dual and `v` over the entire carrier.
The group and carrier universes are independent. The carrier is only an
algebraic complex module; it has no topology or countability assumption.

The quotient is the actual `G / Subgroup.center G` with its supplied measurable
space. The generic definition retains the same weak topological hypotheses as
`IsTemperedModCenter`: a group with a topology suffices to state it. The measure
is required to be Haar. A Borel structure and a topological group instance are
not additional hypotheses of this definition. The real parameter is unrestricted;
its conversion by `ENNReal.ofReal` sends nonpositive values to zero.
The common tensor comparison will separately restrict to `r ≥ 2`.

For a supplied compatible p-adic realization `T`,
`Langlands.PadicField.TopologicalData.IsLp ρ r` quantifies over every Haar measure
on the canonical Borel measurable space of the actual central quotient of
`GL_n(F)`, using `T.topology`. This follows the existing `T.IsTempered` and
`T.IsSquareIntegrable` conventions. The field and carrier universes remain
independent, and every natural rank, including zero, is allowed. No Haar
normalization, central character or coefficient functional is preselected.

The intrinsic lemma `isLpModCenter_two_iff` identifies the new fixed-exponent
predicate at `r = 2` with the existing `IsSquareIntegrableModCenter`. It unfolds
both definitions and uses `ENNReal.ofReal_ofNat`. It assumes the Borel and
topological group instances needed to state the existing square-integrability
predicate. The canonical GL lemma `T.isLp_two_iff` installs the same topology
and Borel instances as both existing GL predicates and applies this equivalence
under each of their measure quantifiers.

This is internally derived interface content. Its provenance is the accepted
Library definitions in `Classification/Tempered` and
`MatrixCoefficient/ModuloCenter`; it is not a newly asserted literature
theorem. In particular the central character is existentially quantified as in
those definitions, and the coefficients use the existing quotient construction.
The module proves the two exponent-two identifications only. It provides no
tensor comparison, character-existence theorem, Haar-transport argument,
integrability estimate or temperedness equivalence.
