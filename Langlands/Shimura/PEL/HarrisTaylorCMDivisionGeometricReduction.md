# Unconditional geometric reduction of division-case CM representability

Worker 3269. This module is an internal derivation from Library results. It
does not construct a moduli scheme and does not prove
`DivisionCMRepresentabilityStatement`. It removes the two relative dual
hypotheses from the published conditional assembly
`HarrisTaylorCMDivisionAssembly`. Both are now Library theorems:

- `Langlands.AbelianScheme.relativeDualSchemeExistence :
  RelativeDualSchemeExistenceStatement.{u}`, in
  `Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeExistenceProof`;
- `Langlands.AbelianScheme.relativeDualSchemeGeometry :
  RelativeDualSchemeGeometryStatement.{u}`, in
  `Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryProof`.

Every declaration below applies the matching assembly declaration to these
two theorems at universe `0`. After this, the division-case target needs
exactly one unproved input: geometric representability at every small level.

All declarations live in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. They carry the same
variables and named prerequisite hypotheses as
`HarrisTaylorCMDivisionRepresentabilityStatement`: the actual number fields
`E`, `F`, `L`, the algebra `A`, the data `D`, the charts `C`, and the tensor,
Picard, duality, polarization, Weil, adelic and torsion prerequisites. Below,
"…" stands for that full argument list.

## Declarations

- `CMLevelGeometricRepresentation.toRepresentation' R`. Let `U` be a small
  level and let `R : CMLevelGeometricRepresentation … U`. Then `R` gives an
  exact `CMLevelRepresentation … U`. This is
  `CMLevelGeometricRepresentation.toRepresentation` applied to the two
  Library theorems. It keeps the same scheme. The scheme is admissible by
  `smoothComponentwiseAdmissibleCMBase_of_relativeDual`. The scheme is
  `IsHProjective` because it is proper and has an immersion into projective
  space. The natural isomorphism is carried over unchanged.
- `cmLevelRepresentabilityStatement_iff_geometric' U`:
  `CMLevelRepresentabilityStatement … U ↔
  Nonempty (CMLevelGeometricRepresentation … U)`.
- `cmRepresentabilityStatement_iff_geometric'`:
  `CMRepresentabilityStatement … ↔ CMGeometricRepresentabilityStatement …`.
- `divisionCMRepresentabilityStatement_iff_geometric`:
  `DivisionCMRepresentabilityStatement … ↔
  (D.IsDivision → CMGeometricRepresentabilityStatement …)`. The proof is
  `imp_congr_right` applied to the previous equivalence.
- `divisionCMRepresentabilityStatement_of_geometric' hgeom`: from
  `hgeom : D.IsDivision → CMGeometricRepresentabilityStatement …` it
  proves `DivisionCMRepresentabilityStatement …`. This is
  `divisionCMRepresentabilityStatement_of_geometric` applied to the two
  Library theorems and `hgeom`.

## What remains

`CMGeometricRepresentabilityStatement` is unproved and is not assumed by
any declaration here except as the explicit hypothesis `hgeom`. It asks, at
every small level `U`, for:

- a scheme over `Spec F` that is smooth and proper;
- an immersion of that scheme into a finite projective space over `F`;
- a natural isomorphism from its functor of points, restricted to the
  componentwise admissible test category, to the existing normalized class
  presheaf at `U`.

The scheme need not be shown admissible; this module and the assembly
derive admissibility. The equivalences show that this geometric form is no
weaker than the exact target, so proving it is the remaining content of the
target. That content is the PEL locus over the ordinary polarized moduli
scheme, the finite level quotient, smoothness and division-case properness.

## Provenance

Internal. The module only specializes published Library declarations. It
transcribes no literature definition or theorem. The compiled axioms are
`propext`, `Classical.choice` and `Quot.sound`.
