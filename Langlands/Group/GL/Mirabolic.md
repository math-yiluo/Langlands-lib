# The actual mirabolic matrix subgroup

Author: Worker 353.

`Langlands.GeneralLinear.mirabolic n F` is the subgroup of the existing
`Langlands.GeneralLinear (n + 1) F` whose last row is `(0, …, 0, 1)`.
The coefficient ring is an arbitrary `F : Type u` with `CommRing F`.
There is no field, nontriviality, characteristic or rank-positivity assumption.
`mem_mirabolic` is exactly the equivalence with
`∀ j, g.val (Fin.last n) j = if j = Fin.last n then 1 else 0`.
The subgroup carries the ordinary inherited group structure and topology.

This is the group P of Bernstein–Zelevinsky (1976), §5.1, printed p.44,
with the source's rank replaced by `n + 1` and indices starting at zero.
The same section defines the full upper unipotent group U inside P.
The Lean algebra generalizes those matrix definitions from local fields to
commutative rings. It constructs the subgroup laws rather than assuming them.

The implemented multiplication argument expands the last row of a matrix
product: if the first factor has the specified row, the product's last row
is the second factor's last row. Applying this identity to `g * g⁻¹ = 1`
proves closure under inverses. Identity membership is entrywise.
These are elementary implementation proofs, not additional literature claims.

`upperUnipotent_le_mirabolic` proves that the published full upper unipotent
subgroup is contained in the mirabolic subgroup. Below the last diagonal entry,
upper triangularity forces zero; the last diagonal entry is one.
Within the namespace `GeneralLinear.Mirabolic`:

- `upperUnipotent n F` is the comap of the ambient unipotent subgroup along
  the actual mirabolic inclusion. `mem_upperUnipotent` exposes this definition.
- `upperUnipotentEquiv` identifies this subgroup with the original
  `GeneralLinear.upperUnipotent (n + 1) F`. Both directions retain the same
  matrix, adding or forgetting the redundant membership certificate. The
  two `_val` lemmas record this exactly.
- `rankOne_eq_one` proves every element of `mirabolic 0 F` is the identity,
  by equality of its sole matrix entry. `rankOneSubsingleton` records the
  resulting instance; rank one is not excluded.
- `entry` is continuous matrix-entry evaluation for any coefficient topology.
  `upperUnipotentContinuousEquiv` upgrades the same unipotent identification
  to an equivalence preserving both inherited topologies.
- `isClosed`, assuming only `TopologicalSpace F` and `T2Space F`, proves
  closedness as an intersection of closed entrywise equations.
  `upperUnipotent_isClosed` is the preimage of the published ambient
  unipotent closedness theorem. `locallyCompactSpace` deduces local compactness
  if the ambient general linear group is locally compact.

These topology laws are derived implementation facts. Under
`IsTopologicalRing F`, the already existing matrix-unit and subgroup instances
supply topological group structures; this module introduces no substitute group
or topology. The inherited-topology facts above need even fewer hypotheses.

No semidirect-product decomposition, derivative functor, or minimality theorem
is asserted. The existing modules, including the Kirillov statement pair,
are unchanged.

Source: I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
GL(n,F) where F is a non-Archimedean local field*, Russian Math. Surveys 31:3
(1976), 1–68, registered as `bernstein-zelevinsky-1976-representations-gln`.
The retained Central-Library PDF has SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Sections 5.1–5.7, printed pp.44–45 (zero-based PDF indices 43–44), were read;
§5.1 supplies this module's group definitions. No relevant erratum was found
in the available literature or public notes.
