# Topology of the actual normalized local-field maps

Author: Worker 200.

This is a derived topology target for the local-field adapters used in
Waldspurger's rational-character norms. Renard, *Représentations des groupes
réductifs p-adiques*, 9 July 2026 edition, V.1, printed p.103 (PDF p.109),
fixes the topology, the normalized order and `|a|_F = q^(−v_F(a))`.
V.2.3, printed pp.105–106 (PDF pp.111–112), uses these maps in the
rational-character valuation and proves smoothness of rational norm
characters. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Waldspurger 2003, I.1, printed pp.239–240 (PDF pp.5–6), uses the actual
normalized absolute value and the negative exponent in defining `H_G`;
its registered source is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

`Langlands.Plancherel.FieldUnitsTopologyStatement` quantifies over
`F : Type uF` with `Field F`, `ValuativeRel F`, `TopologicalSpace F` and
`IsNonarchimedeanLocalField F`. This is the existing characteristic-independent
local-field interface. Its topology comes from the given valuative relation;
no new topology or uniform structure is selected. The unit-group topologies
are the standard ones induced by the existing field and nonnegative-real
topologies. The integer target `Multiplicative ℤ` has the usual discrete
topology inherited from `ℤ` through the type tag.

The conclusion has five components:

- `LocalField.residueNormalizedAbsoluteValue F : F → ℝ` is continuous,
  including at zero.
- `fieldOrderUnits F : Fˣ →* Multiplicative ℤ` is locally constant.
- The same integer-order map is continuous.
- `fieldNormUnits F : Fˣ →* ℝ≥0ˣ` is locally constant.
- The same positive norm map is continuous.

These are the actual maps already constructed in
`Langlands.LocalField.ResidueNormalization` and
`Langlands.Representation.Plancherel.LocalFieldUnits`. The residue cardinality
and normalized valuation are their existing values; no positive-character
family or scale is supplied as a free parameter. Local constancy is asserted
only on `Fˣ`, and makes no claim that the absolute value is locally constant
at zero. Neither characteristic nor field universe is restricted.

The intended proof uses the valuative topology: away from zero, a sufficiently
small valuative ball has constant valuation. The existing order/valuation
comparison then gives local constancy of the integer order, and the proved
normalization gives local constancy of the units norm. Locally constant maps
are continuous. Continuity of the absolute value at zero uses its actual
residue-cardinality normalization and the corresponding small valuative
balls. These are proof suggestions, not proofs included in this statement
unit; another verified proof route is permitted.

This target supplies no rational-point topology and proves no continuity of
an algebraic character evaluation. Those belong to the shared group-scheme
and rational-point topology chain. Once evaluation continuity is proved,
composition with the units norm gives the continuity and local constancy
required for the actual rational norm characters. Common-kernel topology,
image-lattice rank and index, split-center comparisons, character tori and
Haar measures remain separate obligations. The conclusions of this target
are deductions to prove, not new structural hypotheses of the conditional
Plancherel theorem. This unit publishes a Prop-valued statement only.
