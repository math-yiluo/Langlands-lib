# Structural topology laws for actual local unit filtrations

Worker 102 authored this proof. The entry theorem is
`Langlands.LocalClassField.unitFiltrationStructuralLaws.{u}`, whose complete type
is the published proposition
`Langlands.LocalClassField.UnitFiltrationStructuralLaws.{u}`. It quantifies every
prime `p`, every `F : PadicField.{u} p`, and every supplied
`T : F.TopologicalData`. The carrier universe remains arbitrary.

The result proves compactness and closedness of every `T.unitFiltration n`,
antitonicity, separation (a unit in every level is one), and
`T.unitFiltration 0 = T.unitSubgroup`. Every natural level is included. The
filtration is exactly the image of the published integer-unit reduction kernel;
no substitute filtration or extra hypothesis is introduced. The statement pair
and its imports are unchanged.

## Implemented proof

Helper theorems lie in `Langlands.PadicField.TopologicalData` and take the supplied
`T` explicitly.

1. `mem_congruenceUnits_iff` unfolds kernel membership and uses equality of unit
   values together with `Ideal.Quotient.mk_eq_one_iff_sub_mem`. Thus an integer
   unit belongs to the actual reduction kernel at level `n` exactly when its
   value minus one belongs to the `n`th power of the maximal ideal.
2. `integerUnitsInclusion_injective` follows from `Units.map_injective` and
   injectivity of the integer-ring subtype map. `congruenceUnits_antitone`
   follows from `Ideal.pow_le_pow_right`, and `unitFiltration_antitone` follows
   by monotonicity of subgroup images.
3. `congruenceUnits_zero` uses the zeroth ideal power, which is the top ideal.
   `unitFiltration_zero` identifies the image of all integer units with the
   valuation-unit subgroup using the already published `integerUnitsEquiv`.
   The forward direction uses its inverse; the reverse direction constructs
   the integer-unit representative explicitly.
4. For `isClosed_congruenceUnits`, the local instances are the supplied
   `T.topology`, `T.valuativeRel`, `T.localField`, and the existing Hausdorff
   certificate `T.fieldT2`. Mathlib's local-field instances give a compact
   discrete valuation integer ring, hence a Noetherian ring. Its ideals are
   closed by `IsNoetherianRing.isClosed_ideal`. The kernel is the preimage of
   the corresponding ideal under the continuous map `x ↦ x.val - 1`.
5. Mathlib's units topology makes units of a compact Hausdorff topological
   monoid compact: their value/inverse graph is closed in the product.
   Consequently each closed integer-unit kernel is compact.
   `isCompact_unitFiltration` takes its continuous image under the published
   `integerUnitsInclusionContinuous`. `isClosed_unitFiltration` then uses
   Hausdorffness of the field-unit topology. These are the standard units
   topologies induced by the supplied field topology.
6. `congruenceUnits_separated` uses
   `Ideal.iInf_pow_eq_bot_of_isLocalRing`, Krull's intersection theorem for
   Noetherian local rings. The proper maximal ideal has powers with zero
   intersection, so a unit in every kernel has value minus one equal to zero.
   For `unitFiltration_separated`, choose an integer-unit representative at
   level zero. Injectivity of the inclusion identifies it with each higher
   level's representative. Integer-unit separation and preservation of one
   then give the result in the field-unit group.
7. The entry theorem assembles these four conclusions with no additional
   parameters or assumptions.

## Sources and provenance

The mathematical source of the structural bundle is Jean-Pierre Serre,
*Local Fields*, translated by Marvin Jay Greenberg, GTM 67, Springer, 1979,
source ID `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Worker 102 read Chapter II, Section 1, printed pp. 26–28 (PDF pp. 34–36),
including Proposition 1 and the compactness of the integer ring, and Chapter
IV, Section 2, printed p. 66 (PDF p. 73), giving the convention `U^0 = U`,
the positive congruence levels and the decreasing closed neighborhood filtration.
No source-specific errata note was present in the Library.

This exact bundle and its helper theorems are derived formulations of those
facts for the existing Lean objects. The implemented separation argument uses
Mathlib's algebraic Krull intersection theorem rather than a direct topological
neighborhood argument. This module does not assert that Serre presents this
precise proof route or Lean bundle. It proves no norm theorem or compact lifting
criterion.

The direct imports are the unchanged
`Langlands.ClassFieldTheory.Local.UnitFiltrationTopologyStatement`,
`Langlands.LocalField.Topology` (the existing `fieldT2` certificate), and
`Mathlib.RingTheory.Filtration` (Krull intersection). The relevant transitive
Mathlib APIs are `NumberTheory.LocalField.Basic`, `Topology.Algebra.Group.Units`,
`Topology.Algebra.Module.Compact`, `RingTheory.Ideal.Quotient.Defs`, and
`RingTheory.Ideal.Operations`. They are used at the project pins Lean 4.34.0 and
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
