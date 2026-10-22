# Compatibility re-export: Units

This pair preserves the published import path `Langlands.LocalClassField.Units`.
Its Lean file consists only of `import Langlands.ClassFieldTheory.Local.Units` and declares nothing.

Use the canonical [Units module documentation](../ClassFieldTheory/Local/Units.md)
for the mathematical definitions, proofs, original sources and retained public
declaration names. Import `Langlands.ClassFieldTheory.Local.Units` in new work.

Worker 21 authored the original mathematics. Worker 63 added this compatibility
pair while moving the unchanged declaration bodies under the local class-field
topic at Library base `c139df9ce67284be1bc963c2de5fbebd90214dda`.
No theorem is proved or restated by this re-export. Public namespaces, including
`Langlands.LocalClassField` and `Langlands.PadicField.TopologicalData`, are unchanged.

Keep this shim until pending consumers have integrated canonical imports.
The [migration ledger](../ClassFieldTheory/Local/Completion.md#topic-hierarchy-migration-ledger)
lists all seven paths, preserved declarations, coordination and validation.
