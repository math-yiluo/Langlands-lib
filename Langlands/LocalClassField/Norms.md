# Compatibility re-export: Norms

This pair preserves the published import path `Langlands.LocalClassField.Norms`.
Its Lean file consists only of `import Langlands.ClassFieldTheory.Local.Norms` and declares nothing.

Use the canonical [Norms module documentation](../ClassFieldTheory/Local/Norms.md)
for the mathematical definitions, proofs, original sources and retained public
declaration names. Import `Langlands.ClassFieldTheory.Local.Norms` in new work.

This compatibility pair was added when the unchanged declaration bodies moved
under the local class-field
topic at Library base `c139df9ce67284be1bc963c2de5fbebd90214dda`.
No theorem is proved or restated by this re-export. Public namespaces, including
`Langlands.LocalClassField` and `Langlands.PadicField.TopologicalData`, are unchanged.

Keep this shim until the modules that use this path import the canonical module.
The [migration ledger](../ClassFieldTheory/Local/Completion.md#topic-hierarchy-migration-ledger)
lists all seven paths, preserved declarations, coordination and validation.
