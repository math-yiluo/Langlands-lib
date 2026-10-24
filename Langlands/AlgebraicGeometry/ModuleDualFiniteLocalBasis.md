# The internal dual preserves finite local bases and rank

`Langlands.Scheme.Modules.dualFiniteLocalBasisRank` proves the existing
`Langlands.Scheme.Modules.DualFiniteLocalBasisRankStatement` in every universe
`u`. For every scheme `X` and module sheaf `M : X.Modules`, it proves both:

- A single local-generator witness `q` satisfying `q.IsLocallyFreeData` and
  `q.IsFiniteType` gives such a witness for `dual M`.
- For every natural number `n`, `IsLocallyFreeOfRank M n` implies
  `IsLocallyFreeOfRank (dual M) n`.

Here `dual M` remains the existing
`internalHom M (Langlands.SchemeModule.structureModule X)`. Its sections are
morphisms of restricted sheaves on over-categories, with their restriction
compatibility.

## Implemented proof

All names below are in `Langlands.Scheme.Modules`.

`dualLocalGeneratorsData q` keeps the original cover index type `q.I`, its
opens `q.X`, and its covering proof `q.coversTop`. At each cover member `i`,
local freeness makes `(q.generators i).π` an isomorphism from the free sheaf
on `(q.generators i).I` to `M.over (q.X i)`. Finiteness supplies a `Finite`
instance for exactly this index type.

The published `dualLocalFreeIso` from `ModuleDualLocalFree` turns this
trivialization into an isomorphism from the free sheaf on the same index type
to `(dual M).over (q.X i)`. That dependency proves finite coordinate duality
using actual local morphisms, their restriction laws, and both inverse
identities. This module uses the resulting isomorphism unchanged.

Mathlib's `freeHomEquiv` turns this isomorphism's forward map into its
family of generating sections. The inverse-equivalence law
`Equiv.symm_apply_apply` identifies their presentation map with that forward
map, proving its epimorphism property for the generator structure and its
isomorphism property in `dualLocalGeneratorsData_isLocallyFreeData`.
`dualLocalGeneratorsData_isFiniteType`
uses the unchanged generator index type and its original finiteness proof.
`dual_hasFiniteLocalBasis` assembles both properties for the same new witness.

For `isLocallyFreeOfRank_dual`, the given equivalences with `Fin n` first
provide finiteness of each original index type via `Finite.of_equiv`.
The preceding constructor then applies. Its generator index types are
definitionally the original ones, so precisely the original equivalences
with `Fin n` supply the dual rank witness. Finally
`dualFiniteLocalBasisRank` combines these two implications with all schemes,
modules and natural-number ranks quantified as in the unchanged target.

The argument permits varying finite ranks across the cover. It assumes no
global constant rank in its first clause, no nonempty scheme or open, and no
positive rank. It proves neither rank uniqueness on an empty scheme nor a
comparison isomorphism between arbitrary duals and pullbacks.

## Dependencies and provenance

This is a derived assembly of the published finite local dual-basis
construction and Mathlib's local-generator API, rather than a separate
theorem quoted from the literature. Its mathematical dependencies are imported
by the current Library module names `FiniteLocalBasisStatements` and
`ModuleDualLocalFree`; it leaves their Lean/Markdown pairs and imports
unchanged.

The retained Stacks Project source
`stacks-relative-differentials-internal-hom-2026-10-21`, folder SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`,
`01CM.html`, opening of Section 17.22, defines internal Hom using morphisms
of restricted module sheaves. The retained source
`stacks-local-freeness-invertibility-sections-2026-10-21`, folder SHA256
`6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`,
`01C5.html`, Definition 17.14.1 (01C6), defines finite local freeness using
finite local basis index sets and specified rank using their cardinalities.
These passages were read for the meanings used here. The same-index duality
argument is the elementary derived construction proved in the imported
module, and the present proof transports its local isomorphisms over the
original cover.
