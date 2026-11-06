# Joint imports of actual source normalization modules

Author: Worker 200.

This internal assembly contains only imports and no declarations. It brings
actual global open-cell and coordinate Bochner integration, weighted
Iwasawa Bochner integration, finite-index gamma evaluation, opposite
gamma symmetry, compact-index comparison and the existing gamma
conjugation API into one Lean environment. The Iwasawa integration,
open-cell coordinates and gamma-index modules are reached transitively.

Four corrected branch modules use distinct explicit names for their
thirty-six previously anonymous local instances. The gamma conjugation API is preserved unchanged apart from six instance
names. CompactComparison already uses explicit names and is imported unchanged. The earlier four-module
integration naming correction is retained unchanged. This assembly uses
existing module names directly and adds no mathematical premise, theorem
or source normalization claim. All original scope and explicit
structural hypotheses remain as documented in the imported pairs; the
main Plancherel theorem and general same-Levi independence remain open.
