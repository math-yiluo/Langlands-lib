# Actual source integration formulas together

Author: Worker 200.

This internal assembly module imports the actual global two-factor
open-cell integration, the weighted source-coordinate Bochner integration
and the nonnegative Iwasawa integration modules together. It introduces no
mathematical declarations. All hypotheses and normalization conventions
are those stated in the imported modules and their paired Markdown.

The four integration modules use explicit, distinct names for their local
rational-point topology, measurable-space, separation, local compactness,
nonarchimedean and countability instances. The instance types and bodies
and all mathematical definitions and proofs are unchanged. The correction
allows the sibling branches to share a Lean environment without duplicate
automatically generated declaration names. Compiling this module checks
that these branches can be imported together.

The normalization arguments derive from Waldspurger (2003), I.1, formulas
(2), printed p.240 / PDF p.6, as explained in each imported module. This
assembly and naming correction is internal content. It adds no realization
of Iwasawa factorization or compact-limit stability and proves no new
same-Levi independence or Plancherel conclusion. The separate Iwasawa
Bochner and gamma-index comparison branches are outside this assembly.
