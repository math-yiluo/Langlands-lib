# Integral columns for exceptional Cartan matrices

This internal module gives explicit nonnegative integer matrices `K` for
E6, E7, E8, F4 and G2, with `N*K = c*I` and scale factors 3, 2, 1, 1 and 1,
respectively. The displayed integer arrays were computed by rational Gaussian
elimination on Mathlib's standard matrices; each nonnegativity assertion and
full matrix multiplication identity is checked in Lean by `decide`.

These columns supply the nonnegative-vector witnesses used to bound leaf
extensions. They do not assert a classification result.

Applying the leaf-extension bound to these columns proves exact E7
presentations for every finite Cartan leaf extension of E6 with a nonzero
edge, and exact E8 presentations for every such extension of E7. For E6 the
only attachment indices are zero and five; E7 allows only index six. The
new edge is simple in each case. The explicit finite permutations preserve
every ordered integral entry and are checked by finite cases and `decide`.
E8, F4 and G2 admit no finite Cartan leaf extension with a nonzero edge, since
every diagonal column value is at least twice the scale.
