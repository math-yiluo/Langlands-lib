# Compact normalization of actual primitive adelic vectors

The definition `normalizedSet F n` is the set of vectors over the actual full
adele ring whose maximum coordinate norm is one at every finite and infinite
place. This module proves compactness of this fixed set in the existing product
and restricted-product topology, and combines it with the content-idele
construction to normalize every actual primitive vector. All statements retain
arbitrary number fields `F : Type u` and dimensions `n : ℕ`.

The source is T. A. Springer, *Reduction theory over global fields* (1994), §1.8,
printed p.210 (PDF p.4), the paragraph after properties (a)–(d). It defines the
set `K` with local norms one, states that it is compact and that each primitive
vector has an idele multiple in it. The source is registered as
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
The retained original is
`literature/Reduction theory over global fields (Springer, 1994).pdf`.

## Implemented proof

The maps `continuous_finiteNorm` and `continuous_infiniteNorm` are obtained by
applying the existing continuous local projections in each coordinate and then
taking the norm on the finite product of completions. Thus `normalizedSet` is
closed, as an intersection of the inverse images of the closed singleton `{1}`
under these maps.

At every place, each individual coordinate norm is at most the maximum norm
one. At finite places the equivalence between norm at most one and membership
in the actual completed integral subring therefore places every finite
coordinate in `integralFiniteAdeles F`. At infinite places its norm is at most
one. Consequently each coordinate belongs to the existing compact set
`NormOneIdeleClass.adeleBox F 1`. The normalized set is a closed subset of the
finite product of these compact boxes, which proves `isCompact_normalizedSet`.
Only the compact-adele-box theorem from `NormOneIdeleClassCompact` is used in
this proof; no reduction or rational-vector compactness premise is assumed.

The preceding content-idele module proves that `normalizedVector` has local
maximum norms one. Hence `normalizedVector_mem` places it in this compact set.
`exists_content_mul_normalized` states the resulting exact factorization:
every primitive vector is the scalar product of an actual idele and a vector
in this same compact set, and the normalized norm of that idele equals the
original positive height. The scalar product and norm equalities reuse the
proved content-idele identities without changing the carriers or topology.

## Scope

This unit proves compact normalization and the displayed factorization. It does
not prove Springer's height limit properties (c)–(d), existence of rational
height minima, Gauss reduction, rank induction or Galois descent. Connected
reductive Siegel coverage, algebraic setup existence and the compatible compact
subgroup remain obligations of the original reduction task.
