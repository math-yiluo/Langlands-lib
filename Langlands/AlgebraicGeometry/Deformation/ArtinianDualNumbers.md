# Actual dual-number Artinian tests

This is an internal construction from the published augmented Artinian test
category and Mathlib's actual trivial square-zero extension. It needs no
external representability or deformation theorem.

For an arbitrary universe `u`, a commutative ring `k : Type u`, a field
`K : Type u`, and a specified `k`-algebra structure on `K`, `residue k K`
is the test `K` with identity augmentation. The object `dualNumbers k K`
has the actual ring `DualNumber K = TrivSqZeroExt K K`, its original
`k`-algebra structure, and the first-coordinate augmentation to `K`.
The augmentation is surjective because every element has a constant lift.
Mathlib supplies locality of the dual-number ring. Its underlying
`K`-module is the product of two copies of `K`, hence Artinian.
The proof checks the scalar tower with multiplication in the square-zero
ring component by component, then transfers Artinianity from the
`K`-module to the ring.

`dualReduction` and `dualSection` are actual arrows in the augmented test
category, induced by the first-coordinate projection and the constant
inclusion. The lemma `dualSection_reduction` proves their strict section
identity in that category. A section is used only for this particular
split test; none is imposed on other Artinian tests.

The lemma `dualReduction_elementary` proves that this reduction is an
elementary surjection in the published convention: its kernel is
annihilated by the maximal ideal. The augmentation kernel equals the
maximal ideal, and the product of two elements with zero first coordinate
vanishes by the actual square-zero multiplication formula.

For every `c : K`, including zero, `dualScale k K c` is the actual
augmentation-preserving arrow induced by `epsilonScale c` after restriction
of scalars to `k`. The lemmas `dualScale_fst` and `dualScale_snd` state
its coordinate formulas: the constant coordinate is fixed and the
epsilon coordinate is multiplied by `c`.

These constructions identify test objects and arrows. They assert neither
an equivalence of Picard deformation groupoids nor formal versality,
algebraization, or the existence of a smooth atlas.
