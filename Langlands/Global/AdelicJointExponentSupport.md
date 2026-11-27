# Finite sums of joint generalized eigenvectors with prescribed characters

Module `Langlands.Global.AdelicJointExponentSupport` works with a commutative group `A`
acting on a complex vector space `Y` by `T : A →* Module.End ℂ Y`, and with the joint
generalized eigenspaces `jointGenEigenspace T δ` of
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.ExponentDecomposition`.

## Definition

`IsJointlySupportedIn T S y` says that `y` is a finite sum `∑ δ ∈ t, w δ` with every
`δ ∈ t` in the set of characters `S` and `w δ ∈ jointGenEigenspace T δ`. This is an
internal definition. It records the support of an exponent expansion by a set of
characters rather than by a fixed list.

## Closure properties

- `zero`, `of_mem`, `mono`, `add`, `smul`, `neg`, `sub` and `finset_sum`. Sums pad the two
  index sets by zero on their union and use `Finset.sum_ite_mem`.
- `of_decomposition`: if `y = ∑ δ ∈ t, w δ` with `w δ` in the joint generalized eigenspace
  for `δ`, and every component with `δ ∉ S` vanishes, then `y` is supported in `S`. The
  witness is the filtered sum.

## Independence

- `sum_eq_sum_fiberwise_character` regroups a finite family `f i ∈ jointGenEigenspace T (δ i)`
  by the characters `δ i`. Each fibre sum lies in the eigenspace of its character, and the
  sum of the fibre sums is the original sum.
- `fiber_sum_eq_zero_of_isJointlySupportedIn`: if `∑ i ∈ s, f i` is supported in `S` and
  `χ ∉ S`, the fibre sum over `δ i = χ` vanishes. The two decompositions are extended by zero
  to a common finite set of characters containing `χ`. Independence of the joint generalized
  eigenspaces (`iSupIndep_jointGenEigenspace`, through
  `iSupIndep_iff_finsetSum_eq_imp_eq`) compares them component by component. The component
  of the support witness at `χ` is zero.
- `isJointlySupportedIn_of_fiberVanishing` and `isJointlySupportedIn_of_fiberVanishing_sub`
  turn a vanishing property into support. The property is that in every finite joint
  generalized eigendecomposition of `y`, the components outside `S` vanish. Then a given
  family summing to `y`, or a difference of two given families, exhibits `y` as supported
  in `S`. The proof regroups the family by characters and applies the property to the fibre
  sums. The difference version uses a family indexed by a disjoint sum.

The module is used to transport the moving exponent support of
`Langlands.Analysis.Meromorphic.meromorphicExponentSupport` to cuspidal exponent
decompositions. This is the derived exponent comparison in the far-region step of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series* (2024), §8.6.
