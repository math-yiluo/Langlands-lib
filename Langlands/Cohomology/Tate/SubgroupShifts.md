# Tate shifts compatible with subgroup restriction

Author: Worker 45.

For an arbitrary subgroup `H` of `G`, the restriction of functions on `G`
with the right-translation action is isomorphic to functions on `H` whose
values are functions from `G/H` to the original coefficient module.
The explicit coordinate map is
`f ↦ (h ↦ (q ↦ f(q.out * h)))`. Its inverse uses the proved
coset decomposition of `G`. The map intertwines the right-translation
actions by associativity. Normality of `H` is not required.

The coordinate isomorphism identifies the restricted representation with
an actual coinduction from the trivial subgroup of `H`. The already proved
coinduced Tate vanishing therefore applies in every integer degree.
Both scalar-split coefficient sequences from `ShiftDefinitions` remain
short exact upon restriction, and their connecting morphisms in the
subgroup's actual Tate long exact sequence are isomorphisms.

This supplies the shared shift sequences needed to extend the degree-zero
subgroup maps to all degrees in `TransferDefinitions`. This file makes no
comparison with ordinary group cohomology or homology.

Source: Serre, *Local Fields*, Greenberg translation, GTM 67, Springer
(1979), Chapter VII, §1, p. 110 (PDF p. 116), and Chapter VIII, §§1–2,
pp. 127–130 (PDF pp. 133–136). Source ID `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The explicit coset-coordinate proof is an internal realization of the
induced/coinduced acyclicity used in the source's shift argument.
