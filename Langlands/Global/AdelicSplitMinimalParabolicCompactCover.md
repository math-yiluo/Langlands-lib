# Compact norm-one representatives for split minimal parabolics

Author: Worker 82.

For a connected reductive group over a field, suppose `i : T → G` is
both a maximal split torus and a maximal torus, and choose a generic
cocharacter `ν`. `Standard.splitMinimalLeviIso` identifies the original
`T` with the actual canonical empty-index standard Levi.

The proof uses the published equality between the minimal standard Levi
functor and the torus centralizer. The proved maximal-torus centralizer
theorem identifies this centralizer with the image of `i`, on every test
scheme. The uniqueness of a representing group scheme then constructs
the isomorphism. Its forward map recovers `i` after the original Levi
inclusion and equals the already defined `standardLeviTorusFactor`.
Transport along this isomorphism proves that the actual minimal Levi
is a split torus.

Over any number field in universe `u`,
`hasCompactNormOneRationalCover_emptyLevi_of_maximalTorus` applies the
unconditional split-torus compact-cover theorem to this actual Levi.
`hasCompactNormOneRationalCover_emptyParabolic_of_maximalTorus` combines
the published actual rational-Levi structure of the canonical minimal
parabolic with the compact-cover theorem for a split-torus Levi
decomposition in `AdelicNormOneSectionCompactCover`. This constructs
compact principal rational representatives for the norm-one subgroup
of the parabolic, defined using **all characters of the parabolic**.
It does not substitute the intersection with the ambient norm-one group.

Both adelic assertions keep the original scheme-point carriers,
principal rational maps, normalized idelic norms and inherited
topologies. They cover empty root systems and rank-zero tori. No
compactness or fundamental-set assertion for the ambient group is
assumed or proved.

This is internal derived infrastructure for Springer, *Reduction theory
over global fields* (1994), §2.1 and Remark 2.2(a), printed pp.211–212
(PDF pp.5–6), and the split-field use of (C) in §3.5, printed p.215
(PDF p.9). The algebraic comparison is derived from the existing
all-test centralizer and represented-subgroup theorems rather than
assumed from a matrix realization. The registered source is
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`,
file `literature/Reduction theory over global fields (Springer, 1994).pdf`.
No errata note exists. General nonsplit Levi compactness, root bounds
and Galois descent remain separate obligations.
