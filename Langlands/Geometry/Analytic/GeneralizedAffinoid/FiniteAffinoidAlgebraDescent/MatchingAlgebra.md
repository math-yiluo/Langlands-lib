# The complete bounded matching algebra

This module constructs the matching Banach algebra for the ordinary pairwise
transition data in `LocalData`. It does not assume an affinoid realization.

The matching algebra is the closed subalgebra of the finite product of the
original local presented algebras whose two restrictions to every intersection
agree after the supplied transition equivalence. The product carries its maximum
norm and the subalgebra carries the induced norm. Closedness is proved by
intersecting equalizers of continuous bounded maps. Completeness and the
ultrametric inequality follow from the corresponding properties of the actual
product and its closed subalgebra.

`projection` gives the original component maps. `lift`, `hom_ext`, and
`boundedHomEquiv` prove the entire bounded equalizer universal property for every
normed commutative test algebra. The uniform bound for a finite family is the sum
of its positive component bounds plus one, so the empty cover is included and no
nontrivial valuation or open mapping theorem is used.

`LocalAlgebras.structuralMap` uses each original stored cover restriction and
original finite Banach map. Compatibility over the whole base follows from
the supplied equality on the entire overlap coefficient algebra and the exact
pushout square. `PairTransitions.structuralMap` constructs the resulting bounded
map from the original base algebra into the matching algebra.

This is an internal explicit equalizer construction for Kiehl's descent theorem
in Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Kiehl's Theorem and Remark 1.2.1(ii), printed p.15 / PDF p.12, with the finite
algebra application in Lemma 1.2.12, printed p.20 / PDF p.17. Registered source:
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The proof route for the elementary helper results is the closed finite-product
construction described above. Affinoidness, norm-controlled finiteness, effective
base change, and realization of the entire glued spectrum remain separate
effectiveness obligations.
