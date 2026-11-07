# Actual roots of the outer Levi in a fine torus

Worker 17. This internal construction retains two supplied compatible fine
and outer parabolic root presentations, an actual fine-Levi map into the
original outer Levi, and its compatibility with the ambient inclusions.

The original outer Levi is the dynamic centralizer of the transported outer
cocharacter. The fine torus centralizes that cocharacter, so its all-test
image lies in the original outer Levi. The represented-subgroup factor
constructs `outerFineTorusFactor` into that actual Levi. Its composite is
the original fine torus inclusion, and maximal splitness descends along
the closed outer-Levi inclusion.

With the affine and finite-type instances needed to define Lie roots in
both groups, `relativeRoots_outerFineTorusFactor` applies the published
`relativeRoots_centralizer_factor` with the proved `dynamicLie`. The actual
outer-Levi roots are exactly the fine ambient roots pairing to zero with
the transported outer cocharacter. The fine generic cocharacter remains
generic on this subset of roots.

If the ambient group is connected reductive and the fine parabolic is
contained in the outer parabolic on every test, the transported cocharacter
is nonnegative on all fine positive roots. A positive outer-Levi root that
decomposes into two fine positive roots has total pairing zero. Each
summand therefore has pairing zero, so both are outer-Levi positive roots.
This shows an outer-Levi simple root is fine simple and belongs to the zero
face. Conversely a fine simple root in that face is an outer-Levi root and
cannot decompose into two positive outer-Levi roots. Thus
`simpleRelativeRoots_outerFineTorusFactor` identifies the actual simple
roots with the previously constructed outer zero face, including empty
faces and nonreduced systems.

The provenance is the published torus centralizer containment, represented
subgroup factorization, maximal split-torus descent, dynamic Lie comparison
and positive-root simplicity argument. This support for Renard VII.2.3
asserts no general presentation existence, minimality in the outer Levi,
cone comparison or full representation-theoretic conclusion.
