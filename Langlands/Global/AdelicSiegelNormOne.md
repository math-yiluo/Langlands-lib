# Norm-one containment from the actual algebraic Siegel setup

Author: Worker 1377.

This internal derived module constructs
`IsSiegelAlgebraicSetup.positiveNormOneMap`, the continuous homomorphism from
the intrinsic positive torus to the actual ambient norm-one adelic group,
and proves the containment direction of the actual Siegel reduction equality
from the existing `IsSiegelAlgebraicSetup`. It uses
the canonical standard unipotent and Levi schemes, the actual adelic maps,
the unchanged intrinsic positive subgroup and the normalized character norms.
Its field and all group schemes remain in the arbitrary universe `u`.

For a homomorphism from a group scheme satisfying `IsUnipotent`, every ambient
rational character restricts to the trivial homomorphism. The proof applies
the published `IsUnipotent.hom_eq_zero_of_isSplitTorus` to the composite into
`Gm`, a split torus. This first lemma needs only a field, with no affine,
finite-type, connectedness, smoothness or reductivity hypotheses.

For data satisfying `IsSiegelAlgebraicSetup`, its represented derived subgroup
and the equation `t₀ ≫ d = j ≫ i` put the all-test image of `j ≫ i` in the actual
`derivedSubgroup G`. The published `AdelicDerivedNormOne` then supplies both
rational-character triviality and norm-one membership of every `positiveMap`
value. Applying the published `positiveMapNormOneOfDerived` with this proved
containment constructs `positiveNormOneMap`; its continuity and homomorphism
laws come from the actual adelic map with its codomain restricted to the
norm-one subgroup. The simp lemma `positiveNormOneMap_val` states that its
ambient value is exactly the original `positiveMap` value.
The geometric unipotent-radical clause gives `IsUnipotent` of the actual
canonical unipotent scheme, so the first lemma supplies character triviality
of its ambient inclusion. No derived containment of that unipotent inclusion
is assumed or asserted.

Apply the published `productSet_subset_normOne` with these two proved
character facts. It already handles the actual norm-one Levi factor by
functoriality and the compact subgroup by compactness. Consequently every
ordered product `Ω_N Ω_M A K` belongs to `G(𝔸_F)¹` for every subset `A` of the
intrinsic positive torus. Specializing to the unchanged weak simple-root
chamber proves `weakSiegelProduct_subset_normOne`. Finally the published
product formula puts all principal rational points in the norm-one subgroup;
closure under multiplication gives containment of the entire rational left
saturation.

The provenance is internal: the module assembles the published
`AdelicSiegelReductionStatement`, `AdelicDerivedNormOne`,
`AdelicSiegelFactors` and `Torus.UnipotentHom` interfaces without a new
literature assertion. It asserts neither existence of the algebraic setup nor
the reverse covering inclusion, Iwasawa existence, positive-torus compatibility
or the full good-position reduction theorem. Empty root systems and
anisotropic groups are included, since the argument works for every subset
of the intrinsic positive subgroup.
