# Actual first adjointness on standard rational points

Worker 1216 constructs this internal adapter from the actual general
first-adjointness equivalence and Worker 480's standard-unipotent regularity
adapter. The ambient group is literally `RationalPoint k G.X`, with its
canonical evaluation topology `pointTopology`. The subgroup families are
`parabolic i ν I`, `levi i ν I` and `unipotent i ν I` for finite subsets of the
actual `SimpleRoot i ν`. These are the objects and functors appearing in
`RationalRankOneJacquetModulesStatement`.

The field is any nonarchimedean local field, with no characteristic-zero
restriction. The affine group scheme is connected reductive, `i` is a maximal
split torus and `ν` is generic. `StandardCocharacterStatement.{u}` remains an
explicit premise, exactly as in the rational target. Local compactness and
nonarchimedeanness of the rational-point group are at the canonical topology.
The adapter accepts any closedness witness `hU` for the actual unipotent
subgroup. It does not require a new unimodularity or compact-limit hypothesis.
Neither finite length nor admissibility is assumed. The field universe `u`
and representation carrier universes `v` and `w` are independent; in
particular they permit the target's carrier universe `max (u + 1) v`.

`FirstAdjointness.equiv` identifies the actual intertwiner spaces
`Hom_G(A, i_I σ)` and `Hom_L(r_I A, σ)` as complex vector spaces.
`equiv_evaluation` identifies the forward map on quotient generators with
the actual general evaluation map, whose value is evaluation at the identity.
`equiv_symm_evaluation` recovers the original Jacquet map by evaluating the
inverse on generators. The inverse itself is the unchanged general
covariant-orbit-function construction. `equiv_comp` records naturality in the
smooth source, using the actual normalized Jacquet map.

`nontrivial_jacquet_of_map_ne_zero` and
`nontrivial_jacquet_of_injective` specialize the general consequences to
the same rational functors. Thus a nonzero map into induction, and in
particular a nontrivial subrepresentation of induction, has nonzero
normalized Jacquet restriction at that standard Levi. When `σ` is
irreducible, `quotientMapOfNonzero` returns the actual descended evaluation
intertwiner from `r_I A` to `σ` with its surjectivity witness.
`equivalenceOfIrreducibleJacquet` gives an actual representation equivalence
when `r_I A` is also irreducible. `isoOfIrreducibleJacquet` packages that
equivalence as a smooth-category isomorphism at a common carrier universe.

The implementation first applies
`standardUnipotent_isUnimodular_of_standardCocharacterStatement`. Its
actual dependencies are the standard-cocharacter subgroup comparison,
`BruhatTits.dynamicUnipotentCompactOpenContainment`,
`BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups` and
`General.isUnimodularModulus_of_isLimitOfCompactSubgroups`. The resulting
unimodularity proof is supplied to the unchanged
`General.FirstAdjointness.equiv` and the corresponding general consequence
declarations. The final categorical isomorphism uses `SmoothRep.mkIso`.
The forward evaluation formula is definitional; the inverse evaluation
formula applies the inverse law to a quotient generator. Naturality reuses
`General.FirstAdjointness.equiv_comp`.

The first-adjointness construction itself uses
`Jacquet.CharacterReciprocity.evaluation`, its translation and covariance
formulas, the actual localization quotient and its universal property,
`General.inducingRepresentation_jacquet_eq` for normalization cancellation,
and `smoothLift` for the covariant inverse. The consequences use the
injectivity of that linear equivalence and Mathlib's irreducible-map
surjectivity and bijectivity theorems. This is internal composition of those
actual constructions, with no new assertion about an original source.
No classification, character-independence, geometric-lemma or cuspidal-support
theorem is used.

This adapter provides subrepresentation nonvanishing and the actual
quotient map to the inducing representation. Nonvanishing for quotient
constituents, irreducibility of their Jacquet modules, the two-factor
geometric expansion, vanishing at other proper standard subsets and the
whole `RationalRankOneJacquetModulesStatement` remain separate obligations.
