# Head multiplicity and intertwiner dimension

`Langlands.Classification.finiteLengthHeadHomMultiplicity` proves exactly the
published proposition
`Langlands.Classification.FiniteLengthHeadHomMultiplicityStatement`. The group,
source-carrier, and target-carrier universes remain independent. The topology
of the group is arbitrary. The source has finite group-algebra length; its
complex carrier need not be finite-dimensional, smooth, or admissible.

The two component theorems are `semisimpleHomMultiplicity`, for a semisimple
source, and `headHomMultiplicity`, for the actual head of any finite-length
source. In each case the target is admissible and irreducible. Each conclusion
includes finite-dimensionality of the intertwiner space and an actual
composition filtration witnessing the stated Jordan–Hölder multiplicity,
including multiplicity zero.

For an exact sequence of representations with a surjective quotient map, the
proof first establishes contravariant Hom exactness. It converts intertwiners
to maps of the actual complex group-algebra modules, factors a map annihilating
the lower term through the kernel quotient, and uses the quotient-to-codomain
equivalence. This argument also works for a noncommutative group algebra.
Surjectivity of the quotient makes precomposition injective. Semisimplicity of
the middle representation supplies extension of any intertwiner from its
subrepresentation, so restriction on Hom is surjective. Finite generation of
the end terms gives finite generation of the middle Hom space. Additivity of
module length over the complex field then gives additivity of its finite
dimension.

For each simple factor, admissible Schur's lemma identifies its Hom space with
the complex field when that factor is equivalent to the target. Admissibility
is transported along that equivalence. If the factor is not equivalent to the
target, the intertwiner space is zero by the bijective-or-zero form of Schur's
lemma. The dimension is therefore one or zero, respectively.

Every subrepresentation of a semisimple representation is semisimple. An
induction over the prefixes of an actual composition filtration applies the
Hom dimension additivity just proved to the genuine successive quotient maps.
The bottom Hom space is zero; the top is identified with the Hom space of the
whole source. Its dimension is the sum of the zero-or-one contributions of
the simple factors. The cardinality defining `factorMultiplicity` is exactly
this sum. Finite group-algebra length supplies the required composition series
through the published `LengthCriterionProof` conversion.

Finally, the published finite-length head is semisimple and has finite length.
Precomposition with its actual surjective projection is a linear equivalence
on intertwiners to the irreducible target: injectivity follows from
surjectivity of the projection, and surjectivity follows from `headLift` and
`headLift_comp_toHead`. Transport of finite dimension and its dimension through
this equivalence proves the head clause.

The provenance is internal algebraic derivation from the published head
universal property, admissible Schur results, composition-series conversion,
and Mathlib's semisimple-module and module-length algebra. This is a
prerequisite bridge, not a proof of the relative cosocle comparison or a
literal transcription of a theorem from Silberger.
