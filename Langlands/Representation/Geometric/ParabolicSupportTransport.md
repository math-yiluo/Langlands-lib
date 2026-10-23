# Smooth inducing covariance and support-quotient transport

This internal construction connects the published compact support filtration on
smooth parabolic inputs to the specified support filtration of normalized
parabolic induction. It does not identify an orbit piece or assert the geometric
lemma.

`isSmooth_inducingRepresentation` pulls a smooth Levi representation back along
the continuous Levi projection, then applies the published smooth-twist theorem
to the inflated smooth character. `smoothInducingFunctor` bundles precisely the
existing inducing action and intertwining maps with that proof. Forgetting
smoothness gives `inducingFunctor` by definitional equality.

`parabolicSupportGradedCompactSmoothIso` compares the same successive quotient
at each index of the supplied `OrderedDoubleCosets` data. Its source is the
compact support quotient, precomposed with the smooth inducing functor for the
positive half modulus; its target is the actual
`parabolicInductionSupportFiltration` quotient. The construction installs the
published compactness of the actual parabolic quotient and precomposes
`rawSupportGradedCompactSmoothIso` with `inducingFunctor`. All identifications
between precomposition and the specified quotients are definitional. Thus the
forward map is induced by the canonical inclusion that retains the same
function. The orbit order and support subspaces are unchanged.

The construction uses arbitrary smooth complex source-Levi representations,
with independent field and carrier universes. It uses no admissibility,
finite-dimensionality or finite-length assumption. Its provenance is internal:
it composes the published smooth pullback and twist results, parabolic quotient
compactness, and the canonical compact-to-smooth support comparison. The Mackey
orbit comparison, Jacquet image exactness and local normalized comparison remain
separate proof obligations.
