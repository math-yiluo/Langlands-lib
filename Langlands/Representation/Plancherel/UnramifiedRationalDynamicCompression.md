# Actual induced-family compression at a dynamic output parabolic

This derived adapter applies the actual rational induced-family compression
criterion to an arbitrary output cocharacter. The output parabolic may differ
from the inducing parabolic, and the field and inducing-carrier universes remain
independent.

`outputLeviCompactOpen` constructs the literal intersection of the ambient open
subgroup with the output dynamic centralizer, as an open subgroup of that Levi.
`isClosed_outputLeviPoints` reuses `RationalDynamicSource.isClosed_levi` from
`Langlands.Representation.Plancherel.RationalDynamicSourceHaar` on the same
literal dynamic centralizer and canonical rational-point topology. Compactness of the intersection then
follows by pulling back compactness through its closed subtype embedding. These
are derived topological constructions on the existing objects.

`complexInducedCompressedAction_uniform_of_dynamic_jacquet_finite` obtains native
induced fixed-vector finiteness from the published
`universalInducedCoefficientFiniteness` theorem for admissible inducing data. It
obtains full actual specialization bijectivity from the published
`rationalNormalizedInducedSpecialization` theorem. Neither conclusion is a new
assumption of this adapter.

The remaining native output-Jacquet finiteness premise is exactly
`UniversalInducedJacquetFiniteness` for the full universal induced representation.
The proof applies it to the constructed compact open intersection, then invokes
the native family compression criterion. The actual dynamic unipotent subgroup
is closed, and its Levi normalizes it by the canonical dynamic semidirect
decomposition. The Iwahori contraction and Levi-centrality hypotheses are
retained. One positive exponent is chosen before every unramified character and
gives stability of that same power on every actual specialized induction.

The structural hypotheses retained here are connected reductivity, the supplied
parabolic root presentation and geometric unipotent radical, the actual
semidirect decomposition with closed unipotent image, continuity of its
projection, compactness of its literal quotient, and the ambient local
compactness and nonarchimedean group structures. This conditional family result
does not yet prove the host theorem for every smooth representation.
