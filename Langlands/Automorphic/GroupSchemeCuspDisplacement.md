# Small right translates in the cusps of a reductive adelic quotient

`exists_compact_groupSchemeCuspDisplacementCover` uses the actual positive-central rational
quotient of a connected reductive group over a number field. For each identity neighbourhood
in the adelic group it gives a compact subset of the quotient. Outside that subset the
absolute value of every continuous cuspidal function is bounded by its right oscillation
in the given neighbourhood.

The norm-one quotient supplies representatives. The weak Siegel covering with finitely many
right translates gives compact left and right factors around an intrinsic positive torus
point. With every simple-root norm bounded above, the compact simple-root-box theorem puts the
class in the chosen compact subset. The positive torus is taken in the derived group. The
simple roots span its rational character space in the sense used by
`simpleRootBoxCompactStatement_of_rootComplement`.

At a point outside the compact subset, choose a simple root whose norm exceeds the common
threshold. The standard parabolic omitting that root is proper by the order of standard
parabolics. `adelicUnipotentArchimedeanRepresentatives` gives a compact family of archimedean
representatives for its radical, modulo rational left translations and a prescribed open
finite level. The finite adelic coordinates of the original points lie in one compact set
because the positive torus has finite coordinate one. The left Siegel factors normalize the
radical, so conjugation by those factors leaves a compact family of radical points.
`adelicMaximalUnipotentContraction` contracts this family on the archimedean factor as the
selected simple-root norm grows. Conjugation by the compact right factors preserves the
uniform smallness required to combine the archimedean displacement with the finite level.
Thus every radical translate of the class equals a right translate in the original
neighbourhood. Averaging differences over the mass-one radical quotient and using the
vanishing of the constant term bounds the value of the function.

This is a topological consequence of the unipotent contraction and finite-level reduction
in Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), I.2.10,
printed pp. 30–33. It also uses the Library's finite-translate weak Siegel covering and
compactness of the positive simple-root box. The estimate takes right oscillation as its
input and applies to continuous functions.
