# Product opposite stable-image Jacquet bijectivity

`Langlands.Jacquet.refinedOppositeStableImageJacquetBijective` proves the
published `RefinedOppositeStableImageJacquetBijectiveClause` with independent
field and carrier universes. The stronger helper requires only smoothness and
finite-dimensionality of the chosen compact-fixed space.

The argument adapts the Library's `CanonicalLiftBijectivityProof` to arbitrary
representations of a product Levi, using the actual product opposite kernel
and compression proofs. Component uniform contraction on the compact upper
radical intersections, followed by the finite supremum of thresholds, puts the
whole upper product into a smooth vector's stabilizer after conjugation.
Lower-Levi-upper factorization shows that every compact translate of the shifted
lift has the same coinvariant class: the upper factor fixes the lift, the lower
factor vanishes in coinvariants, and the middle factor fixes the target class.
Finite-orbit normalized averaging therefore gives a compact-fixed lift of the
shifted class.

Finite-dimensional Fitting decomposition on the compact-fixed space splits off
the generalized kernel, yielding a stable-image lift. Invertibility of
compression on the stable image and quotient compatibility cancel each scalar
power. Disjointness of the generalized kernel and stable image gives injectivity.
The proof assumes finite-dimensionality only for the compact-fixed space; the
final exact wrapper obtains it from admissibility. It does not assume tensor
factorization or prove the host generic comparison.
