# Upper block counts for actual Jacquet modules

This internal consequence of the actual geometric-filtration vanishing theorem
bounds the target block count of nonzero normalized Jacquet modules of
quasicuspidal induction and of its actual subquotients. It uses the supplied
p-adic topology and independent field and carrier universes. It adds no
finite-length or irreducibility assumption.

`HasJacquetBlockBound F T B π` requires the actual normalized Jacquet carrier of
`π` at every shape `C` with `B.length < C.length` to be subsingleton.

The elementary inclusion argument is valid over any nontrivial commutative
ring. A transposition within a source block lies in the source Levi. If its
conjugate lies in the target Levi, the two permuted coordinates have the same
target block label. The existing transposition-entry criterion proves this
claim for every pair of coordinates in a source block. Thus the block-label
map sends every source block into one target block. It is surjective: take the
inverse image of the first coordinate of each target block. Counting the
finite block-index sets gives `C.length ≤ B.length`.

Consequently, when `B.length < C.length`, the source Levi cannot be conjugate
to an embedded refinement of the target Levi: every such embedded refinement
is contained in the target Levi. The published
`quasicuspidalJacquetVanishing` theorem then kills the actual normalized
Jacquet module of the induced representation. Its proof uses the actual
geometric filtration and vanishing of every proper-source geometric piece;
no splitting of the filtration is involved.

`hasJacquetBlockBound_of_subquotient` transports each actual subquotient
through normalized Jacquet. An actual subquotient of a subsingleton carrier is
subsingleton. Applying this to the proved bound on the original induction
gives `quasicuspidal_subquotient_hasJacquetBlockBound` in every rank, including
zero and the empty Levi. The impossible strict block inequality at rank zero
is already covered by the general subgroup argument.

This is an internal derivation from the existing subgroup, transposition,
geometric-vanishing and Jacquet-subquotient proofs. It does not assert
exactness of any cut differential, concentration below the terminal degree,
or signed Aubert effectivity.
