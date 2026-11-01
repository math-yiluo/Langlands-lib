# CM transport of full automorphic equivalences and classes

This is an internal construction from `OperatorCMTransport`, the existing
full-equivalence relation in `OperatorEquivalence`, and the positive-rank
cuspidal quotients in `CuspidalOperatorRealization`. It supplies the elementary
map conjugation and quotient descent required to use actual CM image
realizations independently of their embedded representatives. No new
literature-defined object is identified here.

Let `K : Type uK` be an actual CM number field and let `n` be any natural rank.
For an actual full intertwiner `L : S.Intertwiner T`, its constructed
`complexConj` is the linear map
`C_T ∘ L ∘ C_S⁻¹`, where the `C` maps are the actual continuous complex-linear
image equivalences in `OperatorCMTransport`. Whole-algebra covariance proves
that this map intertwines every operator on the actual image spaces.
The inverse covariance identity for `C_S⁻¹` reduces the proof to the original
intertwining identity at `cmOperatorConjugation n a`; forward covariance for
`C_T` then gives the required target action.
The construction preserves identity and composition. The intertwiners
themselves are algebraic; no continuity of an arbitrary `L` is asserted.

`OperatorRealization.Equivalence.complexConj` uses the same map and the
composite of the three genuine linear equivalences. Its action on `C_S f`
is exactly `C_T (e f)`. The underlying intertwiner, identity, composition,
and the induced finite-image equivalence satisfy the displayed compatibility
identities. The latter identity compares the actual finite form images via
the existing `finiteEquiv`; it introduces no local factor or factorization.

The theorem `OperatorRealization.complexConj_equivalence_iff` preserves and
reflects the existing full-equivalence relation. The forward implication
applies the constructed equivalence again and uses involutivity of the
actual embedded images. This proves that
`OperatorRealization.IsoClass.complexConj` is well-defined on the existing
quotient. It sends the class of `S` to the class of `S.complexConj`, is
involutive and injective, and gives an actual self-equivalence of the class
type. These classes retain all finite, standard compact and genuine
differential operators in their equivalence relation.

With compactness of the scalar additive adele quotient explicit, the same
construction descends to `CuspidalOperatorRealization.IsoClass K r`, whose
representatives are actual irreducible cuspidal realizations of rank `r + 1`.
Forgetting to the full operator class commutes with CM transport. Its
injectivity and the full-class involution prove the cuspidal-class
involution. The resulting self-equivalence and equality reflection are
proved without a chosen representative.

`PositiveRankCuspidalClass.complexConj` applies the fixed-rank construction
inside each fiber of the existing dependent sum. Its rank index and positive
rank are unchanged. It commutes with `ofFixedRank` and is an involutive
self-equivalence with equality reflection.

All coefficients remain complex and unchanged by the map; CM conjugation
acts on function arguments as established in the imported construction.
Topologies on actual image equivalences are inherited from compact-open
continuous functions. No additional topology is imposed on the quotients.
No arbitrary-class occurrence, spectral existence, tensor factorization,
classification, contragredient identification or conjugate self-duality is
asserted. This pair also does not construct a CM operation on the separate
quotient of all finite smooth representations.
