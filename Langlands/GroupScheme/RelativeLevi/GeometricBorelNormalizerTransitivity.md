# Normalizer conjugacy of geometric Borel subgroups containing a maximal torus

This internal derived module proves the geometric-fibre normalizer transitivity
needed in the proof of Conrad's *Reductive group schemes* (2014), Corollary
5.2.13(2), pp.158–159. Its inputs are the published Borel conjugacy and rational
solvable maximal-torus conjugacy proofs. It does not assert that a geometric
normalizer point lifts to a Zariski neighbourhood over an arbitrary base.

`exists_normalizerPoints_conjugatingIso_of_overgroupIso` works over any field.
It takes two overgroup embeddings `i : B → G`, `i' : B' → G`, embeddings of one
commutative group scheme `T` as maximal tori of both overgroups with equal
composites in `G`, conjugacy of maximal tori in `B'`, and a specified point and
isomorphism conjugating `i` to `i'`. Conjugating the transported torus to the
chosen torus within `B'` produces a correcting point `p`. The product of the
image of `p` with the original conjugating point normalizes the common embedded
torus and still conjugates the two overgroups. The result retains an actual
isomorphism of their source group schemes.

`IsBorelSubgroup.exists_normalizer_conjugatingIso` applies this construction to
two Borel subgroups of a smooth connected affine group over an algebraically
closed field, assuming both contain the range of a specified maximal torus.
The range inclusions factor the torus through each Borel. Ambient maximality
implies maximality in each closed Borel subgroup. Published Borel conjugacy
supplies the initial conjugacy, and published rational maximal-torus conjugacy
for smooth connected affine solvable groups supplies the correction inside the
second Borel. A point in `normalizerPoints` lies in the full subgroup-functor
normalizer, whose definition tests all schemes over the field.

`IsBorelSubgroup.exists_normalizer_range_conjugacy` forgets the retained
isomorphism and obtains equality of the conjugated range with the second Borel's
range. Precomposition by a source isomorphism preserves the range on every test
scheme. No reductivity or split-torus assumption is needed for these geometric
lemmas. Their provenance is the imported conjugacy, factorization,
maximal-torus transport and inner-automorphism identities; they introduce no
new structural assumption as an unconditional theorem.

`IsBorelSubgroup.normalizerConjugacy` chooses an actual normalizer point from
this existence theorem. Its subtype retains both the full normalizer condition
and the equality of Borel subgroup functors. This defined witness is the entry
construction of the module.
