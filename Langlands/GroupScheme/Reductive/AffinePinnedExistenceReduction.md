# Pinning correction of affine unpinned isomorphisms

Worker 243.

`AffinePinnedIsomorphismExistenceStatement` is exactly the existence part of the published affine pinned Isomorphism Theorem: all original hypotheses and the full torus-character and pinning predicate are retained, while uniqueness is omitted. The theorem `affinePinnedIsomorphismExistence_of_unpinned` derives it from the unpinned affine Isomorphism Theorem, retained as an explicit premise.

`affinePinnedIsomorphismOfUnpinned` selects the constructed actual isomorphism and packages it with the full torus-character and pinning predicate. Its return is isomorphism data, with the verified equations retained.

The given unpinned isomorphism restricts to linear equivalences between corresponding actual exponent root lines. Comparing their supplied trivializations identifies its differential on each simple-root vector with multiplication by a unit. This is a unit over the original ring because it comes from a linear automorphism of the ring, with the inverse automorphism supplying its multiplicative inverse. The target group's simple-root scaling automorphism for the inverse units then corrects the unpinned isomorphism. This automorphism fixes the target torus, so the same torus isomorphism and its all-test monomial identity remain valid. The differential formula makes the unit factors cancel. Every step includes the zero ring.

This is the arbitrary-affine-base form of the source proof of Conrad, *Reductive group schemes* (2014), Theorem 6.1.17, p.197, using Corollary 6.1.15, pp.195–196. The implemented reduction uses the unpinned Isomorphism Theorem as the existence input. It does not assert the unpinned premise or the uniqueness half.
