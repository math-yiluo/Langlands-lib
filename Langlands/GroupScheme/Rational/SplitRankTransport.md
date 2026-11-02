# Transport and finite-rank comparison for split subtori

Worker 1271. This internal development supplies formal consequences of the published
split-torus, lattice and split-rank constructions. It does not establish ambient
rational conjugacy, existence of maximal extensions, or rank attainment.

Closed-subgroup morphisms compose and stay closed after an ambient isomorphism.
Consequently split-subtorus and maximal split-torus structure are invariant under
ambient isomorphisms, and `splitRank` is monotone under closed subgroup morphisms
and equal for isomorphic group schemes.

For finite split tori over any field, `splitTorus.cocharacterMap` transports
postcomposition on actual cocharacters through the published integral lattice
equivalences to an integral linear map `(I → ℤ) →ₗ[ℤ] (J → ℤ)`. A monomorphism
of underlying schemes over the field makes this map injective by cancellation.
Mathlib's finite free-module rank inequality then gives `Nat.card I ≤ Nat.card J`.
In particular a closed immersion has this inequality and an isomorphism has equal
cardinalities, by applying it in both directions. This proves splitting-rank
uniqueness without assuming the target conjugacy or rank statement.

The provenance is internal: these are categorical and linear-algebraic consequences
of `Rational.SplitTorus` and `Torus.Lattice`, intended for the proof of the
supremum clause in `MaximalSplitTorusConjugacyStatement`.
