# Separated étale representability of central closed torus subgroups

`EtaleCentralTorusSubgroupRepresentabilityStatement.{u}` concerns a smooth,
separated, quasi-compact group scheme with geometrically connected fibres over a
locally noetherian base in universe `u`. It assumes adic-limit bijectivity for
the presheaf of all actual closed torus subgroups and local Artinian nilpotent
bijectivity for its central subpresheaf. The conclusion gives a separated
étale parameter scheme and an actual closed relative torus in the centre of
the pulled-back ambient group. `IsCentralUniversal` means that every actual
admissible central subgroup functor on every test scheme has a unique parameter
whose evaluated subgroup functor is literally equal to it.

The proof applies Murre's separated étale criterion. The central presheaf has
small values and satisfies the Zariski, fpqc, filtered-colimit and valuative
conditions. Adic bijectivity transfers from the ordinary torus-subgroup
presheaf. The representing equivalence at the identity gives a small central
section. Decoding it as an actual subgroup functor gives a closed torus
representative. Naturality under precomposition and the compatibility of
shrinking with restriction identify its evaluations with the representing
equivalences on all tests.

This is a conditional formulation of the application to central tori in
Raynaud, SGA 3, Exposé XV, Theorem 8.8(a) and Lemma 8.10, Gille–Polo recomposition,
PDF pp. 61–62. The Lean proof uses local Artinian nilpotent bijectivity directly
as the infinitesimal hypothesis of the criterion.
