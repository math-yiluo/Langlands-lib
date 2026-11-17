# Positive simple-root monoids under algebraic field extension

For a supplied split pinning over a field and an algebraic extension, `positiveRootMonoidBaseChangeEquiv` restricts actual character-lattice pullback to an additive equivalence of the monoids of nonnegative integral combinations of the supplied simple roots. The supporting membership theorem reflects as well as preserves positivity.

The proof maps the additive closure defining `positiveRootMonoid`. The published pinning base change retains the simple-root index set and pulls back each root character. Thus the image of the generating set is exactly the new generating set. The split-torus character-lattice map is injective, yielding the equivalence and the membership comparison. The algebraicity hypothesis comes from the published `SplitPinning.baseChange` used here.

Provenance: this is an internal consequence of the published actual pinning and lattice base-change constructions, used for the weight-order part of Milne, *Algebraic Groups* (2017), discussion 22.5 (printed p.464), registered as `milne-2017-algebraic-groups`, SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. The official 2017 errata snapshot registered as `milne-2017-algebraic-groups-errata-2026-11-02` contains no amendment to that discussion. No representation-theoretic irreducibility or classification result is used.
