# Assembling derived central isogenies from existence and multiplication

This internal reduction preserves the published
`ReductiveDerivedCentralIsogenyStatement` and derives its quotient-pairing
clause from its multiplication clause. Its provenance is the proved generic
transfer in `CentralIsogeny.QuotientPairing`, together with the definitions in
the target module. It introduces no new external structural theorem.

`ReductiveDerivedMultiplicationStatement` retains precisely the following
parts of the original target, in every universe and over every base scheme:

- Every reductive group scheme has a maximal central relative torus.
- For every supplied closed normal semisimple subgroup `d : D ⟶ G`, every
  represented fppf quotient `q : G ⟶ Q` by its full range with `Q` a relative
  torus, and every maximal central relative torus `z : Z ⟶ G`, the actual
  multiplication `prodHom z d (hz.commute_values d)` is a central isogeny.

Here semisimplicity has exactly the original hypotheses: `D` is reductive
and every geometric fibre is semisimple. The local maximal-central-torus
predicate is copied verbatim from the original statement: closedness,
centrality, being a relative torus, and greatestness among closed central
relative tori as subgroup functors on every test scheme.

`ReductiveDerivedCentralIsogenyReductionStatement` asserts equivalence of
the original target with this existence-and-multiplication proposition.
The theorem `reductiveDerivedCentralIsogenyReduction` proves the equivalence,
and `reductiveDerivedCentralIsogeny_of_multiplication` exposes its assembly
direction directly.

For assembly, the proof keeps the given existence and multiplication
conclusions. Closedness of `d` and `z` gives monomorphisms of their underlying
maps in `Over S`. Centrality of `z` supplies the required commutation.
Applying `isCentralIsogeny_quotientPairing_of_prodHom` to the two supplied
fppf quotients proves that the actual pairing
`lift q p : G ⟶ Q ⊗ P` is a central isogeny for every quotient `p` by the
full range of `z`. The generic transfer requires no quasi-compactness
hypotheses on `q` or `p`. The converse simply keeps the original existence
clause and projects the multiplication clause from its conjunction.

This module proves a conditional equivalence. It does not supply a maximal
central torus or establish the initial multiplication isogeny. Those
structural obligations remain necessary to prove the unchanged original
target unconditionally.
