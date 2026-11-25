# The clopen inner-action locus for reductive group schemes

`Langlands.GroupScheme.reductiveInnerActionLocus.{u}` proves
`Langlands.GroupScheme.ReductiveInnerActionLocusStatement.{u}` for every
universe `u`. It takes the supplied full-centre fppf quotient and compatible
action from that proposition, over an arbitrary base scheme and with
arbitrary acting and test group schemes.

The proof applies `reductiveInnerActionLocus_of_geometry` to
`reductiveAutomorphismSchemeGeometry` and `relativeAdjointQuotientExistence`.
The first theorem supplies the full self-isomorphism scheme and a separated
étale outer parameter. The second gives an affine full-centre quotient,
which the reduction proves reductive. The quotient comparison then transfers
reductivity to the supplied quotient target and identifies the supplied
action with its canonical inner action by uniqueness.

The reduction equips the self-isomorphism scheme with its represented
group structure. It identifies the canonical inner classifier with
inversion followed by the orbit through the identity. That orbit is
isomorphic to the fibre over the identity class. The section of the
separated étale parameter is open and closed, so the orbit and the inner
classifier are open and closed immersions.

The pullback of the two action classifiers in group schemes gives `K` and
its projections `j` and `φ`. Stability under pullback proves that `j` is
an open and closed immersion. The classifier identifies equality of
restricted actions with equality of the corresponding homomorphisms.
The pullback therefore gives `c.restrict φ = a.restrict j` and the unique
lift for each compatible pair `h` and `x` on an arbitrary test group
scheme. The construction applies over empty and nonreduced bases.

This is an internal composite proof of the derived consequence of Brian
Conrad, *Reductive group schemes* (2014), Theorem 7.1.9(1), pp. 245–246,
recorded in the target module. The registered source is
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
