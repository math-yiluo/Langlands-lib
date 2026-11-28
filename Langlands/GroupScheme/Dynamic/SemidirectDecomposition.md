# The semidirect product of represented dynamic subgroups

Let \(G\) be a separated group scheme over a scheme \(S\) and let
\(\chi:\mathbb G_{m,S}\to G\) be a cocharacter. Assume that \(P_G(\chi)\),
\(Z_G(\chi)\), and \(U_G(\chi)\) are represented by the supplied group schemes
\(P\), \(Z\), and \(U\) with their maps to \(G\). These functors are defined
on every test scheme over \(S\), including nonreduced schemes.
`Dynamic.semidirectProductIso` is an isomorphism \(U\rtimes Z\simeq P\) in
`Grp (Over S)` for `Dynamic.centralizerAdjointAction`, with action
\((z,u)\mapsto zuz^{-1}\). `Dynamic.semidirectProductIso_hom` identifies its
underlying scheme map with `Dynamic.multiplication`, which sends \((u,z)\)
to \(uz\).

The construction uses `Dynamic.centralizerToParabolic` for the Levi inclusion
and `Dynamic.unipotentIsoKernel` followed by the kernel inclusion for
\(U\to P\). The conjugation identity in \(P\) follows from the identity in
\(G\) by cancellation against the representing monomorphism \(P\to G\).
`Dynamic.subgroupMultiplication_eq_multiplication` identifies multiplication
of the inclusions with the scheme isomorphism given by
`Dynamic.isIso_multiplication`. `AutomorphicAction.semidirectFactorIso` lifts
this map to an isomorphism of group schemes using the conjugation identity.

This is the represented cocharacter form of Conrad, *Reductive group schemes*
(2014), Theorem 4.1.7(1), (3) and its proof, printed and PDF pp. 112–114
(`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`).
Conrad treats \(\mathbb G_m\)-actions on finitely presented affine groups
over a ring and establishes representability. The Lean construction takes
representatives as inputs and applies over any base scheme for the action
by conjugation through \(\chi\).
