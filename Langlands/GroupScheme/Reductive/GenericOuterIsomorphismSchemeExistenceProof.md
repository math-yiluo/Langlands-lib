# Existence of actual outer-isomorphism quotients over a DVR

`Langlands.GroupScheme.genericOuterIsomorphismSchemeExistence` proves
`Langlands.GroupScheme.GenericOuterIsomorphismSchemeExistenceStatement.{u}`
for every universe `u`. It applies
`genericOuterIsomorphismSchemeExistence_of_pinnedCharts` to the published
proof `pinnedOuterIsomorphismChart`.

The reduction uses the two actual pinned étale atlases to obtain a common
fppf covering sieve. On its tests the pinned chart gives a unique
decomposition into an adjoint point and a point of an actual constant scheme
of labels. Source and target transport put those charts in the supplied Isom
representative with the inner action of the supplied full-centre quotient.
Effective descent gives the class scheme from the separated locally
quasi-finite local quotients. The theorem specializes this arbitrary-base
construction to `Spec R` for the given DVR.

The returned `OuterIsomorphismScheme` has a flat, surjective and quasi-compact
class morphism, invariant under inverse precomposition. On every relative
test scheme, including nonreduced tests, two points with the same class
differ by a unique adjoint point on that test. The descent uses the faithful
action of the full-centre quotient and requires only local lifts to the
source group.

This proof composes two published Library results for the derived Isom
statement. Its provenance is the pinned splitting and descent of the outer
quotient in Conrad's *Reductive group schemes* (2014), Theorem 7.1.9(1), (3)
and its proof, pp. 245–247, with the pair interpretation of the forms argument
in Theorem 7.2.16, p. 261. The registered source is
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
