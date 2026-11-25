# A finite outer component containing a prescribed generic isomorphism class

`FiniteGenericOuterClassExistenceStatement` is a proposition in every
universe. Let `R` be a commutative domain DVR with specified fraction
field `K`, and let `G` and `H` be reductive groups over `Spec R` with a
specified actual generic isomorphism `f`. For every supplied relative
full-centre adjoint quotient `hq`, representing isomorphism scheme `I`,
and actual outer quotient `O` for its descended inner action, the
proposition asserts a `FiniteGenericOuterClass` of the point
`I.classify (LocalGroupIso.ofBaseChangeIso f)`.

Concretely, the conclusion supplies a scheme finite over `Spec R`, a
morphism from it to `O.parameter`, and an actual `K`-point of that finite
scheme whose image equals the outer class of the specified `f`. The
classifying point retains the complete natural local family of `f`,
through the actual-base-change equivalence. The finite scheme need not
be supplied as an open or closed subscheme, or with an étaleness proof:
those stronger facts are unnecessary for this consumer. The whole
outer scheme is not asserted finite.

The original source is Brian Conrad, *Reductive group schemes* (2014),
Theorem 7.1.9(1), pp.245–247, the outer-point discussion on p.259, and
the proof of Theorem 7.2.16 on p.261. It is registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The theorem gives a separated étale locally constant outer
automorphism scheme. Its finite-component proof applies more generally
to every étale locally constant scheme over a normal locally
noetherian base (pp.246–247). The outer-isomorphism sheaf of two étale
forms is a torsor under that outer automorphism scheme, as in the
argument on p.261, so the same component argument applies.

A DVR is normal and noetherian. The connected component containing
the image of the specified generic outer class is therefore finite
étale over `Spec R`. Taking that component and its inclusion gives the
data requested here. For arbitrary supplied `I` and `O`, deriving this
statement also requires identifying their represented fpqc quotient
with that outer-isomorphism sheaf. This is part of the geometric
argument, not an extra premise. The Library proves the statement as
`finiteGenericOuterClassExistence` (module
`FiniteGenericOuterClassExistenceProof`).

The general-DVR scope is derived from the geometric part of the cited
argument. Henselianity and finite residue are used subsequently in
Conrad to trivialize adjoint torsors; they are unnecessary for the
finite-component assertion and are absent here. This module supplies
a proposition-valued definition and does not prove it. Extending the finite-scheme
point and constructing its actual fibre are separately implemented by
`FiniteGenericOuterClass.integralClass` and
`GenericInnerIsomorphismTorsor.ofOuter`; they do not prove this
finite-component existence assertion.
