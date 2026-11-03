# A fixed split torus containing the full centre

Worker 1372.

`FixedCenterContainingTorusStatement.{u}` is an unproved structural proposition
target. Over every algebraically closed field `k : Type u`, a connected
reductive group `G` with an actual automorphic action of a split torus `S`
admits a closed split torus `j : T ⟶ G` that contains the full scheme-theoretic
centre of `G` and is fixed pointwise by `S`.

The centre containment is an inequality of subgroup functors on all schemes
over `Spec k`. The fixedness identity also quantifies over every such test
scheme, every acting point and every point of `T`. Thus both assertions include
nonreduced tests. No smoothness or reducedness of the centre is assumed, and
no semigroup or comparison proposition occurs in the hypotheses.
`IsConnectedReductive G` supplies the usual smooth, affine and connected
conditions with trivial geometric unipotent radical. The conclusion does not
require the chosen torus to be maximal.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition
(2015), registered as `conrad-gabber-prasad-2015-pseudo-reductive`, in the proof
of Proposition 3.3.10(c), printed p.113 / PDF p.139. After reducing to an
algebraically closed field and a connected reductive group, the source uses
Corollary A.4.7(2) to factor the torus action through `G/Z(G)`. Choose a maximal
torus in that adjoint quotient containing the acting image, and lift it to the
corresponding maximal torus of `G`. This torus contains the full centre; the
conjugation action through its quotient fixes it. Over the algebraically closed
field it is split. Corollary A.4.7(2) and its proof occur on printed pp.495–497 /
PDF pp.521–523; the proof treats actual group functors and their base changes.

The exact proposition is derived from that argument: it records only the
fixed closed split torus and centre containment needed by the semigroup
application, rather than an adjoint action factorization or maximality.
Constructing the quotient action, lifting the torus and establishing the
all-test identities remain obligations of a separate proof.

The companion module `Rational.SemigroupCenterContainment` proves a generic
fixed-torus semigroup inclusion and deduces full-centre containment
conditionally on this structural proposition. Neither module proves this
proposition or the full semigroup comparison.
