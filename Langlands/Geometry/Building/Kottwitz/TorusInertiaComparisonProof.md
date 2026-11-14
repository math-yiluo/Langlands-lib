# Residual Galois comparison of torus inertia targets

This module proves
`Langlands.Geometry.Building.Kottwitz.TorusInertiaComparisonStatement`.
The theorem `torusInertiaComparison_proof` establishes unique existence of the
representative-characterized comparison, the selected map's specification,
bijectivity, and equivariance for the actual residual group `Aut_k(K)`.

The contextual source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Construction 11.3.1, Fact 11.3.5, Lemma 11.3.6 and the inertia targets
in §11.5, printed pp. 427–430 / PDF pp. 458–461 in the registered copy,
source ID `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' 1 November 2024 corrections do not change these items.
The present comparison after inertia descent is an explicit consequence of
the torus identification and Galois functoriality, rather than a separately
numbered assertion in the source.

The implemented descent packages the bijective and absolute Galois equivariant
comparison as an actual representation equivalence. `inertiaEquiv` descends
that equivalence and its inverse to the actual integral inertia quotients.
Its representative formula gives `IsTorusInertiaComparison`; uniqueness follows
from the quotient projection's universal property. Classical epsilon therefore
selects this same map. Bijectivity and residual `Aut_k(K)` equivariance follow
from the descended equivalence and `inertiaMap_equivariant`. That equivariance
lemma lifts each residual automorphism to an absolute one and checks the
identity on quotient representatives, so it uses the existing residual action.

The intermediate theorem
`torusInertiaComparison_of_fundamentalComparison` records this descent as an
internal implication from `TorusFundamentalComparisonStatement`. The final
theorem supplies the published `torusFundamentalComparison_proof`, so no
comparison isomorphism or existence assertion remains as a premise.

The tower and torus hypotheses are exactly those of the target. In particular,
the codomain is the actual `torusInertiaCoinvariants` used by the torus
Kottwitz homomorphism, and the residual group is the actual automorphism group
of `K/k`. There is no assertion about surjectivity on residual invariants.
