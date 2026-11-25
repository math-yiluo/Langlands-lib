# The relative Levi moduli is a unipotent-radical torsor

`Langlands.GroupScheme.relativeLeviTorsor.{u}` proves exactly the published
`Langlands.GroupScheme.RelativeLeviTorsorStatement.{u}`. The base scheme and
universe are arbitrary. For a relative parabolic in a reductive group and a
supplied relative unipotent radical, the theorem constructs an actual
representing scheme, its actual radical action, the natural correspondence
with all-test Levi subgroup images, conjugation equivariance, and the fpqc
torsor properties required by the statement.

The proof first isolates the assembly in `relativeLeviTorsor_of_sheaf`.
Its two hypotheses are Zariski sheafness and the singleton sheaf condition
for every surjective etale morphism between arbitrary tests, uniformly over
all the parabolic and radical data. On every affine open of the base,
arbitrary parabolic base change preserves the supplied radical and the
Levi restriction predicate. Dynamic local parabolic descriptions give local
Levi images; Zariski gluing on the disjoint union of those tests and affine
etale refinement give a section over an affine surjective etale test.
Unique radical conjugacy makes the actual moduli presheaf a naturally
simply transitive radical presheaf.

The affine cocycle construction uses this local point and the singleton
sheaf condition to represent the actual presheaf on every scheme test.
The radical is affine and smooth, so the resulting model is affine,
smooth and surjective. These models glue over the standard affine open
cover of the original base. The canonical comparison of direct and
iterated subgroup pullbacks identifies the changed-base moduli problem
with restriction of the original presheaf during this gluing.

The representing correspondence transports the actual presheaf action to
the representing scheme, so its equivariance is precisely conjugation by
the image of the supplied radical point. Simple transitivity makes the
actual `ModObj.leftSMul` morphism an isomorphism. Smoothness gives flatness,
affineness gives quasi-compactness, and surjectivity is retained from the
local models. These are all the conclusions of the published target.

The unconditional theorem discharges both sheaf hypotheses using
`moduliFunctor_isSheaf_zariski` and `moduliFunctor_isSheafFor_etale`.
Their explicit stability hypotheses follow from
`restrictionStable_of_parabolic` and `IsRelativeUnipotentRadical.baseChange_parabolic`.
The sheaf results come from effective descent of matching actual Levi
images, with equality detected on the covering family. No global Levi,
section over the original base, or affine torsor vanishing is assumed.

The geometric source is Brian Conrad, *Reductive group schemes* (2014),
Definition 5.4.2, p.174, Proposition 5.4.5, pp.177–178, and Corollary 5.4.6
with proof, p.178; source identifier
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The implemented proof factors this argument through the Library's actual
subgroup descent, cocycle torsor construction and Zariski representation
gluing APIs.
