# Conjugation of subgroup images and relative restriction

This internal module proves that the actual conjugation construction commutes
with restriction of arbitrary all-test subgroup functors. It uses the exact
`pulledBackPoint` from the representation interface, so its action convention
is the convention already used in `ModuliRepresentation.IsEquivariant`.

`baseChangeBasePointsEquiv_pulledBackPoint` identifies that point under the
actual pullback adjunction. `pulledBackPointHom` proves compatibility with the
group law. `familyPointsEquiv_constantPoint` compares the constant families on
every relative scheme test by their projections to the original group.
`mem_conjugateImage` tests conjugate membership by inverse conjugation.
Since the family-point adjunction is a multiplicative equivalence, these facts
give `restrictImage_conjugateAt`.

For a supplied homomorphism `r : U → P`, `subgroupConjugationAction r T` is
the actual action of `U(T)` on subgroup functors of the actual pullback `P_T`.
The action sends a subgroup to its conjugate by the image of the point of `U`.
`restrictImage_smul` proves the action's compatibility with restriction along
every morphism of tests. The base and all geometric objects stay in the same
arbitrary universe `u`; subgroup-functor values lie in `Type (u+1)`.

These are internal consequences of the published group-point and pullback
constructions and the separately submitted moduli interface. They provide the
naturality required by the conjugation action in Conrad, *Reductive group
schemes* (2014), Corollary 5.4.6, p.178, registered source
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
This module acts on all subgroup functors and does not yet prove preservation
of the relative Levi predicate under arbitrary base change or any torsor
existence assertion.
