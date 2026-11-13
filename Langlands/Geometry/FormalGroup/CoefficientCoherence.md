# Coherence of formal-module coefficient extension

This module proves the comparison laws for coefficient extension of the
finite-coordinate formal O-modules constructed in `FormalModule`. The
comparison `mapIdIso` identifies extension along the identity with the
original law. The comparison `mapCompIso` identifies two successive
extensions with extension along the composite. Both comparisons use the
identity coordinate map.

`mapIdIso_natural` and `mapCompIso_natural` prove that these comparisons
commute with integral O-linear formal homomorphisms. The proofs compare
coordinate maps, remove identity compositions and apply the coefficient
identity and composition formulas. `Iso.ext_hom` proves that an integral
isomorphism is determined by its forward map: the two inverse equations
force the inverse to be unique.

`mapCompIso_id_left` and `mapCompIso_id_right` prove the two unit laws.
`mapCompIso_assoc` proves that the two routes from three successive
coefficient extensions to extension along their composite agree. All the
comparison maps have identity coordinates; mapping such a map again
preserves its coordinates. The equality is of actual formal-module
isomorphisms, including their forced inverses.

`mapSquareIso` constructs the identity-coordinate isomorphism between the
two successive base changes around any commutative square of coefficient
O-algebra maps. Its naturality equation is proved by comparing the two
composite coefficient maps. This does not require the maps to be flat.

The `RationalHom` namespace proves the same identity, composite and square naturality equations on the
actual tensor-product rational Hom. Tensor induction reduces them to the
integral equations and multiplication by one in the field. In the
`QuasiIsogeny` namespace, the equations are equalities of quasi-isogenies,
obtained by extensionality of their forward rational maps. The domain and
fraction-field hypotheses on quasi-isogenies are retained.

These are derived comparison laws for the coefficient extension already
constructed in `ModuleBaseChange`, motivated by the formal modules and
quasi-isogenies in Drinfeld, *Coverings of p-adic Symmetric Regions*
(1976), §1, printed p.108, and §2 A, printed p.109. They supply algebraic
coherence for changing the base of a moduli object. They assert no
nilpotent-thickening rigidity, local gluing, height or representability
result.
