# Actual outer-isomorphism quotients for reductive groups over a DVR

Worker 217.

`GenericOuterIsomorphismSchemeExistenceStatement` works in every universe
over a commutative domain DVR `R` with specified fraction field `K`.
The groups `G` and `H` are reductive and have a specified actual generic
isomorphism. Given any actual full-centre quotient `q : G ⟶ A` satisfying
`IsRelativeAdjointQuotient q` and any
`I : GroupIsomorphismScheme G H`, it asserts a nonempty
`OuterIsomorphismScheme I hq.innerAction`.

The conclusion supplies an actual relative class scheme and a morphism
from `I.parameter` to it that is flat, surjective and quasi-compact.
The class is invariant under the canonical left action by inverse
precomposition, using the relative adjoint inner action. On every
relative test scheme, every pair of isomorphism points with equal class
differs by a unique `A`-point under this action. Existence of that
difference is required on the original test scheme, including nonreduced
tests; no global lift of the `A`-point to `G` is required.

This is a derived Isom version of Brian Conrad, *Reductive group schemes*
(2014), Theorem 7.1.9(1) and its proof, pp.245–247, with the forms
argument of Theorem 7.2.16 on p.261. Source:
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The original constructs the actual automorphism scheme, its closed
inner subgroup `G/Z_G`, and its separated étale locally constant outer
quotient as an exact sequence of sheaves. For groups that are étale
forms of each other, descent gives the corresponding outer-isomorphism
scheme. Its class morphism is an adjoint torsor, and hence an fpqc
morphism with invertible shear. The latter is exactly the asserted
unique-difference property on every scheme test. Inverse precomposition
gives the left-action convention used here; taking an inverse does not
change the quotient classes.

The supplied quotient may be any full-centre quotient with the stated
reductivity. Its identification with the adjoint quotient, and
compatibility of its descended inner action, are part of deriving this
formulation. The proposition asks only for the quotient and orbit data
needed by `OuterIsomorphismScheme`; it does not assert that the whole
Isom or outer scheme is quasi-compact or finite. Such an assertion would
exclude higher-rank tori, whose automorphism components can be infinite.

No representability proof, finite outer component, integral outer
section, or torsor section is supplied by this module. There are no
henselian, completeness, residue-finiteness, splitting, or characteristic
assumptions. This is an unproved proposition-valued definition.
