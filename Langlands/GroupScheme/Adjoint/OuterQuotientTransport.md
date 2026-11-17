# Outer-quotient transport between full-centre quotient representatives

This is a derived construction from the published descent of morphisms through
full-centre fppf quotients and the supplied relative adjoint quotient interface.
It supplies no new quotient existence theorem and uses no external source.

For two supplied maps `q : G ⟶ A` and `p : G ⟶ B` satisfying
`IsRelativeAdjointQuotient`, `IsRelativeAdjointQuotient.quotientIso` is the
canonical group-scheme isomorphism `A ≅ B` induced by the identity on `G`.
It commutes with `q` and `p`.

`innerAction_quotientIso` identifies their descended conjugation actions on
every relative test scheme. To prove equality at an arbitrary `A`-point, the
proof passes to the canonical fppf cover on which that point lifts through `q`.
There the commuting quotient square and the conjugation restriction laws
identify both actions. The cover is an effective epimorphism, so equality
descends. This argument does not assume a global lift of the acting point.

`OuterIsomorphismScheme.changeAdjointQuotient` then applies
`changeActingGroup` along the canonical quotient isomorphism. It preserves
the class parameter and class morphism and transfers the exact all-test
unique-difference property, including on nonreduced tests. No additional
base, splitting, characteristic or smooth-centre hypothesis is imposed.
