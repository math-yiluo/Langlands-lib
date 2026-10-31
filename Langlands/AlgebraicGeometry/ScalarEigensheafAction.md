# Commuting actions on scalar eigensubsheaves

This internal construction restricts an actual ring action on a module
sheaf to its simultaneous scalar eigensubsheaf. Let `ρ : R →+* End M`
and `χ : R →+* Γ(S, ⊤)` define `scalarEigensheaf ρ χ`.
Given another action `σ : A →+* End M` commuting with every `ρ r`,
`scalarEigensheafAction` constructs a ring homomorphism
`A →+* End (scalarEigensheaf ρ χ)`.

Each endomorphism is the previously constructed restriction
`scalarEigensheafMap` of `σ a`. Its ring laws follow on actual sections
from the ambient ring homomorphism and subtype extensionality.
The multiplication proof respects `End` multiplication:
`f * g = g ≫ f`. The section formula and equivariance of the actual
inclusion are proved.

`scalarEigensheafMap_intertwines` proves that a sheaf morphism
intertwining both ambient actions also intertwines these constructed
restricted actions. On sections the equation is exactly the ambient
intertwining equation.

This is an internal consequence of the actual scalar eigensubsheaf
construction; it introduces no literature theorem or geometric hypothesis.
The rings may be noncommutative, and the scheme may have nilpotents.
No tensor-factor interpretation, splitting, rank, or base-change theorem
is asserted.
