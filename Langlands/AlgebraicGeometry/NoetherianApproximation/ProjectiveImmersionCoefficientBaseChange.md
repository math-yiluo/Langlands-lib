# Projective immersion models over a specified coefficient ring

`ProjectiveImmersionRingModelData R F X n j` records an actual model of a
specified projective map j : X → Pⁿ_F over a specified commutative coefficient
ring R equipped with an algebra map to the field F. It gives a scheme X_R,
an immersion m : X_R → Pⁿ_R, a locally finitely presented quasi-compact structure
morphism m followed by Pⁿ_R → Spec R, and a comparison p : X → X_R. The square
with structure maps and the specified Spec F → Spec R is Cartesian. The
comparison also satisfies p followed by m equals j followed by the canonical
projective coefficient map Pⁿ_F → Pⁿ_R. Every ring, field and scheme lies in an
arbitrary common universe; n may be zero.

Given finite coefficient model data D from
`ProjectiveImmersionSubalgebraModel`, write A for its actual integer subalgebra
of F. `projectiveImmersionCoefficientBaseChange D R` constructs the preceding
model from compatible algebras A → R → F whose composite is the original A → F.
R is any commutative ring with those maps; it need not itself be a subring or
field. The constructor requires no further finiteness, flatness, characteristic
or separability assumption on R or F.

This is derived infrastructure for the quasi-projective arithmetic model chosen
in Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Example 4.2, printed pp.9–10. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
It allows the finite coefficient model to pass to an actual arithmetic
integer ring after the coefficients have been placed there. The arithmetic
placement and the adelic comparison are separate obligations.

The constructed scheme is literally the pullback of D's structure morphism
along Spec R → Spec A. The original-field comparison p is the pullback lift of
D's comparison and the original X → Spec F → Spec R. Pullback cancellation,
using the compatible spectrum maps, proves its Cartesian square. The published
`ProjSpace.isPullback_map` constructs m by its two projections to Pⁿ_A and
Spec R. A second pullback cancellation identifies m as the base change of D's
immersion, so it is an immersion. Local finite presentation and
quasi-compactness of the structure morphism follow from stability under base
change. Finally, the two projections of the same projective coefficient square,
together with D's original-immersion identity and composition of projective
coefficient maps, prove the new original-immersion identity.
