# Smooth valuation stalks and their localized Picard groups

This internal construction connects the imported smooth valuation algebra
regularity theorem to actual scheme stalks. All rings and schemes lie in
one arbitrary universe. The scheme morphism is smooth; the valuation domain
can have any rank and can be a field. No global finite-presentation,
properness, connectedness, or integrality assumption on the scheme is added.

`SmoothStalkModel R A` records an actual smooth coefficient algebra, a prime,
and a ring equivalence from the corresponding prime localization to `A`.
`smoothStalkModel` constructs this data for the actual stalk of a scheme
smooth over `Spec R`: it chooses an affine chart through the point, takes
the chart's actual ring of global sections, and uses the structure morphism
to define its coefficient map. The map is smooth by the affine
ring-homomorphism property of a smooth morphism and the canonical
global-sections equivalence for `Spec R`. The affine localization theorem
and the open immersion's stalk isomorphism give the displayed actual
local-ring equivalence.

The imported smooth algebra theorem proves regularity of the model's prime
localization. Ring-equivalence transport therefore proves regularity of the
actual scheme stalk. Here regularity means precisely the existing
`FinitelyPresentedRegularRing` conjunction: finite submodules of finite free
modules are finitely presented, and every finitely presented module in the
ring's universe has some finite projective-dimension bound. This is not an
assertion of Noetherian regular local ring structure.

Picard vanishing is also transported to any actual algebra model of a
localization. The proof first uses the imported coherent regular local-ring
theorem for `Localization M`, then the canonical localization equivalence.
Ring-equivalence invariance of trivial Picard groups follows from the
composition and identity laws for Mathlib's actual `Pic.mapRingHom`.
Consequently every invertible module on any such localized stalk model has
an actual linear equivalence to that model ring, by Mathlib's free
invertible module characterization.

This pair does not construct a scheme line-bundle extension or identify
the canonical generic self-product map with one of these algebra models.
Its provenance is the explicit internal derivation above from the imported
algebra results and Mathlib's affine-chart and stalk constructions.
