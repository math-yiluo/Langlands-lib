# Finite fixing fields and Krull continuity on actual components

Author: Worker 1604.

This is an internal derived proof of the exact published proposition
`Langlands.GroupScheme.IdentityComponent.ComponentGaloisKrullContinuityStatement`.
It combines the published actual-component and affine-coordinate constructions
with Mathlib's finite algebra generation and Krull topology. It introduces no
external literature premise. The fields have the same arbitrary universe, the
base field is arbitrary, and the algebraically closed coefficient extension is
assumed only algebraic. Smoothness and affineness are the hypotheses of the
published target.

The helper `exists_finite_fixing_algHoms` takes finitely many algebra maps from a
finite-type algebra into the algebraic extension. Choose a finite algebra
generating set, collect its values under all of the maps, and adjoin these
finitely many elements to the base field. Algebraicity makes this intermediate
field finite dimensional. An automorphism in its fixing subgroup agrees with
the identity on all the collected values. Algebra-homomorphism extensionality
on the chosen generators proves that it fixes every value of each map.

For the group scheme, the algebra is its actual affine coordinate ring. The
finite family of maps consists of the coordinate maps of the published chosen
actual rational representative in every component of the actual base change,
transported through `baseChangeCoeffEquiv`. Local finite type follows from
smoothness and supplies finite type of this coordinate algebra. The coordinate
comparison is injective and commutes with coefficient conjugation, so the
constructed field's fixing subgroup fixes the representatives as actual points.
The published representative criterion then places this fixing subgroup in
`componentGaloisKernel`.

Mathlib's Krull topology makes the fixing subgroup of every finite intermediate
field open. A subgroup containing an open subgroup is open, which gives
openness of the actual action kernel. The canonical image projection equals
one on that kernel and is therefore eventually one near the identity; continuity
of a homomorphism follows from continuity at the identity. Finally, both the
published finite effective image and the actual component space are discrete.
Evaluation of the image action is continuous, and composing it with the
continuous projection on the first factor proves joint continuity of the
original coefficient action. The component topology is precisely the existing
connected-component quotient topology with its published discreteness instance.

The final theorem `componentGaloisKrullContinuity_proof` assembles these four
conclusions with exactly the named proposition as its type. No perfection,
separability, finite-dimensionality of the full coefficient extension or
connectedness hypothesis is added; no fixing-field or continuity conclusion is
assumed.
