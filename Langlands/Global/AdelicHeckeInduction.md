# Half-twisted adelic sections induced from actual block Hecke characters

Author: Worker 2. Provenance: internal specialization of the actual block
Hecke representation and half-twisted adelic section construction. This unit
claims no new identification with original literature.

The number field `F : Type uF` has arbitrary universe. Every natural rank `n`
and positive ordered block shape `B` is allowed, including the empty shape in
rank zero. Each `χ_i` is an actual continuous complex Hecke character on the
actual idele-class group; unitarity and finite order are not assumed.

`inducingCharacter` is the continuous product of the constructed positive
complex half-character and the actual block Hecke character, inflated to the
actual adelic parabolic. Its scalar value is
`(∏_i χ_i^(B.size i)).onIdeles(z)`: the positive half is one on common scalar
ideles and the block Hecke character has the displayed rank exponents.
The character is one on the actual rational parabolic and unipotent radical
by the two factors' proved restriction laws. `inducingRepresentation_apply`
identifies the generic coefficient action with multiplication by this
concrete character using associativity of complex multiplication.

`Sections` consists of actual complex valued covariant functions on the full
adelic matrix group. `covariance` expresses its defining condition as
`f(p * g) = inducingCharacter(p) * f(g)`. Its proved rational restriction gives
`rationalParabolic_invariance`; this is invariance under the rational
parabolic subgroup. Full rational matrix invariance is not asserted.

`FiniteSmoothSections` further requires one common open finite-factor
stabilizer. `SmoothSections` requires this and real smoothness of every
archimedean slice in the actual mixed matrix coordinates. Both are precisely
the existing actual function subspaces specialized to the one-dimensional
block Hecke representation. `finiteSmoothInduced` and `smoothInduced` are
the resulting full adelic right actions. `evaluate_smoothInduced` records
the actual translation formula `f(x) ↦ f(x * g)`. The general construction
already proves finite-factor smoothness, continuity of full smooth sections
and their faithful realization in continuous functions; those apply here
without a new choice of carrier or topology.

`leviRepresentation_scalar` proves that common scalar ideles act on the
coefficients by the actual rank-weighted Hecke character. Applying the
generic scalar-action laws gives `finiteSmoothInduced_scalar` and
`smoothInduced_scalar` on the two actual induced spaces. These are proved
identities for every section, without an assumed central-character law.

The section spaces may be zero; no nonzero section is constructed here.
The positive half has not been identified with Haar scaling, so the name
half-twisted retains that normalization boundary. No completed or unitary
induction, full rational invariance, automorphic realization, irreducibility,
local tensor decomposition or isobaric classification is asserted.
