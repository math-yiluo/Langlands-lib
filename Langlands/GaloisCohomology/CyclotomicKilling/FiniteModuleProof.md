# Cyclotomic restriction of finite primary cohomology classes

`numberFieldFiniteModuleCyclotomicKilling` proves
`NumberFieldFiniteModuleCyclotomicKillingStatement`. The proof first bounds
the ℓ-cohomological dimension of a closed subgroup that fixes the ℓ-power
cyclotomic tower and then descends vanishing of a degree-two class to a
finite layer.

## Brauer classes and Kummer cohomology

Given a number field and a Brauer class annihilated by a prime ℓ, take the finite set
of finite places where its localization is nonzero. The cyclotomic local-degree construction
`Langlands.Global.CyclotomicSplitting.exists_pow_dvd_localDegree` supplies a totally complex
subfield of an ℓ-power cyclotomic layer whose local degrees over that set are divisible by ℓ.
Embed the layer in the chosen separable closure and transport the local-degree conditions
along the induced isomorphism of subfields. By `brauerRestriction_eq_zero_of_isComplex`,
the Brauer class restricts to zero there. This is the finite-layer Brauer step of Serre,
*Galois Cohomology*, Chapter II, §3.3(d), Proposition 9 and its proof.

For a closed subgroup \(P\) fixing every layer, a class in \(H^2(P,\mu_\ell)\)
comes from a class on an open subgroup \(U\) containing \(P\) by
`Langlands.ProfiniteCohomology.exists_resOfLE_eq`. The Kummer map sends the class
on \(U\) to an ℓ-torsion class with units coefficients. The isomorphism
`openCohomologyIso` identifies it with a Brauer class over the fixed field of
\(U\). Apply the Brauer step over that number field. The new field is contained
in the compositum of the fixed field of \(U\) and a cyclotomic layer over the
original field, so its fixing subgroup still contains \(P\).

The comparison via `IntermediateField.fixingSubgroupEquiv` identifies the
Brauer restriction with restriction between the corresponding subgroups.
Hilbert 90 makes the degree-two Kummer map injective on the new open subgroup.
Thus the class with \(\mu_\ell\) coefficients restricts to zero there and
hence on \(P\).

## Cohomological dimension and finite layers

For a closed subgroup \(H\) fixing the tower, apply the pro-ℓ Sylow criterion
for ℓ-cohomological dimension. On its pro-ℓ Sylow subgroup, the module
\(\mu_\ell\) is trivial and is additively isomorphic to \(\mathbb Z/\ell\mathbb Z\).
The degree-two vanishing just proved therefore gives
\(\operatorname{cd}_\ell H\leq 1\).

Take \(H\) to be the intersection of the fixing subgroups of the cyclotomic
layers. The dimension bound gives zero degree-two cohomology with the given
finite ℓ-primary coefficients. By `Langlands.ProfiniteCohomology.exists_res_eq_zero`,
the class already vanishes after restriction to an open subgroup containing \(H\).
The layer fixing subgroups are nested and compact, so one of them is contained
in that open subgroup. An intermediate field containing a primitive root of
the chosen order contains every root of that order and thus the entire layer.
Its fixing subgroup gives a further restriction on which the class vanishes.
This finite-layer descent is the restriction argument of Serre, Chapter I,
§2.2, Proposition 8.
