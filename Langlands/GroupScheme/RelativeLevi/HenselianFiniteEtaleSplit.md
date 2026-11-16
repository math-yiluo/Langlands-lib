# Finite étale splitting data over a Henselian local ring

`Langlands.GroupScheme.henselianFiniteEtaleSplitData` constructs a chosen
local finite étale splitting algebra and full splitting data for a reductive
group scheme over the spectrum of a Henselian local commutative ring `R`.
It works in every universe and requires neither a finite residue field nor
Noetherianity.

Its dependent tuple contains the carrier `R'`, its commutative local ring
and `R`-algebra structures, certificates that it is étale and module-finite
over `R`, a finite coordinate type `I`, and an actual homomorphism
`𝔾_m^I → G_{R'}`. The homomorphism is closed and a maximal torus on every
residue-field fibre. The tuple also contains a root index type `J` and a
full root datum `P` on the coordinate lattices. This is the torus root
datum on every field-valued fibre, and every actual root exponent weight
space of the Lie algebra is `R'`-linearly isomorphic to `R'`. The
isomorphisms are certified by `Nonempty`; the tuple does not choose
bases of the root spaces.

The construction applies the published
`exists_etale_affine_split_maximalTorus` at the closed point to obtain
an affine étale neighbourhood with a closed fibrewise maximal coordinate
torus. The published unconditional
`Langlands.CommutativeAlgebra.henselianFiniteEtaleRefinement` supplies a
local finite étale algebra `R'` and an actual factorization of
`Spec R' → Spec R` through this neighbourhood. The published
`localSplitDataOfFactoredNeighbourhood` pulls back that torus, identifies
the ambient group with `G_{R'}` using the factorization, and supplies its
full root datum and rank-one root spaces over the local ring `R'`.
Classical choice selects the resulting dependent tuple.

The provenance is internal assembly of these published results. This
construction gives the finite étale splitting part of
`HenselianFiniteResidueQuasiSplitStatement` without a residue-field
finiteness assumption. It does not assert quasi-splitness over the original
base; the unchanged full target still requires that separate conclusion.
