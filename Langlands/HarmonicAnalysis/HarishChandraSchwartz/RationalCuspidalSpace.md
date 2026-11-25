# The integrable cuspidal kernel on actual rational points

This is a construction and elementary proof module for Waldspurger,
*La formule de Plancherel pour les groupes p-adiques*, 2003, III.6
and VIII.2.1 (printed pp.321–322). The registered source is
`waldspurger-2003-plancherel`, DOI 10.1017/S1474748003000082.

`rationalCuspidalSubmodule` is a complex submodule of the published
`RationalSchwartzSpace hKc hPK ρ`, with its actual Xi and matrix height.
For every finite subset `I` of the simple relative roots other than the
whole simple-root set, every Haar measure on the actual group
`standardUnipotentPoints i ν (rootSet i ν I)`, and every pair `x,y`
of actual rational points, its functions satisfy absolute integrability
and `∫ u, f(x u y) = 0`. No new spectral index is introduced. These
are the standard parabolics for the chosen torus and chamber, with all
translates; this module does not prove their comparison with all
semistandard parabolics.

The generic `IsIntegrableUnipotentCuspidal` condition and its submodule
are internal constructions. Additivity uses integrability of both
summands before applying `integral_add`; scalar closure uses
`integral_const_mul`. This avoids treating the totalized Bochner
integral as an additive operator on divergent functions.
`isIntegrableUnipotentCuspidal_iff_constantTermInd` proves equivalence
with the actual normalized formula
`δ(m)^(1/2) ∫ u, f(g₂⁻¹ m u g₁)` together with integrability.
The reverse implication evaluates at `m=1`, `g₁=y`, `g₂=x⁻¹`.
`mem_rationalCuspidalSubmodule_iff_constantTermInd` applies this to
every proper standard parabolic.

`rationalCuspidalLevel` and `rationalCuspidalLeftLevel` intersect this
kernel with actual bi-invariance and left invariance under a subgroup.
Their membership, inclusion and refinement laws are proved; smaller
subgroups give larger levels. They apply in particular to compact open
subgroups. Empty simple-root sets impose no conditions, as proved by
`rationalCuspidalSubmodule_eq_top_of_simpleRoots_empty`; rank zero is
not excluded.

`rationalConstantTermIndVanishes_of_mem_rationalCuspidalSubmodule`
imports the published
`isUnipotentCuspidal_iff_rationalConstantTermIndVanishes`.
Its `ConstantTermEstimate`, Levi Iwasawa pair, connected reductivity,
maximal split torus and generic cocharacter assumptions are explicit.
This is an auxiliary comparison to the Schwartz-valued operator,
not a proof of the constant-term estimate.

All field characteristics are allowed, including positive
characteristic, and neither splitness nor quasi-splitness of the
reductive group is assumed. The topology is the canonical rational-point
topology, with affine and locally finite type hypotheses. The torus,
cocharacter, compact open subgroup, Iwasawa pair and matrix height remain
visible. The construction itself is defined without reductivity;
its interpretation as cuspidality uses the stated reductive setting.

In VIII.2 Waldspurger first constructs `°f = f − κ(ψ)`, with `ψ`
the proper-parabolic Fourier family. This uses the preceding isometry
and induction on strictly smaller semisimple rank. VIII.2.1 identifies
its image with vanishing of all proper semistandard induced constant
terms. Neither direction of that recursive-image comparison is proved
here. The all-standard/semistandard comparison and the removal of
integrability from the kernel description remain separate analytic
targets. The intrinsic semistandard index is the separate
`SemistandardSpectralIndex`; the recursive projector, VIII.2.2, VIII.2.3, VIII.3 and VIII.4 analytic
proofs remain open. No arbitrary projector or same-rank spectral
finiteness is used.
