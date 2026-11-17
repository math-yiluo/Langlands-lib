# Plancherel weights on unitary orbits for dynamic parabolics, with density packages

Author: Worker 131, task `b2eba110-082e-4b07-9076-f64b90cd0dc3` (Task 7454, revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.DynamicOrbitPlancherelWeight`,
namespace `Langlands.HarishChandraSchwartz.DynamicInducedOrbit`. It imports only
`Langlands.Representation.Plancherel.StandardLeviPlancherelWeight`.

## Purpose

Item 3 of Task 7454 asks for the lower densities `µ^{M'}` on the conjugated orbits `sO`. Each
`µ^{M'}` is the actual Plancherel density of the lower group `M'` relative to `M' ∩ s·P`, built
from the published weight constructions applied to `M'`, its maximal split torus and the
conjugated cocharacter. Its
continuation data, domains, irreducibility locus and regularity witness must be bundled in an
explicit, named hypothesis package.

The published `standardLeviPlancherelWeight` (module `StandardLeviPlancherelWeight`) is the top
density `µ^G` for a *standard* Levi `M_I` of `G`. Its torus `i` is assumed maximal split. This
module gives the same orbit construction for the Levi `Z_H(χ)(F)` of the actual dynamic
parabolic of any cocharacter `χ = ζ ∘ j` of any connected reductive `H`. Here `j : T ⟶ H` is
arbitrary, so the module is a generic wrapper of the Library expression `plancherelWeight j ζ …`.
That expression is the source density only when `j` is a maximal split torus of `H` (see
"Scope of the source identification" below). The task applies the module with
`H = M' = Standard.leviScheme i ν J'`, `j = Standard.leviTorusHom i ν J'` (maximal split) and the
cocharacter of `M' ∩ s·P`.

## Data

- `F`: a nonarchimedean local field, in universe `u`, of any characteristic.
- `H`: an affine group scheme over `Spec F`, locally of finite type, with
  `hH : IsConnectedReductive H`.
- In the first section, any cocharacter `χ : 𝔾_m ⟶ H`. In the second section,
  `χ = CommGroupScheme.groupHom ζ ≫ j` for a commutative group scheme `T`, a homomorphism
  `j : T ⟶ H` and `ζ : cocharacterLattice T`. This is the shape that the published
  `plancherelWeight j ζ …` requires.
- `π`: an irreducible admissible complex representation of the literal Levi subgroup
  `levi χ = Z_H(χ)(F)` of `H(F)`. Its carrier universe `uV` is independent of `u`. `π` is square
  integrable modulo a central subgroup `C` (`hsq`), for a Haar measure `mu` on the quotient.
- `hRefl : RelativeRootReflectionExistenceStatement` and
  `hCST : CentralSplitTorusCharacterStatement`. These are the two global Library statements
  that the published weight `plancherelWeight`, and hence `µ^G`, takes as hypotheses. They are
  parameters here as well. They do not depend on the group, so `µ^G` and every `µ^{M'}` use the
  same two.

## Definitions and results

Section `Restrict` (any cocharacter `χ`):

- `leviCharacterRestrict χ` (new definition): the homeomorphic group isomorphism
  `Im X(Z_H(χ)(F)) ≃ₜ* Im X(Z_H(χ))`, `z ↦ z ∘ e`, with `e = parameterHomeomorph χ` the
  identification of the centralizer scheme's points with the literal Levi. It is the inverse of
  the published `unitaryUnramifiedCharactersHomeomorph e (normCharacters χ)`.
  `leviCharacterRestrict_apply` (proved by `rfl`) states that the value at `m` is `z (e m)`.
- `nonempty_twist_pullback_iso` (proved): if `a : B ⊗ ψ ≃ B` and `τ = ψ ∘ e`, then
  `(B ∘ e) ⊗ τ ≅ B ∘ e`. This is the one-pullback version of the published
  `nonempty_twist_pullback_pullback_iso`, with the same proof.
- `leviCharacterRestrict_mem_stabilizer` (proved): if `s` stabilizes the class of `π` in the
  discrete-series orbit, then `s ∘ e` lies in `smoothRepUnramifiedTwistStabilizer` of `π ∘ e`.
  The proof follows the published `standardLeviCharacterRestrict_mem_stabilizer`.
- `orbitWeight χ π C hC mu hsq W hW` (new definition): a function `W` on `Im X(Z_H(χ))` that is
  invariant under unitary self-twists of `π ∘ e` descends to the function `π ⊗ z ↦ W(z ∘ e)` on
  the orbit `O = discreteSeriesOrbit C hC mu (leviNormCharacters χ) (class of π)`. The descent
  uses the published `discreteSeriesOrbitDescend`, following the published `standardOrbitWeight`.
  `orbitWeight_orbitMap` and `continuous_orbitWeight` are proved.

Section `Package` (`χ = ζ ∘ j`):

- `structure DensityPackage j ζ hRefl hCST hH A` (new definition): the explicit hypothesis
  package for the Plancherel density of a smooth representation `A` of `Z_H(χ)(F)`. Its fields
  are exactly the remaining inputs of the published `plancherelWeight j ζ hRefl hCST hH …`:
  - a compact open subgroup `K` of `H(F)` (`hK`);
  - the Iwasawa decompositions `H(F) = P(χ)(F) K` (`hPK`) and `H(F) = P̄(χ)(F) K` (`hOppK`);
  - a `ForwardContinuation` `p` and a `ReverseContinuation` `q` of the standard intertwining
    integrals;
  - nonempty open sets `DForward ⊆ forwardFullDomainRegion` and
    `DReverse ⊆ reverseFullDomainRegion` of unramified characters;
  - a nonempty open set `D` of unramified characters with every induced representation
    irreducible (`hirr`);
  - `hreg`, regularity of `j_P⁻¹` at every unitary unramified character, where
    `j_P = conditionalCanonicalRationalScalar …` is the canonical scalar of the package.
  `DensityPackage.canonicalScalar` is `j_P`.
- `DensityPackage.weight P` (new definition): the published `plancherelWeight j ζ …` with the
  fields of `P`, a function on `Im X(Z_H(χ))`. When `j` is a maximal split torus of `H`, it is
  the source function `z ↦ µ(A ⊗ z)`. For arbitrary `j` it is only the Library expression.
  `DensityPackage.weight_stabilizer_invariant` restates the published
  `plancherelWeight_stabilizer_invariant` for the package.
- `orbitPlancherelWeight j ζ hRefl hCST hH π C hC mu hsq P` (new definition), for
  `P : DensityPackage j ζ hRefl hCST hH π.obj`: the weight `π ⊗ z ↦ P.weight (z ∘ e)` on the
  orbit `O` of `π`, defined as `orbitWeight` of `P.weight`. For `j` maximal split it is the
  source Plancherel weight `π ⊗ z ↦ µ(π ⊗ z)`. `orbitPlancherelWeight_orbitMap`
  states that its value at `π ⊗ z` is `P.weight (z ∘ e)`. `continuous_orbitPlancherelWeight`
  is proved from the published `continuous_plancherelWeight`.

## Comparison with the source and with `µ^G`

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333 (literature id `waldspurger-2003-plancherel`). Page
numbers are printed pages.

V.2, printed p. 292: "Pour `ω ∈ O`, on pose `µ(ω) = j(ω)^{-1} ∏_α γ(M_α|M)^2`, où `α` parcourt
les racines réduites de `A_M` au signe près. On notera parfois plus précisément
`µ^G(ω) = µ(ω)`." The superscript records the ambient group. For a Levi `M'` containing `s·M`,
`µ^{M'}` is the same definition with `M'` as the ambient group and `s·M` as the Levi.

The Library's `plancherelDensity` is the expression `j_P⁻¹ (rankOneGammaProduct j ζ K hK)²`,
with `plancherelDensityConstant = (rankOneGammaProduct j ζ K hK).toReal ^ 2`, and
`plancherelWeight` is its value on unitary characters.

### Scope of the source identification

`rankOneGammaProduct j ζ K hK` (module `RationalPlancherelConstant`) is a product over
`rankOneCocharacterSet j ζ`. Its members are the submodules `rankOneCocharacters j ζ β` of the
cocharacter lattice of `T`, one for each relative root `β` of `j` positive on `ζ`: the
cocharacters killed by `β` and by the roots of `j` vanishing on `ζ`. The Library documents this
as `X_*(A_α)` for `T` a maximal split torus. In that case the roots of `j` are the relative roots
of `H`, the members are the lattices `X_*(A_α)`, one for each `α ∈ Σ_red(P)`, and the product is
Waldspurger's `∏_α γ(M_α|M)`. For a smaller torus the indexing is wrong. Distinct source factors
can have the same kernel in the smaller lattice and merge into one factor. The reviewer of the
first version of this module gave this example: `H = SL₃` over `ℚ₂`, `T = 𝔾_m`,
`j = χ = diag(t, 1, t⁻¹)` and `ζ = id`. The three positive roots restrict to the weights
`1, 1, 2`, no root vanishes on `ζ`, and all three kernels are zero. So the Library product has a
single factor, with centralizer `H`, instead of the three source factors. With the principal
congruence subgroup the reviewer computed `441/64` for the Library constant and `729/64` for the
source constant.

So `P.weight` and `orbitPlancherelWeight` are Waldspurger's `µ` only when `j` is a maximal split
torus of `H`. The module does **not** assume maximality. Nor does it prove that the Library's
roots and rank-one Levi subgroups are the source ones. Both are obligations of the place where
the module is used. The published `µ^G` meets
this condition through its hypothesis `hi : IsMaximalSplitTorus i`.

The intended specialization in Task 7454 is
`H = M' = Standard.leviScheme i ν J'`, `j = Standard.leviTorusHom i ν J'`. Here `J'` is the root
set of the standard Levi `M'`, and `ζ` is the conjugate of the standard cocharacter of `M` by a
representative of `s`. Then `j` is maximal split in `M'` by the published
`Langlands.GroupScheme.Standard.isMaximalSplitTorus_leviTorusHom i ν J' hi`, where
`hi : IsMaximalSplitTorus i` is the ambient maximality hypothesis of `µ^G`. Only in that
specialization is `orbitPlancherelWeight` used as the lower density `µ^{M'}`.

### Comparison with `µ^G`

With `j` maximal split in both cases:

- `µ^G` (`standardLeviPlancherelWeight`) is `standardOrbitWeight` of
  `plancherelWeight i ζ …` for `H = G`, `j = i` and `ζ` a standard cocharacter of `M_I`;
- a lower density `µ^{M'}` is `orbitPlancherelWeight` for `H = M'`,
  `j = Standard.leviTorusHom i ν J'` and the cocharacter of `M' ∩ s·P`. It is `orbitWeight` of
  the same `plancherelWeight`.

Both are therefore normalized in the same way: the same canonical scalar construction `j_P` and
the same constant `∏_α γ(M_α|M)²`, each computed in its own ambient group. The two orbit descents
are the same construction. The only difference is that `standardOrbitWeight` also composes with
the published identification of the standard Levi scheme `M_I` with the centralizer. The
constants `γ(G|M')` and `c(G|M)` of V.1 and V.2.2 do not enter `µ^G` or `µ^{M'}`. They enter the
c-family and the norm identity of Lemma V.2.2, which are stated in later modules of the task.

The package is genuinely separate data. The continuations, domains, irreducibility locus and
regularity witness of `µ^G` concern the induction from `M_I` to `G`. Those of `µ^{M'}` concern
the induction from `s·M` to `M'`, with a compact open subgroup of `M'(F)` and the Iwasawa
decompositions of `M'(F)`. Neither set of data supplies the other.

## Status

- Imported proofs: `plancherelWeight_stabilizer_invariant`, `continuous_plancherelWeight`,
  `nonempty_twistEquiv_of_mem_discreteSeriesStabilizer`, `discreteSeriesOrbitDescend_orbitMap`,
  `continuous_discreteSeriesOrbitDescend`, `SmoothRep.isoClass_eq_iff`.
- Imported constructions: `plancherelWeight`, `conditionalCanonicalRationalScalar`,
  `ForwardContinuation`, `ReverseContinuation`, `discreteSeriesOrbitDescend`,
  `unitaryUnramifiedCharactersHomeomorph`.
- New definitions: `leviCharacterRestrict`, `orbitWeight`, `DensityPackage` (with
  `canonicalScalar`, `weight`), `orbitPlancherelWeight`.
- New proved lemmas: `leviCharacterRestrict_apply`, `nonempty_twist_pullback_iso`,
  `leviCharacterRestrict_mem_stabilizer`, `orbitWeight_orbitMap`, `continuous_orbitWeight`,
  `DensityPackage.weight_stabilizer_invariant`, `orbitPlancherelWeight_orbitMap`,
  `continuous_orbitPlancherelWeight`.
- No targets are stated here.
