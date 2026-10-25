# Fixed-orbit identity and composition comparison equivalences

This internal construction lifts the actual abelian-scheme identity and binary
base-change comparison isomorphisms to monodromy-fixed right-orbit classes of
full and prime-to-modulus Tate frames. It uses the published frame comparisons
from `AdelicFrameCoherence`, the corresponding unrestricted right-orbit maps from
`AdelicFrameOrbitCoherence`, and naturality of actual rational Tate monodromy
from `RationalMonodromy`. No external theorem is being transcribed.

## Inputs and conventions

For the full construction, fix an abelian scheme `A` over `S`, a rational
algebra action `i : D →ₐ[ℚ] End0 A`, the common scalar comparison `h`, a module
`V` over `D ⊗[ℚ] Global.FiniteAdeles ℚ`, and a group representation `ρ` on `V`.
The right action on a frame is precomposition by `ρ(g)`. An invariant orbit is
a right `U`-orbit class fixed by the actual finite-etale fundamental group; no
fixed representative is required.

The comparison is taken at a field-valued point `s` on the common base of its
two abelian schemes. Its finite-fibre witness `hs`, the named
`TorsionFiniteEtaleStatement` hypothesis `htor`, and invertibility of every
retained positive order on that base remain explicit. Algebraic closedness,
connectedness and local noetherianness are not hypotheses of this conditional
construction.

## Identity and binary composition

`adelicFrameOrbitBaseChangeId` is an equivalence from the fixed frame-orbit set
of the pullback of `A` along the identity of `S` to that of `A`, both evaluated
at `s`. The action on the pullback is
`(rationalBaseChangeEnd (𝟙 S) A).comp i`. Its representative map is precisely
`adelicFrameBaseChangeId`, hence postcomposition by the Tate map of the actual
`baseChangeIdIso A`.

For `b : S' ⟶ S` and `c : S'' ⟶ S'`,
`adelicFrameOrbitBaseChangeComp` goes from the fixed frame-orbit set for direct
pullback along `c ≫ b` to the set for pullback first along `b`, then along `c`.
Both are evaluated at the same point of `S''`. Their rational algebra actions
are the corresponding direct and successive pullbacks of `i`. Its
representative map is `adelicFrameBaseChangeComp`, obtained from the actual
`baseChangeCompIso b c A` in this same direction.

Each definition applies `InvariantOrbit.equiv` with the identity isomorphism
of `FundamentalGroup s hs`. Right equivariance follows by evaluation on the
source module. For left equivariance the proof evaluates the frame at a vector,
uses the published formula for the comparison map, and applies
`rationalMonodromy_map` to the actual comparison homomorphism. Thus the inverse
also preserves fixed classes. This does not use a surjectivity assertion about
a map between fundamental groups or the pointed-base-change monodromy
proposition.

The `_val` and `_symm_val` lemmas identify the underlying forward and inverse
functions with the corresponding unrestricted right-orbit comparison
functions. These identifications are definitional.

## Change of level

For each comparison, `_translate` proves compatibility with the actual
`adelicFrameOrbitTranslate` maps. The hypothesis is
`g⁻¹ * u * g ∈ U'` for every `u ∈ U`; both sides go from level `U` to level
`U'`. The proof uses subtype extensionality and the existing
`RightOrbit.map_translate` theorem for the representative comparison.
`_forget` is the specialization to `g = 1` and an inclusion `U ≤ U'`.

## Prime-to-modulus version and scope

All the definitions and laws above have `primeToAdelic` counterparts for every
`m : ℕ`. They use the actual prime-to-modulus Tate frames, coefficients
`D ⊗[ℚ] Global.PrimeToFiniteAdeles m`, and the same full comparison `h` with the
coupled `hAway : PrimeToRationalProfiniteIntegerAdeleComparison h m` at both
endpoints. Retained positive orders satisfy `Nat.Coprime n m`; units are required
only for those orders. No primality assumption on `m` is imposed.

These are ambient tensor-linear frame-orbit comparisons. They impose no Weil
pairing or polarization condition. This module supplies the fixed-set
comparison equivalences and their level compatibility; it does not yet prove
identity or composition coherence for the separate pointed pullback maps, or
construct an unpointed PEL functor.
