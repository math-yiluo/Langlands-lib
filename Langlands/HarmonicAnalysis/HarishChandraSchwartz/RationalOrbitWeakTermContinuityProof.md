# Continuity of the weak constant term on the unitary orbit: proof

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitWeakTermContinuityProof`.

`Langlands.HarishChandraSchwartz.rationalOrbitWeakTermContinuity` proves exactly
`RationalOrbitWeakTermContinuityStatement hG hi hν I J hKc hPK π C hC mu hsq hA` (module
`RationalWeakExpansionIdentityDensity`). [Statement](RationalWeakExpansionIdentityDensity.md)

The theorem has only the data of the statement: a connected reductive `G` over a nonarchimedean
local field `F` with maximal split torus `i` and generic `ν`, finite sets `I`, `J` of simple roots,
a compact open `K` with `G(F) = P_∅(F) K`, the representation `π` of `M_I(F)` square integrable
modulo the normal central subgroup `C` with Haar measure `mu` on `M_I(F)/C`, and a compatible split
component `hA` of `M_J`. It assumes no compact subgroup `K0`, basis or Cartan covering; these are
constructed in the proof. Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Proof

After introducing the Borel structure on `M_I(F)/C`, the section `Φ` and the point `m ∈ M_J(F)`:

1. `exists_constantTermPremises_of_joint` (module `RationalSpecialCompactConstantTermPremises`),
   applied to the proved `jointSpecialCompactBasisExistence` (module
   `Langlands.BruhatTits.SpecialCompact.JointBasisProof`), gives a compact subgroup `K0` of `G(F)`
   with `SimultaneousStandardBasisAt i ν K0` and, for every `J' ⊆ Δ`, the Cartan covering
   `StandardLeviCartanCovering F i ν J' K0`.
2. `SimultaneousStandardBasisAt` gives one compact open normal basis `B` of `K0`
   (`CompactOpenNormalBasis K0 B`) and, for `rootSet J`, a compatible split component
   `q' : A' → S` of `M_J` with `StandardParabolicBasisMember i ν (rootSet J) q' L` for every
   `L ∈ B`.
3. `StandardParabolicBasisMember.of_compatibleComponent` (module
   `Langlands.BruhatTits.SpecialCompact.StandardComponentBasisTransport`) turns each of these into
   `StandardParabolicBasisMember i ν (rootSet J) q L` for the given component `hA`.
   [Transport](../../BruhatTits/SpecialCompact/StandardComponentBasisTransport.md)
4. `standardCocharacter` (module `StandardCocharacterProof`) gives a standard cocharacter `ζ` for
   `rootSet J`.
5. The published `rationalOrbitWeakTermParameterContinuity` (module
   `RationalOrbitWeakTermParameterContinuity`), at `ζ`, with `K0`, its basis property, the Cartan
   covering of `M_I(F)` (step 1 at `rootSet I`), `B` and the basis members of step 3, gives
   continuity of `ω ↦ (f_ω)^w_{P'}(m)` on the orbit `O`.

The inclusions `rootSet I ⊆ Δ` and `rootSet J ⊆ Δ` are `RationalPointFamily.rootSet_subset`.

## Provenance

The statement is the continuity of `χ ↦ (E^G_P sp_χ ψ)^w_{P'}(m')` on `Im X(M)` used in
Waldspurger's proof of Proposition VI.3.1 (printed p. 304); its Markdown gives the source. This
proof is an internal composition of the published results named above and of the transport of
basis members between compatible split components.
