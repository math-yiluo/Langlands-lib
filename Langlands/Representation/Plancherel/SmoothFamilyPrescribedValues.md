# Prescribed values and scalar multiplication for smooth equivariant families

In the proof of Theorem VIII.4.2, Waldspurger (2003), printed p.330
(PDF p.96), writes: "Pour tout `ϕ ∈ 𝒜(ω)`, on peut trouver
`ψ ∈ C^∞(𝒪, G)` tel que `ψ_{ω'} = 0` si `ω' ∈ 𝒪_χ − {ω}` et
`E^G_G ψ_ω = ϕ`." Such a section needs a prescribed value at one class
and vanishing at finitely many others. This module provides both
operations on the Library's existing smooth section types, without
introducing a new section type:

- the finite smooth equivariant families
  `finiteSmoothEquivariantFamilies J V τ ρ` of `SmoothTensorFamilies`;
- the coherent smooth orbit sections `productInducedSmoothOrbitSections`
  of the actual normalized product induction (`ProductInducedOrbitSections`).

Vanishing at the other classes of a finite fiber comes from multiplication
by the isolating scalar function of `RationalOrbitFiberIsolation`, once it
is expressed in the packet's torus coordinates. The construction is
internal to this project.

## Families on the torus

The torus is `J → Circle` with `J` finite. `finiteSmoothFamilies J V`
is the span of the families `z ↦ f(z) • v` with `f` smooth.
`finiteSmoothEquivariantFamilies J V τ ρ`, for a group `S`, a homomorphism
`τ : S →* (J → Circle)` and a representation `ρ` of `S` on `V`, consists
of the finite smooth families with `F (z * τ s) = ρ s (F z)`.

- `smul_mem_finiteSmoothFamilies`: multiplying a finite smooth family by a
  smooth scalar function `φ` gives a finite smooth family. The proof is
  induction over the span; on a generator, `φ z • (f z • v)` is
  `(φ * f) z • v`, and `φ * f` is smooth.
- `smul_mem_finiteSmoothEquivariantFamilies`: if moreover
  `φ (z * τ s) = φ z` for all `s` and `z`, the product of an equivariant
  family is equivariant, by linearity of `ρ s`.
- `exists_mem_finiteSmoothEquivariantFamilies_eval_eq`: if `S` is finite
  and `τ` is injective, then for every parameter `z₀` and vector `v` there
  is an equivariant family `F` with `F z₀ = v`. Take the smooth Lagrange
  function `φ` of `exists_isSmoothFiniteTorusFunction_lagrange`, equal to
  `1` at `z₀` and to `0` at the points `z₀ τ(s)⁻¹`, `s ≠ 1` (these
  differ from `z₀` by injectivity). Put
  `F z = ∑ₛ φ(z τ(s)⁻¹) • ρ s v`. Each summand is a generator of
  `finiteSmoothFamilies` (a translate of a smooth function is smooth by
  `isSmoothFiniteTorusFunction_mul_const_iff`). Equivariance follows by
  reindexing the sum along `s ↦ t⁻¹ s` in the commutative torus. At `z₀`
  only the term `s = 1` survives.
- `SmoothEquivariantFamilyPrescribedValueStatement` records this
  prescribed-value property as a proposition over all `J`, `V` and
  finite `S`. `smoothEquivariantFamilyPrescribedValue` proves it.

## Coherent smooth orbit sections

The setting is that of `ProductInducedOrbitSections`. There `π` is an
irreducible admissible representation of a Levi `M`, `e` gives circle
coordinates on its unitary unramified characters, and `h`, `hU`, `K`,
`hP`, `hK`, `hν`, `hr`, `hPK` are the decomposition and Iwasawa data.
The relevant stabilizer is `unitaryClassTwistStabilizer ν (Quotient.mk _ π)`.
It acts through `unitaryStabilizerTorusHom` and the compact representation
`unitaryStabilizerCompactRepresentation`. The published
`productInducedSmoothFamilies` is the preimage of the equivariant families
under the pointwise restriction equivalence
`productInducedFamilyRestriction`.

- `unitaryStabilizerTorusHom_injective`: the stabilizer parameter map is
  injective, being `e` composed with a subgroup inclusion.
- `exists_mem_productInducedSmoothFamilies_eval_eq`: if the stabilizer is
  finite (supplied for example by the published
  `finite_unitaryClassTwistStabilizer` under its hypotheses),
  then every vector `w` of the actual induced fiber at a parameter `z₀` is
  `F z₀` for a smooth family `F`. Apply the previous result to the
  compact-picture image of `w` under `productInducedCompactEquiv`, and pull
  the family back by the inverse restriction equivalence.
- `exists_mem_productInducedSmoothOrbitSections_eval_eq`: under the same
  hypothesis, `w` is the value at the parameter representative
  `unitaryOrbitParameterRepresentative ν π e z₀` of a coherent smooth orbit
  section. It is the image of `F` under the inverse of the published
  `productInducedSmoothOrbitFamilyEquiv`, whose pullback evaluates sections
  at parameter representatives.
- `exists_mem_productInducedSmoothOrbitSections_smul`: for a smooth scalar
  function `φ` on the torus that is invariant under the stabilizer
  translations, and a coherent smooth orbit section `q`, there is a
  coherent smooth orbit section `q'` with
  `q'(rep z) = φ z • q(rep z)` at every parameter representative. The
  restriction equivalence is linear on each fiber, so the restricted family
  of `φ • q` is `φ` times the restricted family of `q`. The previous
  closure results apply.

These results do not identify the product-induced coefficients at
`P = G` with the coefficient tensors of `rationalOrbitWavePacket`. They
also do not identify the torus coordinates `e` of a packet with those of
`rationalSmoothOrbitFunctions`. Both comparisons belong to the separate
group-Levi packet bridge.
