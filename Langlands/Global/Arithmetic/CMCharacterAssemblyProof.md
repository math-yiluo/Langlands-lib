# Proof of the CM regular unit-prescription assembly

Worker 84 and Worker 1242. The theorem
`Langlands.Global.cmRegularUnitPrescriptionOfInputs` proves the Library
proposition `Langlands.Global.CMRegularUnitPrescriptionOfInputsStatement.{u,v}`
from `Langlands.Global.Arithmetic.CMCharacterAssemblyStatement`, with the
universes `u` (the CM field) and `v` (the imaginary-quadratic field) kept
independent.

The proof assumes exactly the three existence statements named in that target:
`CMUnramifiedInfinityRealizationStatement.{u}`,
`CMFiniteCharacterPrescriptionStatement.{u}` and
`IntegralUnitCharacterExtensionStatement.{u}`. It does not prove any of them.

## Implemented argument

Fix the data of `CMRegularUnitPrescriptionStatement.{u,v}`: a CM field `K`, an
imaginary-quadratic field `E` with embeddings `ι : E →+* K` and `τ : E →+* ℂ`,
an anticyclotomic infinity type `a` with distinct weights above `ι` and `τ`, a
finite set `S` of finite places disjoint from its image under the actual
complex conjugation, and continuous characters `η w` of the actual integral
units at each `w ∈ S`.

1. **Extension.** For each `w ∈ S`, the third premise applied to `η w` gives a
   continuous character `ξ w` of the local multiplicative group with
   `ξ w ^ n = 1` for some `n > 0`, whose value at the image of each integral
   unit `b` under the inclusion of the integral ring is `η w b`. The family
   `ξ` is obtained with `choose`.
2. **Finite prescription.** The second premise, applied to `K`, `S`, the
   disjointness hypothesis and the finite-order family `ξ`, gives a Hecke
   character `ψ` that is conjugate self-dual, has trivial infinity component
   and has finite component `ξ w` at every `w ∈ S`. (Its finite order is not
   used further.)
3. **Infinity realization.** The first premise, applied to `K` and `a`, gives
   a positive natural number `m` and a Hecke character `μ` that is conjugate
   self-dual, has infinity component `InfinityType.toCharacter (m * a)`, and is
   unramified at every finite place.
4. **Product.** The proof returns `m` and `μ * ψ`, the product on the actual
   idele-class group, and checks the four conclusions:
   - *Conjugate self-duality.* Pointwise, `(μ * ψ)` at the conjugate of `x` is
     `(μ x)⁻¹ * (ψ x)⁻¹`, which equals `(μ x * ψ x)⁻¹` in the commutative
     group `ℂˣ`.
   - *Infinity component.* The infinity component of the product is,
     definitionally, the product of the infinity components; rewriting with
     those of `μ` and `ψ` gives `toCharacter (m * a) * 1`, and `mul_one`
     closes it.
   - *Regularity.* Since `m > 0`, the integer `(m : ℤ)` is nonzero, so
     `m * a σ = m * a ρ` implies `a σ = a ρ` by cancellation; the given
     injectivity of `a` on embeddings above `ι` and `τ` then gives `σ = ρ`.
     Hence the scaled weights `m * a` are still distinct above `ι` and `τ`.
   - *Local units.* For `w ∈ S` and an integral unit `b`, the image of `b` in
     the local multiplicative group lies in the units of the integral
     submonoid, because `b` and `b⁻¹` both lie in the integral ring. This is
     the subgroup used by `HeckeCharacter.IsUnramifiedAt`, so the finite
     component of `μ` is `1` there. By `HeckeCharacter.finiteComponent_mul`
     the finite component of the product is the product of the components,
     that of `ψ` is `ξ w` by step 2, and `ξ w` at the image of `b` is
     `η w b` by step 1. The value is therefore exactly `η w b`.

The implementation uses only the existing completion inclusion, the existing
`HeckeCharacter.finiteComponent`, `HeckeCharacter.atInfinity` and the group
structure on Hecke characters; it constructs no alternate idele or character
interface. The separated finite place set and the single common multiplier
`m` are those of the target. The kernel axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

This is the assembly at the end of the proof of Henniart 2000, Section 3.6,
Lemma 3, printed p.451, registered source `henniart-2000-simple-proof`,
SHA-256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
There, the prescribed unit character is extended to a finite-order local
character, and the global character is `X = YZ`, with `Y` from Lemma 1
(p.450: conjugate self-dual, of the scaled infinity type and unramified at
every finite place) and `Z` from Lemma 2 (pp.450–451: finite order,
conjugate self-dual, with the prescribed local components). Steps 1–4 follow
that route, with `μ` in the role of `Y` and `ψ` in that of `Z`. The separated
finite set
and the embedding-independent weights are the generalizations documented in
the target statement pair. The proof draft was written by Worker 84; Worker
1242 checked it against the current Library and wrote this description.
