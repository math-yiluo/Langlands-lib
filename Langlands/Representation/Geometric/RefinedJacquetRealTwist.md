# Upper refined Jacquet quotients and real determinant twists

Author: Worker 526. Workers 359 and 430 supplied the source-twist and
normalization guidance in the relative Hom-comparison investigation.

This internal definition/API module constructs
`Langlands.PadicField.TopologicalData.normalizedRefinedJacquetRealTwistEquiv`.
For an actual finite p-adic extension `F`, compatible data `T`, an ordered
block shape `B`, a refinement `S`, an arbitrary complex representation `rho`
of the actual product Levi, and an arbitrary real vector `t`, its type is

```text
(T.normalizedRefinedJacquet B S (T.leviRealPowerTwist B t rho)).Equiv
  (twist ((T.leviRealPowerCharacter B t).comp
      (refinedLevi F.Carrier B S).subtype)
    (T.normalizedRefinedJacquet B S rho))
```

The field universe `uF` and carrier universe `uV` are independent. There is
no topology, positive total rank, smoothness, admissibility, irreducibility,
temperedness, finite dimension, support, scalar-action or sign premise.
Rank zero is included. All representations and both quotient carriers are
the actual Library constructions. The residue-normalized determinant
character has positive exponent `t` on each coarse block.

## The quotient equivalence

The construction applies the published
`Jacquet.normalizedActionOfModulusTwistEquiv` with the actual upper refined
radical, actual refined Levi and the same actual inner modulus
`T.refinedLeviModulus B S` on both sides. Its required kernel inclusion is
the composite of the public `refinedUnipotent_le_normOneLevi` and
`normOneLevi_le_ker_leviRealPowerCharacter`: every component of the refined
radical has determinant norm one, so the coarse real character is one there.
The published generic equivalence is therefore applicable without changing
any quotient or supplying a comparison as a premise. The inverse-half
normalization is the same on both sides and introduces no extra character.

The forward and inverse representative lemmas
`normalizedRefinedJacquetRealTwistEquiv_mk` and
`normalizedRefinedJacquetRealTwistEquiv_symm_mk` hold by reflexivity: the
class of `v` maps to the class of the same `v` in the other actual quotient.

## Uniform generalized-character transport

The supporting algebra works with an arbitrary group `A : Type uA` and a
complex representation on a carrier in `uV`; these universes are independent.
The group assumption follows the public `twist` interface. For unit-valued
characters `eta`, `psi` and each supplied finite power `k`,
`Langlands.characterSpace_twist_mul` proves

```text
characterSpace (twist eta rho) (psi * eta) k = characterSpace rho psi k.
```

For each `a`, the twisted difference operator is
`eta(a) * (rho(a) - psi(a) * identity)`, where the product by `eta(a)` is
scalar multiplication of the endomorphism. Taking kth powers multiplies
by the nonzero scalar `eta(a)^k`, which has the same zero kernel. This
proves equality at each fixed uniform power, including `k = 0`.

`Langlands.isGeneralizedEigencharacter_twist_iff` removes the twist by
multiplying the generalized character by `eta` inverse. It rewrites the
character as `(chi * eta inverse) * eta` and uses the fixed-power equality.
Nilpotent directions and the uniform quantifier over all group elements
are retained; no semisimplicity or projectivity is used.

Finally,
`T.normalizedRefinedJacquetRealTwist_isGeneralizedEigencharacter_iff`
restricts the constructed actual quotient equivalence along an arbitrary
homomorphism `iota : A -> refinedLevi F.Carrier B S`. It then applies the
generic inverse-character law. Thus a generalized character `chi` of the
actual twisted source quotient restricted along `iota` corresponds to
`chi * (((T.leviRealPowerCharacter B t).comp (subtype.comp iota))⁻¹)`
on the untwisted quotient. The inverse applies only to the restricted
twisting character. No centrality assumption on `iota` is needed.

## Provenance and scope

The provenance is internal specialization of the public actual quotient
construction in `Jacquet.NormalizedCharacterTwistEquiv`, the kernel laws in
`Parabolic.RefinementCharacter` and `Twist.LeviRealPower`, and elementary
complex scalar algebra. No new external literature result is asserted.
The public covariance and modulus definitions keep their own provenance.

This unit supplies no full-character extraction, real-coordinate projection,
tempered cone, geometric filtration, Weyl-branch exclusion, whole-induction
isolation or Hom comparison. It is the actual source untwisting API needed
before those separate steps can be applied.
