# Commutativity of the actual spherical Hecke algebra of `GL_(r+1)(F)`

This module proves that the published spherical Hecke algebra
`Langlands.Unramified.SphericalHeckeAlgebra F r` is commutative. That algebra is the
compact-open corner of `GL_(r+1)(F)` for the actual spherical subgroup
`GL_(r+1)(O_F)`. It also proves that the published standard spherical Hecke
operators commute. It uses the published canonical topology, valuation, and
local-field structure of a `PadicField`. The module reuses the local instances of
`Langlands.Representation.Unramified.HeckeOperators`, together with its Haar measure
`sphericalHaar F r`, which gives the spherical subgroup mass one.

Provenance: Borel (1979), *Automorphic L-functions*, §7.1 (printed page 39, PDF
page 48), identifies the spherical Hecke algebra with a commutative algebra through
the Satake isomorphism. The Lean proof instead specialises Gelfand's argument
(`Langlands.Representation.Hecke.GelfandTrick`) to the inverse-transpose
automorphism. It uses the published Cartan decomposition
`Langlands.GeneralLinear.Cartan.exists_cartan` (Gross 1998, Proposition 2.6). This
route is an internal derivation.

## Inverse transpose and the spherical subgroup

- `inverseTranspose_torus` shows that inverse transpose sends every diagonal
  torus element `GeneralLinear.Iwasawa.torus ϖ lam` to its inverse. A diagonal
  matrix equals its transpose (`Matrix.diagonal_transpose`), and the published
  `torus_inv_val` gives the inverse.
- `sphericalInverseTranspose F r` is the published continuous automorphism
  `GeneralLinear.inverseTransposeContinuous (r + 1) F.Carrier`.
- `inverseTranspose_mem_sphericalSubgroup` shows that inverse transpose preserves
  `sphericalSubgroup F r`. Membership in `Conductor.integralSubgroup`
  (`Conductor.mem_integralSubgroup`) says that the entries of `g` and of `g⁻¹` are
  integral. By `GeneralLinear.inverseTranspose_entry`, the entries of the inverse
  transpose of `g` are the transposed entries of `g⁻¹`. The entries of its inverse
  are the transposed entries of `g`.
- `preimage_sphericalInverseTranspose` turns this into the set equality
  `θ ⁻¹' GL_(r+1)(O_F) = GL_(r+1)(O_F)`. The inclusion `⊇` is the previous lemma.
  The inclusion `⊆` applies the previous lemma once more, then uses involutivity
  (`GeneralLinear.inverseTranspose_involutive`).

## The double-coset condition

`sphericalInverseTranspose_mem_doubleCoset_inv` proves that for every `x` there
are `k₁ k₂ ∈ GL_(r+1)(O_F)` with `θ x = k₁ * x⁻¹ * k₂`.

Proof. Choose a uniformizer `ϖ` (`GeneralLinear.Iwasawa.exists_isUniformizingElement`).
The Cartan decomposition writes `x = c₁ * t * c₂` with `c₁ c₂` integral and `t` a
diagonal torus element. Inverse transpose is multiplicative and inverts `t`, so
`θ x = θ c₁ * t⁻¹ * θ c₂`. Since `x⁻¹ = c₂⁻¹ * t⁻¹ * c₁⁻¹`, the witnesses
`k₁ = θ c₁ * c₂` and `k₂ = c₁ * θ c₂` satisfy the identity. The `group` tactic
checks it. Both witnesses lie in the spherical subgroup by the previous section.

## Measure preservation and commutativity

- `sphericalHaar_measurePreserving_inverseTranspose` shows that `θ` preserves
  `sphericalHaar F r`. It applies `Hecke.measurePreserving_of_preimage_eq` with:
  - local compactness of the canonical group topology
    (`F.canonicalGeneralLinearLocallyCompactSpace`);
  - regularity of the normalized compact-open Haar measure
    (`RankinSelberg.normalizedCompactOpenHaar_regular`);
  - compactness of the spherical subgroup;
  - the preimage equality above.
- `sphericalHeckeAlgebra_mul_comm F r f g : f * g = g * f` is
  `Hecke.HeckeAlgebra.Corner.mul_comm_of_measurePreserving`, applied to `θ` with
  the two facts just proved.
- `standardHeckeOperator_commute` deduces that the operators
  `standardHeckeOperator F A i` and `standardHeckeOperator F A j` commute on the
  actual spherical fixed space of any `AutomorphicObject` `A`. Both are images of
  corner elements under the algebra homomorphism `Hecke.cornerAction`, so
  `Commute.map` applies.
