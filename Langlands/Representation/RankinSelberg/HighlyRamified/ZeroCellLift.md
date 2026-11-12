# Zero-cell Kirillov lifts are fixed by the integral mirabolic group

Module `Langlands.Representation.RankinSelberg.HighlyRamified.ZeroCellLift`.

This module supports the proof of
`Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement`. It is a step toward the
essential-vector input `EssentialPairInput` (module `HighlyRamified.EssentialInput`) for
p-adic fields. It does not use the essential-vector level statement.

## Provenance

The invariance under the integral mirabolic group is the first step of the proof of
Jacquet, Piatetski-Shapiro and Shalika 1981, *Conducteur des représentations du groupe
linéaire*, Theorem (5.1)(ii), printed p. 211: the essential vector is fixed by the
integral matrices whose last row is `(0, …, 0, 1)`. The route here is internal to this
project. It uses the Library's Kirillov injectivity theorem
`UnramifiedUnitary.kirillov_injective`, multiplicity one `Whittaker.multiplicityOne`, and
the lifting of mirabolic test functions `Whittaker.modelKirillovTransfer`.

## Results

- `mem_fixedVectors_fieldJacquetMirabolic_of_zeroCell`: let `π` act on `GL_(n+2)(F)` and
  let `ℓ` be a `ψ`-Whittaker functional. Assume that `v ↦ (p ↦ ℓ(π(p) v))`, restricted to
  the mirabolic subgroup `P`, is injective. Let `w` be a model vector that agrees on `P`
  with the zero-cell function `W₀` (`zeroCellWhittaker`). Then `w` is fixed by
  `H(0) = GL_(n+2)(O) ∩ P` (`Conductor.fieldJacquetMirabolic`).
- `zeroCell_mul_fieldJacquetMirabolic`: the same, pointwise: `w(g k) = w(g)` for
  `k ∈ H(0)`.
- `isMirabolicRestrictionInjective_of_isGeneric`: over a p-adic field, a generic `π` of
  `GL_(n+2)(F)` and a nonzero `ℓ` have injective mirabolic restriction.
- `exists_zeroCellLift`: over a p-adic field with `ψ` trivial on `O`, every nonzero
  Whittaker functional of a generic `π` has a model vector agreeing with `W₀` on `P`.

## Proofs

`mem_fixedVectors_fieldJacquetMirabolic_of_zeroCell`. By
`Conductor.mem_fixedVectors_of_levi_restriction`, it suffices to check
`w(diag(g, 1) h) = w(diag(g, 1))` for `h ∈ H(0)`. Both `diag(g, 1) h` and `diag(g, 1)` lie
in `P`, so both sides are values of `W₀`. They agree because `W₀` is right
`GL_(n+2)(O)`-invariant (`zeroCellWhittaker_mul_integral`).

`isMirabolicRestrictionInjective_of_isGeneric`. Multiplicity one makes every functional a
multiple of `ℓ`. The Kirillov injectivity theorem then says that a vector `v - v'` whose
coefficients vanish on `P` is zero.

`exists_zeroCellLift`. The zero-cell function is a mirabolic test function
(`isMirabolicTestFunction_zeroCellWhittaker`), and a generic `π` is of Whittaker type, so
`modelKirillovTransfer` lifts it into the model of `ℓ`.
