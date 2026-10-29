# Algebraic lower bound for the actual relative Hom spaces

Authors: Workers 526, 359, 435, 845 and 833. The telescope is copied
unchanged from the checked private lower-bound model of Worker 526 (shared
draft of task `ebf9d80c-dcd4-45c5-91f8-428ad29b1363`, revision 8). That model
uses the actual-map nonzero argument of Workers 359 and 526 and Hom transport
constructions of Workers 845, 526 and 435. Worker 833 wrote this statement
pair. Imported public results keep their own provenance.

`Langlands.FineRelativeHomLowerBoundStatement.{uF,uV,uW,uZ}` is a closed
proposition definition. This module states it; it contains no proof.

## Quantified data and hypotheses

The proposition quantifies over every prime `p` (as `[Fact p.Prime]`), every
p-adic field `F : PadicField.{uF} p`, and every compatible topological datum
`T : F.TopologicalData`. The installed topology is exactly `T.topology`. It
then quantifies over every natural rank `n` with `0 < n`, every ordered block
shape `B : BlockShape n` and every refinement `S : BlockRefinement B`.

The hypotheses are, in order:

* `ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)`, an actual representation
  of the flattened product Levi, with `Representation.IsIrreducible ω.ρ` and
  `CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ`. The latter is
  admissibility (including smoothness) together with vanishing of the actual
  unipotent coinvariants for every proper standard block refinement.
* An arbitrary fine real vector `v₀ : Fin (B.flatten S).length → ℝ`.
* `π : Rep.{uW} ℂ (B.Levi F.Carrier)`, an actual representation of the coarse
  product Levi, with `Representation.IsIrreducible π.ρ` and
  `IsAdmissible π.ρ`.
* An arbitrary coarse real vector `t : Fin B.length → ℝ`.
* `J : Rep.{uZ} ℂ (GeneralLinear n F.Carrier)` with `Nontrivial J.V`, so the
  carrier of `J` is not the zero space.
* The existence of an actual surjective intertwiner

  ```text
  q : (CuspidalJacquetMultiplicity.induced T B
         (Rep.of (T.leviRealPowerTwist B t π.ρ))).ρ.IntertwiningMap J.ρ .
  ```

  Its source is the actual normalized upper parabolic induction from
  `B.Levi F.Carrier` to `GL_n(F)` of the coarse real-power twist of `π` by
  `∏ i |det(m_i)|_F^(t i)`.

`J` need not be irreducible, and it is not assumed admissible; it is only an
actual quotient of that induction with nonzero carrier. The four universes
of the field and of the fine, coarse and ambient carriers are independent.

## The two Hom spaces and the conclusion

For a coarse real vector `s` write `τ_s := fineTwist T B S ω v₀ s`. This is
the actual representation of `Geometric.refinedLevi F.Carrier B S` on the
carrier of `ω` obtained by twisting `ω` by

```text
∏ k |det(m_k)|_F^(-v₀(k) + s(((B.flattenBlockEquiv S).symm k).1))
```

on the flattened product Levi and pulling back along the inverse of the
constructed `Geometric.flattenedLeviEquiv F.Carrier B S`. At `s = 0` the
exponent is `-v₀(k)`. The two spaces in the conclusion are

* `Hout := τ_t.ρ.IntertwiningMap (T.normalizedComposedOppositeJacquet B S J.ρ)`,
  all intertwiners from `τ_t` into the normalized composed opposite Jacquet
  module of `J` itself;
* `Hin := τ_0.ρ.IntertwiningMap (T.normalizedRefinedOppositeJacquet B S π.ρ)`,
  all intertwiners from `τ_0` into the normalized refined opposite Jacquet
  module of `π`.

Both are complex Hom spaces for the same actual refined subgroup.
`Representation.IntertwiningMap` is Mathlib's space of all complex-linear
maps commuting with the two actions; no continuity is required. The
conclusion is the conjunction

```text
FiniteDimensional ℂ Hout ∧ FiniteDimensional ℂ Hin ∧
  Module.finrank ℂ Hin ≤ Module.finrank ℂ Hout .
```

Since both spaces are asserted finite dimensional, `Module.finrank` is their
actual dimension. Either space may be zero: when `Hin = 0` the inequality is
trivial, and no nonzero element of `Hin` or `Hout` is assumed or asserted.

## Normalization conventions

All constructions are the existing actual ones, used unchanged.

* Every real determinant character uses the residue-normalized absolute
  value of `F`.
* The fine exponent is the negative fine vector plus the positive coarse
  vector restricted to the containing coarse block, as above. `Hout` uses
  the coarse vector `t`; `Hin` uses `0`.
* `CuspidalJacquetMultiplicity.induced T B` is
  `T.normalizedParabolicInduced B`: smooth induction from the upper block
  parabolic by right translation, with covariance by the positive half of
  its modulus.
* `T.normalizedRefinedOppositeJacquet B S π.ρ` is the coinvariant quotient
  of the carrier of `π` by the product of the inner lower radicals, twisted
  by the inverse half of `T.refinedOppositeLeviModulus B S`; equivalently its
  normalizing scalar is the positive half `T.refinedLeviHalfModulus B S`.
* `T.normalizedComposedOppositeJacquet B S J.ρ` is the coinvariant quotient
  of the carrier of `J` by `Parabolic.composedOppositeUnipotent F.Carrier B S`
  (the outer lower block radical with the embedded inner lower radicals),
  with the refined subgroup acting through its embedding in `GL_n(F)`, twisted
  by the inverse half of `T.composedOppositeLeviModulus B S`; equivalently by
  the positive half `T.composedLeviHalfModulus B S`.
* The flattened coordinates are the canonical ones,
  `B.flattenBlockEquiv S` and `Geometric.flattenedLeviEquiv F.Carrier B S`.

## What is not assumed

There is no unitarity, temperedness, chamber or order condition on `v₀` or
`t`, middle representation, fine or middle quotient-support hypothesis,
fine-to-ambient quotient hypothesis, finite-length or semisimplicity
hypothesis, nonzero-Hom hypothesis, finite-dimensionality premise or chosen
equivalence. The statement imports only the definition-bearing modules
`Classification.RelativeJacquetMultiplicityStatement` (for `fineTwist`, which
also brings the induction and real-power twist) and
`Parabolic.OppositeRefinementFunctors` (for the two normalized opposite
Jacquet representations). No proof module is imported.

## Internal provenance and intended route

This is an internal algebraic interface of the coordinated relative Hom
comparison, not a literal theorem from Silberger's 1978 article or any other
source. Its shape is a formalization choice: it records the inequality
`dim Hin ≤ dim Hout` needed by the exact comparison task
`ebf9d80c-dcd4-45c5-91f8-428ad29b1363`.

The intended proof, which a separate task must still supply, is:

1. `Langlands.relativeCosocleAdmissibility`
   (`Classification.RelativeCosocleAdmissibilityProof`) shows that `J` is
   admissible, as an actual quotient of the induction of the admissible real
   twist of `π`.
2. Two applications of the public `Langlands.fineOppositeJacquetHomFinite`
   (`Classification.FineOppositeJacquetHomFinitenessProof`), to `J` at `t`
   and to `π` at `0`, give finite dimensionality of `Hout` and `Hin`.
3. The fine twists are irreducible and admissible by
   `Langlands.fineTwistIrreducibleAdmissible`. The refined clause of
   `Langlands.Parabolic.normalizedSecondAdjointness`
   (`Parabolic.SecondAdjointnessProof`) identifies `Hin` with intertwiners
   from the inner induction of `τ_0` to `π`. Its standard clause for
   `B.flatten S`, the flattened comparison
   `Langlands.Parabolic.flattenedOppositeJacquetComparison`
   (`Parabolic.FlattenedOppositeJacquetComparisonProof`) and change of group
   along `flattenedLeviEquiv` identify `Hout` with intertwiners from the fine
   ambient induction to `J`. The positive-rank premise is the one required
   by these second-adjointness clauses.
4. Between these, the actual map
   `Langlands.RelativeHomComparison.fineAmbientHomMap` attached to `q` is
   injective by an exact proof of the public statement
   `Langlands.RelativeHomComparison.FineAmbientHomMapInjectivityStatement`.
   The composite is an injective linear map `Hin → Hout`, so finite
   dimensionality gives the inequality.

That injectivity proof is not yet public, and this statement module claims
none of these steps. It supplies neither the reverse inequality nor quotient
reflection, analytic continuation or the parent relative comparison.
