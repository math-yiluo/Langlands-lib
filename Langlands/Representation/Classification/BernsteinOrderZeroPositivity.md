# Central exponents of subquotients and order-zero lower positivity

Module `Langlands.Representation.Classification.BernsteinOrderZeroPositivity`,
namespace `Langlands.Classification`.

This module proves the order-zero case of Bernstein's necessary lower
shifted-derivative positivity for irreducible unitarizable representations of
`GL_N(F)`. It also proves three general facts about Bernstein central exponents
(`HasBernsteinCentralExponent`, `Langlands.Representation.Classification.BernsteinDerivativePositivity`)
that the higher-order cases reuse.

## Provenance

Bernstein, *P-invariant distributions on GL(N) and the classification of
unitary representations of GL(N) (non-archimedean case)* (1984)
(`bernstein-1984-p-invariant`), §§7.2–7.3, printed p.82, fixes the twist
`ν^(1/2)` and the central-exponent normalization. §8.2, printed p.88, includes
order zero in the positivity condition. At order zero the shifted derivative is
`ν^(1/2) π`. Its exponent is `N/2`, since an irreducible unitary `π` has
exponent zero. Bernstein uses this without proof. The statements below are
internal Lean versions of these routine facts. No numbered source result is
formalized here.

## Conventions

The usual `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p` and
`T : F.TopologicalData` are fixed, with `T.topology` installed in every
statement. Representations are actual objects of `SmoothRep.{0, uF, uV} ℂ`.
`GeneralLinear.scalar` is the scalar-matrix homomorphism
`F.Carrierˣ →* GL_n(F)`.

## Declarations

- `HasScalarCharacter.of_isSubquotient`: for any topological group `G`, a
  homomorphism `z : C →* G` and a character `ω : C →* ℂˣ`, if `z c` acts on `A`
  by the scalar `ω c` and `D` is an actual smooth subquotient of `A`
  (`SmoothRep.IsSubquotient D A`), then `z c` acts on `D` by `ω c`.
  Proof: the published `HasScalarCharacter.of_injective` handles the inclusion
  `SmoothRep.subtype A S`. `HasScalarCharacter.of_surjective` handles the
  quotient map `SmoothRep.mkQ`. It also handles the inverse `e.inv` of the
  supplied isomorphism `e`, which is surjective because
  `e.hom ≫ e.inv = 𝟙`.

- `eq_of_normalizedAbs_uniformizer_rpow_eq`: if
  `|ϖ|^e = |ϖ|^s` for the chosen uniformizer `ϖ = T.uniformizer`, then
  `e = s`. Proof: take real logarithms (`Real.log_rpow`). The published
  `UnitaryWeylRigidity.normalizedAbs_uniformizer_pos_ne_one` says
  `0 < |ϖ| ≠ 1`, so `log |ϖ| ≠ 0` and can be cancelled.

- `HasBernsteinCentralExponent.eq_of_hasScalarCharacter`: let `D` be a
  representation of `GL_n(F)` with nontrivial carrier, let
  `HasBernsteinCentralExponent T D e` hold, and let `ω` be a scalar character
  of `D` with `‖ω a‖ = |a|^s` for every `a`. Then `e = s`. Proof: the
  existential gives `ω'`, also a scalar character of `D`. Applying both to a
  nonzero vector `v` gives `ω' ϖ • v = ω ϖ • v`, so `ω' ϖ = ω ϖ`. The norm
  equations then read `|ϖ|^e = |ϖ|^s`. Conclude with the previous lemma.

- `exists_hasScalarCharacter_norm_one_of_isUnitarizable`: an irreducible
  unitarizable smooth `π` on `GL_N(F)` has a scalar character `ω` with
  `‖ω a‖ = 1` for every `a`. Proof: the published cuspidal embedding theorem
  `CuspidalSupport.cuspidalEmbedding F T N` gives admissibility of `π`.
  `admissibleSchur_centralCharacter` then gives a character `χ` of the center,
  and `ω = χ ∘ GeneralLinear.scalarToCenter`. Irreducibility makes the carrier
  nontrivial (`IsSimpleModule.nontrivial`). The published
  `UnitaryWeylRigidity.norm_eq_one_of_isUnitarizable` applies the invariant
  positive form to a nonzero vector, giving `‖ω a‖ = 1`.

- `bernsteinShiftedDerivative_zero_positive` (the order-zero case): for
  `0 < N`, a unitary additive character `ψ`, and an irreducible unitarizable
  smooth `π` on `GL_N(F)`,

  ```lean
  BernsteinPositiveCentralExponents T (bernsteinShiftedDerivative T ψ π 0 hk)
  ```

  holds for every proof `hk : 0 ≤ N`. Proof: the zeroth derivative
  `generalLinearDerivative T ψ N 0 hk` is the identity functor by definition,
  so the shifted derivative is `T.segmentFactor π (1/2)`. Take an irreducible
  subquotient `D` of it with central exponent `e`. With `ω` from the previous
  lemma, the published `T.hasScalarCharacter_segmentFactor` shows that
  `ω · (|det|^(1/2) ∘ scalar)` is a scalar character of `ν^(1/2) π`.
  `HasScalarCharacter.of_isSubquotient` passes it to `D`, and `D` is
  nontrivial because it is irreducible. The published
  `T.norm_determinantPowerCharacter_scalar` gives the norm of this character
  at `a`: it is `1 · |a|^(N · (1/2))`. So
  `HasBernsteinCentralExponent.eq_of_hasScalarCharacter` gives
  `e = N · (1/2)`, which is positive because `N > 0`.

## Scope

No highest-derivative property of the order is used or asserted, and no
higher-order derivative appears. The lemmas assume no admissibility or
finite-length hypothesis; admissibility of `π` is derived inside the proof.
