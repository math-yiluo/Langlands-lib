# Realizing actual characters on the exact finite-length K₀

Authors: Worker 34 (Lean proof and first draft) and Worker 969 (Markdown
revision and submission).

The theorem `Langlands.Character.exactK0CharacterRealization` proves the
published proposition
`Langlands.Character.ExactK0CharacterRealizationStatement.{uG,uV}` of
`Langlands.Representation.Character.ExactK0Targets`. Its type is exactly that
proposition, with the group universe `uG` and the carrier universe `uV`
independent. It adds no hypotheses.

## What is proved

For every group `G` and measure `μ` as in the target, assume the target's
premise

```
hAdm : ∀ (A : SmoothRep.{0,uG,uV} ℂ G), A.HasFiniteLength → A.IsAdmissible.
```

Then there is exactly one integer-linear map
`χ : SmoothRep.FiniteLengthGrothendieckGroup.{0,uG,uV} ℂ G →ₗ[ℤ]
HarmonicAnalysis.Distribution G` with

```
χ (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
  distribution μ A.representation (hAdm A hA)
```

for every actual smooth representation `A` in `Type uV` and every
`hA : A.HasFiniteLength`. The domain is the published exact quotient: the free
integral module on genuine finite-length isomorphism classes modulo the
integral span of `[B] - [A] - [C]` over all actual short exact sequences,
including nonsplit ones. The premise `hAdm` is kept as an explicit premise; the
theorem does not prove it for any reductive group.

## The implemented proof

1. **Character values on isomorphism classes.** The function
   `a : SmoothRep.FiniteLengthIsoClass ℂ G → HarmonicAnalysis.Distribution G`
   is defined by `Quotient.lift` of
   `A ↦ distribution μ A.val.representation (hAdm A.val A.property)`. To show
   it is well defined, an actual categorical isomorphism `e : A.val ≅ B.val`
   gives the equivariant linear equivalence `E := SmoothRep.equivOfIso e`.
   `Character.distribution_eq_of_equivariant`, applied to
   `E.toLinearEquiv` and `E.toIntertwiningMap.isIntertwining`, shows that the
   two representatives have equal characters.
2. **Exact additivity.** `a` satisfies
   `SmoothRep.FiniteLengthGrothendieckGroup.IsExactAdditive ℂ G a`. For
   finite-length objects `A`, `B`, `C` and a short exact sequence `f`, `g`
   between them, this is `distributionShortExactAdditivity`
   (the published `DistributionShortExactAdditivityStatement` at universes
   `uG, uV, uV, uV`), applied with the admissibility proofs supplied by
   `hAdm`. The values of `a` on the three classes reduce to these characters by
   the computation rule of `Quotient.lift`.
3. **Existence.** The witness is
   `SmoothRep.FiniteLengthGrothendieckGroup.lift ℂ G a ha`. This map descends
   through the span of all actual short exact relations. Its generator values
   are given by `lift_ofRepresentation`.
4. **Uniqueness.** For any `χ` with the generator formula,
   `FiniteLengthGrothendieckGroup.hom_ext_object` reduces equality with the
   lift to equality on every finite-length object `A`. There the formula for
   `χ` at `A.val`, `A.property` and `lift_ofObject` give the same value.

## Dependencies

Declaration-level dependencies: `Character.distribution`,
`Character.distribution_eq_of_equivariant`, `SmoothRep.equivOfIso`,
`Character.distributionShortExactAdditivity` (from
`Langlands.Representation.Character.ExactAdditivityProof`), and from
`Langlands.Representation.Smooth.FiniteLengthGrothendieck` the definitions
`FiniteLengthIsoClass`, `IsExactAdditive`, `ofRepresentation` and `lift`, with
`lift_ofRepresentation`, `lift_ofObject` and `hom_ext_object`. The module
imports only `Langlands.Representation.Character.ExactAdditivityProof`.

The proof does not use `existsUnique_lift_iff`, the irreducible realization
theorem, finite-family character independence, classification, a geometric
lemma, adjointness or a cuspidal-support result. The target's `μ.Regular`
instance is introduced but not used.

## Provenance

This is a derived application of the published exact quotient's universal
property. The target's paired Markdown records the original character
convention of Bernstein–Zelevinsky (1976), Section 2.17, separately from the
derived exact-K₀ interface.
