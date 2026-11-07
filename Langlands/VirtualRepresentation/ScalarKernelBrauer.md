# Brauer induction for representations that are scalar on a finite-index kernel

Helper module for the proof of
`Langlands.ClassField.Global.RelativeWeilGroup.InducedCharacterGenerationStatement`.
It proves the scalar case: let `π : S →* Q` be a homomorphism from a topological
group to a finite group with open kernel. Let `B` be a continuous
finite-dimensional complex representation of `S` on which every element of
`ker π` acts by a scalar. Then the exact virtual class of `B` is an integral
combination of classes `Ind_{π⁻¹ H}^S θ`, for subgroups `H` of `Q` and continuous
characters `θ` of `π⁻¹ H`. The finite-group input is the published proved finite
Brauer theorem `Langlands.FiniteRep.BrauerTheory.finiteBrauerTheory`, through
its conjunct `IntegralBrauerSpanningStatement`. Finite Brauer theory is not
reproved here.

## Generators (`Langlands.VirtualRepresentation.ExactGrothendieckGroup`)

- `ofRepresentation_eq_zero_of_rank_eq_zero`: a representation of rank zero has
  virtual class zero. The defining exact relation for `0 → A → A → 0` (identity,
  then zero) gives `[A] = [A] + [A]`.
- `continuousInduce_characterClass_congr`: if `T₁ = T₂`, every induced character
  class from `T₁` is an induced character class from `T₂` (by `subst`).
- `isOpen_comap_of_isOpen_ker`: if `ker π` is open, so is every `π⁻¹ H`.
- `quotientInducedGenerators π hπ` is the set of
  `continuousInduce (H.comap π) _ (characterClass θ)` for `H : Subgroup Q` and
  `θ : H.comap π →ₜ* ℂˣ`, with carriers in the universe `max uG uV`. For the
  projection `W_{E/F} → Gal(E/F)` this is exactly the published
  `inducedCharacterGenerators`.
- `mem_quotientInducedGenerators_of_ker_le`: induction from any open subgroup
  `T ⊇ ker π` of a continuous character is a generator, because
  `T = (π T).comap π` (`Subgroup.comap_map_eq_self`).

## The scalar-lift map (`Langlands.VirtualRepresentation.ScalarKernel`)

Let `ρ` be continuous on a nontrivial finite-dimensional `V`, scalar on an open
subgroup `N`.

- `liftRep σ` is a representation `σ` on `ULift Y`, a copy of its carrier in a
  prescribed universe. `liftRepEquiv` is its equivalence with `σ`.
  `ContinuousExact S` is the continuous exact virtual group of `S` with
  carriers in `max uS uW`.
- `isContinuous_liftRep_scalarLift`: the lifted scalar lift of every
  `U : FDRep ℂ (normalizedImage ρ)` is continuous (`isContinuous_scalarLift` and
  the published `isContinuous_iff_of_equiv`).
- `scalarLiftClass ρ hρ hNo hN` sends the isomorphism class of `U` to the class
  of `liftRep (scalarLift ρ U.ρ)`. It is well defined by `scalarLiftEquiv`.
  `scalarLiftClass_add`: it is additive on direct sums, by
  `scalarLiftProdEquiv` and the published `ofRepresentation_eq_add_of_equiv_prod`.
- `scalarLiftVirtual` is the induced `ℤ`-linear map from the published split
  Grothendieck group `FiniteRep.VirtualRep ℂ (normalizedImage ρ)`. It exists by
  the universal property of the group completion.
  `scalarLiftVirtual_ofClass` computes it on classes.
- `scalarLiftVirtual_tautological`: it sends the class of `tautological ρ` to
  the class of `B` whenever `ρ` is equivalent to `B` (via `modelEquiv` and
  `scalarLiftTautologicalEquiv`).
- `scalarLiftVirtual_induce_mem` (for `N = ker π`): for a subgroup `A` of the
  normalized image and `ψ : A →* ℂˣ`, the image of the class of
  `FiniteRep.induce A (oneDimensional ψ)` lies in the span of the generators.
  The published `induceRepEquiv` and `indCoindEquiv` identify the induced
  representation with Mathlib's coinduction. If `IsTautOn ρ A ψ` holds,
  `coindScalarLiftEquiv` identifies the scalar lift with
  `Ind_T (characterLine θ)`, where `T = scalarPreimage ρ A` contains `ker π` and
  `θ = continuousScalarCharacter ρ hψ hρ hπ hN`. So the image is
  `continuousInduce T _ (characterClass θ)`, a generator. Otherwise the
  tautological part is zero (`tautPart_coind_eq_bot`), and the image is `0`.

## Main theorem

`ofRepresentation_mem_span_of_scalar π hπ B hB hscalar`: the class of `B` lies in
`Submodule.span ℤ (quotientInducedGenerators π hπ)`.

Proof. If `B` is zero-dimensional its class is `0`. Otherwise let
`ρ = B.representation`. The kernel of `π` has finite index, so
`normalizedImage ρ` is finite (`finite_normalizedImage`). The published
`finiteBrauerTheory (normalizedImage ρ)` contains `IntegralBrauerSpanningStatement`:
`brauerExpansion` is surjective. So the class of the tautological
representation is `Σ c_d [Ind_{A_d} ψ_d]` in the split Grothendieck group.
Apply `scalarLiftVirtual`. The left side becomes `[B]`
(`scalarLiftVirtual_tautological`). By `Finsupp.apply_linearCombination` and
`Finsupp.range_linearCombination`, the right side lies in the span of the images
of the `[Ind_{A_d} ψ_d]`. Each image lies in the span of the generators
(`scalarLiftVirtual_induce_mem`).

## Dependencies

The module imports `Langlands.VirtualRepresentation.ScalarKernelInduction`, the
published `Langlands.VirtualRepresentation.FiniteInflation`
(`ofRepresentation_eq_add_of_equiv_prod`),
`Langlands.VirtualRepresentation.ExactInductionTwist` (`continuousInduce`),
`Langlands.Weil.Representation.SubquotientContinuity`
(`isContinuous_iff_of_equiv`) and `Langlands.Representation.Finite.BrauerTheoryProof`
(`finiteBrauerTheory`). It also uses the published `FiniteRep.induceRepEquiv`,
`FiniteRep.indCoindEquiv`, `FiniteRep.modelEquiv`, `FiniteRep.equivOfIso`,
`FiniteRep.prodEquiv`, `FiniteRep.brauerExpansion` and `FiniteRep.completionLift_of`.
