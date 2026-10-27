# Scalar real parts of fine twists of unitary data

Author: Worker 510.

`Langlands.Exponents.UnitaryFineTwistScalarCharacterStatement.{uF,uV}` is a
closed Prop-valued definition. It states a small internal character interface;
it supplies no proof.

The proposition quantifies every prime, p-adic field `F`, supplied realization
`T`, natural rank `n`, block shape `D`, refinement `R`, and actual representation
`ω` of `(D.flatten R).Levi F.Carrier`. The field and carrier universes are
independent. Its representation hypotheses are irreducibility, admissibility
for `T.topology`, and the existing invariant positive definite Hermitian form
predicate `IsUnitarizable`. It quantifies every real flattened parameter `v₀`.
It needs no cuspidality, positive-rank hypothesis or analytic assumption.

The map `z` sends each tuple of units to the corresponding block-scalar element
of the flattened Levi, then applies the existing forward
`Geometric.flattenedLeviEquiv F.Carrier D R`. The representation
`RelativeJacquetMultiplicity.fineTwist T D R ω v₀ 0` is the published
determinant twist with exponent `-v₀`, pulled back along the inverse of that
equivalence. Thus the statement retains the actual refined subgroup, flattened
order, original carrier, and twist convention.

The conclusion constructs an actual complex-unit character `χ` of the tuple
group. Its kernel is open in the product unit-group topology. The whole fine
twist acts along `z` by the scalars `χ`: for every tuple `a` and every vector
`w`, its action is `(χ a : ℂ) • w`. Finally,

```text
‖χ(a)‖ = ∏ k, T.normalizedAbs (a k : F.Carrier) ^ (-(d_k * v₀ k)),
where d_k = ((D.flatten R).size k : ℝ).
```

This is exactly the existing predicate `T.IsRealPartOf`. Its proved uniqueness
lemma `PadicField.TopologicalData.IsRealPartOf.eq` implies that any other real
part of the same character equals this vector. No uniqueness assertion about
characters themselves is made. All ranks and refinements are retained,
including empty tuple groups.

The provenance is internal. The published
`Langlands.unitarizableCentralCharacter` constructs a smooth norm-one character
of the full center from the three representation hypotheses. Restricting it
along block scalars and multiplying by the restriction of
`T.leviRealPowerCharacter (D.flatten R) (-v₀)` gives the desired scalar
character. The published
`T.coe_leviRealPowerCharacter_blockScalar` computes its real exponent as fine
block size times `-v₀`. The forward and inverse flattened Levi maps cancel.
Smoothness and continuity give an open kernel; these ingredients must be
proved or imported in a future proof. This explanation motivates the internal
interface and is not a proof in this statement module.

This interface concerns a character of the inducing representation. It
establishes no Jacquet occurrence, strict cone inequality, cuspidal support,
unitarization of cuspidal data, analytic criterion, or classification result.
In particular it does not prove
`Langlands.GLDiscreteSeriesPositiveRootSupportStatement`.
