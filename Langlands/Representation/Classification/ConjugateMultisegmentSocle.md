# Complex conjugation of segment and multisegment socles

This helper module supports the proof of `UnitarizableSocleHermitianSymmetry` (Tadić 1986,
§2.1–2.4). It formalizes the part of Tadić's §2.2 that concerns complex conjugation. If `π`
is the Zelevinsky socle of the multisegment `a`, then the complex conjugate `π̄` is the
socle of `ā`, where each segment `[ρ, ν^(m-1) ρ]` is replaced by `[ρ̄, ν^(m-1) ρ̄]`. It also
proves Tadić's §2.3 fact that `ρ̄ ≅ ρ̃` for a unitary cuspidal `ρ`.
The helper is internal to the proof. It is derived from the published conjugate-space,
Hermitian-dual and Zelevinsky-socle definitions and cites no further literature.

The complex conjugate of a representation `ρ` on `V` is the published `ConjSpace.rep ρ`.
This is the same action on `ConjSpace V`, the additive group `V` with the conjugate scalar
action.

## Generic conjugate-space equivalences (`Langlands.ConjSpace`)

- `linearEquivOfConj N` reads a conjugate-linear equivalence `N : V ≃ₗ⋆[ℂ] W` as a
  linear equivalence `V̄ ≃ W`.
- `repEquiv N hN` shows that if `N` intertwines `ρ` with `σ`, then `ρ̄` and `σ` are
  equivalent as representations. The intertwining identity is `hN` itself, applied to the
  underlying vectors.
- `mapEquiv` conjugates an equivalence `ρ ≃ σ` to an equivalence `ρ̄ ≃ σ̄`.
  `conjConjEquiv` identifies the double conjugate of `ρ` with `ρ`.
- `conjTwistEquiv` identifies `(χ ⊗ ρ)‾` with `χ ⊗ ρ̄` for a character `χ` with values
  fixed by complex conjugation. The underlying map is the identity, and the check is
  `map_smulₛₗ` together with `conj (χ g) = χ g`.

## Transport along conjugate-linear equivalences

- `isIrreducible_of_conjEquiv`: let `M : W ≃ₗ⋆[ℂ] W'` intertwine `π` with `π'`. Then `π'`
  is irreducible if `π` is. The proof combines the published `isIrreducible_conjComp_iff`
  (for `π̄`, taking the identity homomorphism) with
  `CentralEigenspaceSplitting.isIrreducible_iff_of_equiv` along `repEquiv M`.
- `Classification.IsIrreducibleSocle.of_conjEquiv`: let `N` be a conjugate-linear
  equivariant equivalence of the ambient representations `ρ ≃ ρ'`, and `M` one of the
  subrepresentations `π ≃ π'`. Then the irreducible socle relation transports from
  `(ρ, π)` to `(ρ', π')`. The new embedding is `N ∘ j ∘ M⁻¹`, which is linear because two
  conjugations cancel. Uniqueness works as follows. Let `j''` be an injective intertwining
  map from an irreducible `π''` into `ρ'`. Then `N⁻¹ ∘ j''` is an injective intertwining
  map from the irreducible conjugate `π̄''` into `ρ`. The original uniqueness clause gives
  its range, and the two range inclusions are checked elementwise.

## Smooth and supercuspidal objects

- `SmoothRep.conj A` is the smooth conjugate `Ā`, with the same smooth vectors.
  `conjEquiv` is the identity conjugate-linear map `A → Ā` and `conjEquiv_action` is its
  equivariance. `isIrreducible_conj` shows that `Ā` is irreducible when `A` is.
- `isAdmissible_conjRep` shows that `ρ̄` is admissible when `ρ` is. Its fixed vectors under
  each compact open subgroup are the image of those of `ρ`, so they are finitely generated.
- `GeneralLinear.isSupercuspidal_conjRep` shows that `ρ̄` is supercuspidal when `ρ` is.
  The defining spanning family of the Jacquet relations of `ρ` (`ρ(u)v - v`) lies in the
  Jacquet relations of `ρ̄`. So every Jacquet module of `ρ̄` is zero, hence subsingleton.
- `SupercuspidalRep.conj` and `conjIso` give the conjugate supercuspidal object and the
  conjugate isomorphism. `SupercuspidalClass.conj` is the induced map on isomorphism
  classes. It is an involution (`conj_conj`, via `conjConjEquiv`). It commutes with every
  twist by a real-valued character (`conj_twist`, via `conjTwistEquiv`).

## Cuspidal data and segments (`Langlands.PadicField.TopologicalData`)

- `conj_determinantPowerCharacter`: the characters `ν^s = |det|^s` are real-valued.
  `supercuspidalClassConj_realPowerTwist` therefore gives `(ν^s a)‾ = ν^s ā` on classes.
- `CuspidalDatum.conj` conjugates the class and keeps the rank. It satisfies
  `(ν^s ρ)‾ = ν^s ρ̄` (`conj_twist`), `conj_conj` and `conj_injective`.
  `isRepresentedBy_conj` shows that `Ā` represents `ρ̄` when `A` represents `ρ`.
- `Segment.conj Δ` replaces the base `ρ` by `ρ̄` and keeps the length. Its members are the
  conjugates of the members of `Δ` (`conj_member`, from `conj_twist`), so its support is
  the image of the support of `Δ` (`conj_support`). It is an injective involution.
  Conjugation preserves linkage and precedence (`IsLinked.conj`, `Precedes.conj`,
  `precedes_conj_iff`), since `CuspidalDatum.conj` is injective and commutes with twists.

## Products and segment socles

- `exists_productConjEquiv`: suppose there are blockwise conjugate-linear equivariant
  equivalences `X i ≃ Y i` for any block shape `B`. Then there is a conjugate-linear
  equivariant equivalence of the normalized products `i(X_1, …, X_r) ≃ i(Y_1, …, Y_r)`,
  with the blocks in the **same** order. The published `tensorConjEquiv` and
  `tensorConjEquiv_external` give the map of tensor products. It intertwines the inducing
  representations because the normalizing character `δ^(1/2)` is real
  (`leviHalfCharacter_toMonoidHom`, `leviHalfModulus_apply`, `Complex.conj_ofReal`).
  The published `Induction.smoothFunctionsConjEquiv` then gives the map on smooth induced
  functions.
- `exists_segmentInducedConj` applies this to `i(A, νA, …, ν^(m-1)A)` and
  `i(Ā, νĀ, …, ν^(m-1)Ā)`, using `conj_determinantPowerCharacter` on each factor.
- `IsSegmentSocle.conj`: let `π` be the socle of the segment `Δ`, represented by `A`. Then
  every `π'` conjugate-linearly equivalent to `π` is the socle of `Δ̄`, represented by `Ā`.
  This is `IsIrreducibleSocle.of_conjEquiv` applied to the two equivalences above.

## Zelevinsky socles

- `SegmentProductDatum.conj` conjugates every segment and every block and keeps the order.
  Its shape is unchanged (`conj_shape`). Its induced representation is the normalized
  product of the conjugate blocks (`conj_induced`). Its multisegment is
  `d.multisegment.map Segment.conj` (`multisegment_conj`, via `List.map_ofFn`).
- `IsPrecedenceOrdered.conj` and `HasSegmentSocles.conj` follow from
  `precedes_conj_iff` and `IsSegmentSocle.conj`.
- `SegmentProductDatum.IsZelevinskySocle.conj` combines these with
  `exists_productConjEquiv` and `IsIrreducibleSocle.of_conjEquiv`.
  `Multisegment.IsZelevinskySocle.conj` passes through the existential datum: if
  `a.IsZelevinskySocle π` and `M : π ≃ₗ⋆[ℂ] π'` is equivariant, then
  `(a.map Segment.conj).IsZelevinskySocle π'`.

## Unitary cuspidal data

`CuspidalDatum.conj_eq_dualDatum`: for a unitary cuspidal datum `ρ`, the conjugate `ρ̄`
equals the published contragredient datum `dualDatum ρ` (Tadić §2.3, `ρ^+ = ρ` for unitary
`ρ`). Take a representative `A` and an invariant positive form `b` on it. Then
`b.smoothDualEquiv` (the map `v ↦ b(v, -)`, bijective by admissibility of the
supercuspidal `A`) is a conjugate-linear equivariant equivalence `A ≃ Ã`. So `repEquiv`
gives `Ā ≅ Ã`, and the published `dualRep_represents` identifies the class of `Ã` with
`dualDatum ρ`.
