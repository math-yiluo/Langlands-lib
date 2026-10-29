# Dual exponents of quotients of a maximal central-defect layer

Module `Langlands.Representation.Exponents.WeakCriticalTopLayerExponents`.
Internal helper module, author Worker 728. Mathematically it is the
"arguing as in Corollary 2.4.2" step of Silberger 1979, proof of Corollary
4.5.11 (printed pp.189–190). There the top layer of the character quotient is
compared with the exponents of the source along finer parabolics.

## A linear-algebra lemma

- `Subrepresentation.defect_pow_mem`: a subrepresentation of an abelian group
  action is stable under `(ρ a - z • 1) ^ k`.
- `exists_generalized_preimage`: let `ρ` be a representation of a commutative
  group `H` on a vector space `V` over a field `K`. Assume `V` is spanned by
  the generalized character spaces of the characters satisfying a predicate
  `P`. Let `Λ` be a vector of the generalized `ψ`-space and suppose
  `(ρ a - z • 1) ^ k L = Λ` for some `L`. Then the same holds for some `L'` in
  the generalized `ψ`-space. Proof: write `L = y + w` with `y` in the
  `ψ`-space and `w` in the sum of the other spaces. The defect power preserves
  each space, and its image of `w` lies in the `ψ`-space and in the sum of the
  others. These two spaces meet only in `0` by
  `ScalarSubquotientDualSpectrum.independent_weights` and
  `generalized_le_weight`. So the image of `y` is `Λ`.

## The main theorem

`PadicField.TopologicalData.topLayer_flattened_dual`. The data are:

- `0 < n`, `B : BlockShape n`;
- an irreducible admissible `A` of `GL_n`;
- a character `χ` of the block scalars of `B`, a block scalar `a` and `k : ℕ`;
- `S : Rep ℂ (B.Levi F)` with `HasScalarCharacter S.ρ (B.blockScalarLevi F) χ`;
- a surjective full-Levi intertwiner
  `q : T.dualJacquetCharacterDefectRangeRepresentation B A χ a k → S`;
- a refinement `D` of `B`, a character `ψ` of the flattened block scalars, and
  a nonzero `φ` on `RefinedOppositeJacquetModule B D S.ρ` with the `ψ`-eigen
  equation of the consumer form of the product-Levi criterion.

There are three conclusions.

1. `ψ (c ∘ B.flattenOuter D) = χ c` for every block scalar `c` of `B`. The
   eigen equation at `c ∘ flattenOuter` uses three Library facts from
   `Classification/MaximalConeLifting`: the refined half modulus is trivial
   there (`refinedLeviHalfModulus_blockScalarLevi_comp`), the flattened Levi
   element is the outer block scalar (`flattenedLeviEquiv_blockScalarLevi_comp`),
   and `S` has scalar character `χ`.
2. The `ψ`-eigenspace of `T.splitCentreDualJacquet (B.flatten D) A` is nonzero.
3. Some vector `L` of the generalized `ψ`-space of
   `T.splitCentreDualJacquet (B.flatten D) A` satisfies
   `((ρ (a ∘ flattenOuter) - χ a • 1) ^ k) L ≠ 0`.

Proof as implemented. Let `O` be the opposite Jacquet module of `A` along `B`,
`X` its dual-detected character quotient with map `πχ`, `W` the defect range,
`m : O → W` the canonical surjection, and `incl : W → X` the inclusion. `J_D`
denotes `T.normalizedRefinedOppositeJacquetMap B D`.

- `O` is admissible (`Parabolic.isAdmissible_standardOppositeJacquet`), so `X`
  is smooth (`isSmooth_of_surjective`). Then `J_D incl` is injective
  (`normalizedRefinedOppositeJacquetMap_injective`). A linear left inverse
  (`LinearMap.exists_leftInverse_of_injective`) extends `φ ∘ J_D q` from `J_D W`
  to a functional `lamX` on `J_D X`.
- Transitivity and the flattened comparison
  (`Parabolic.normalizedOppositeRefinementTransitivity`,
  `Parabolic.flattenedOppositeJacquetComparison`) give a linear equivalence `E`
  from `J_D O` to the opposite Jacquet module of `A` along `B.flatten D`. It
  sends the class of `v` to its class, and it intertwines the flattened block
  scalars, as in `glOppositeJacquetSubquotientExponentInheritance`.
- Put `Λf = φ ∘ J_D q ∘ J_D m ∘ E⁻¹` and `L = lamX ∘ J_D πχ ∘ E⁻¹`. The eigen
  equation of `φ` and the intertwining properties make `Λf` a `ψ`-eigenvector.
  It is nonzero because `q`, `m` and the quotient maps are surjective.
- On the class of `v` along the flattened shape, the defect power applied to
  `L` is computed with `splitCentreOppositeJacquet_defect_pow_mk` (flattened
  shape, then `B`). The embedded block scalars and half moduli of
  `a ∘ flattenOuter` and `a` agree (`leviEmbedding_blockScalarLevi_coarsen`,
  `leviModulus_blockScalarLevi_coarsen`). With
  `dualJacquetCharacterDefect_pow_quotientMap`, the result is
  `lamX (J_D incl (class of m v)) = φ (J_D q (class of m v)) = Λf (class of v)`.
  So `(ρ (a ∘ flattenOuter) - χ a • 1) ^ k L = Λf`.
- The generalized spaces span the full dual (`glDualJacquetFiniteness`, third
  component), so `exists_generalized_preimage` replaces `L` by a generalized
  `ψ`-vector with the same image `Λf ≠ 0`.
