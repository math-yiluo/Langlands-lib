# Degenerate Jacquet modules and vanishing pieces of the geometric lemma

Module `Langlands.Representation.Geometric.DegenerateJacquetPieces`. Two independent
facts used in the proof of Renard VI.5.3 (`MaximalLeviSupercuspidalInductionEndomorphismStatement`),
where the graded pieces of the geometric lemma (Renard VI.5.1,
`GeometricLemmaIntersectionDatum.pieceFunctor`) are analysed for a single represented
parabolic `P = MU` and `Q = P`.

## Provenance

Internal. Nothing here formalizes a numbered statement of a source. The first part is the
trivial case of normalized Jacquet restriction (Renard VI.1) along a parabolic equal to its
own Levi; the second is the observation, implicit in Renard VI.5.3, that a graded piece
`i^L_{Q'} ∘ ι ∘ r^M_{P'}` vanishes on a representation `ρ` whenever `r^M_{P'} ρ` vanishes
(for supercuspidal `ρ` and a proper `P'`).

## Haar modulus on the trivial subgroup

- `Langlands.HaarModulus.normalizerCharacter_eq_one_of_eq_bot`: if `U = ⊥`, the modulus
  `normalizerCharacter U g` of conjugation by any `g` in the normalizer is `1`. Proof: `U`
  is finite, so the whole of `U` is a compact open subgroup preserved by conjugation, and
  `normalizerCharacter_eq_one_of_preimage` applies with the top open subgroup.
- `Langlands.HaarModulus.closedInverseHalfCharacter_eq_one_of_eq_bot`: for a closed `U = ⊥`
  and a subgroup `M` normalizing it, the inverse half modulus
  `closedInverseHalfCharacter U hU M hMU m` is `1`. Proof: unfold through
  `Jacquet.inverseHalfCharacter_eq_one` to the previous lemma.

## Jacquet restriction along a full Levi

All in namespace `Langlands.Aubert.General.RepresentedParabolic`, for a represented
parabolic `p : P ⟶ G` with Levi `l : M ⟶ P`, radical `r : U ⟶ P` and multiplication
isomorphism `hmul`, under the hypothesis `[IsIso l]` (the Levi is all of `P`). No
hypothesis on `p` is needed.

- `pointImage_radical_eq_bot_of_isIso_levi`: the image `pointImage (r ≫ p)` of the radical's
  rational points in `G(F)` is trivial. Proof: for a rational point `u` of `U`, the point
  `r(u)` of `P` equals `l(m)` with `m = l⁻¹(r(u))`, so `l(m) · r(1) = l(1) · r(u)`; uniqueness
  of the factorization through `hmul` (`eq_and_eq_of_pointMultiplication`) gives `u = 1`.
- `jacquetRelations_eq_bot_of_isIso_levi`: for a smooth representation `π` of `G(F)`, the
  submodule `Jacquet.Localization.relations π.representation (pointImage (r ≫ p)) 1` of
  relations `n · x - x` is zero, since every `n` in the trivial radical image is `1`.
- `fullLeviJacquetEquiv` (definition): the linear equivalence
  `(leviJacquetFunctor p l r hp hr hl hmul).obj π ≃ₗ[ℂ] π` between the normalized Jacquet
  module of `π` along `P`, read on `M(F)`, and the space of `π`. It is
  `Submodule.quotEquivOfEqBot` applied to the vanishing of the relations.
- `fullLeviJacquetEquiv_mk`: it sends the coinvariant class of `x` to `x` (by definition).
- `fullLeviJacquetEquiv_representation`: it intertwines the Jacquet action of `m ∈ M(F)`
  with `π` of its image `(l ≫ p)(m) ∈ G(F)`:
  `fullLeviJacquetEquiv (m · x) = π((l ≫ p)(m)) (fullLeviJacquetEquiv x)`. Proof: write `x`
  as a class `[y]`; the Jacquet action is `δ^{-1/2}(m) [π(m) y]` by
  `normalizedJacquetFunctor_obj_apply`, and the inverse half modulus is `1` by the lemma
  above since the radical image is trivial.

## Vanishing graded pieces

- `GeometricLemmaIntersectionDatum.subsingleton_pieceFunctor_obj`: for an intersection datum
  `D` and a smooth representation `ρ` of `M(F)`, if the normalized Jacquet module
  `(jacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj ρ` of `ρ` along
  `P' = M ∩ zQz⁻¹` is a subsingleton, then so is the graded piece `D.pieceFunctor.obj ρ`.
  Proof: the piece is the normalized induction of a pullback of that Jacquet module, so its
  elements are functions with values in the carrier of the Jacquet module (pullbacks keep
  the carrier); two such functions agree pointwise, hence are equal by `Subtype.ext` twice
  and `funext`.
