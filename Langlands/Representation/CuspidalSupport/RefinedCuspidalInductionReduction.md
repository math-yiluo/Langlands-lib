# Reduction of refined cuspidal induction to standard cuspidal induction

Author: Worker 717.

This module reduces the published proposition
`Langlands.CuspidalSupport.RefinedCuspidalInductionFiniteLengthStatement`
from [`RefinedCuspidalInductionLengthStatement`](RefinedCuspidalInductionLengthStatement.md)
to the finite-length half of standard cuspidal induction,
`Langlands.CuspidalSupport.CuspidalInductionLengthTheorem` from
[`NormalizedCuspidalInductionStatement`](NormalizedCuspidalInductionStatement.md),
in positive rank. It does not prove the target proposition, and it does not
prove `CuspidalInductionLengthTheorem`. The field universe `uF` and the
representation universe `uV` are independent throughout, as in the target.

## Declarations

In namespace `Langlands.CuspidalSupport`, for a prime `p`,
`F : PadicField.{uF} p`, `T : F.TopologicalData`, `B : BlockShape n` and a
complex vector space `V`. The topologies are `T.topology`,
`T.generalLinearTopologicalGroup n` and `T.leviTopologicalGroup B`.

- `normalizedParabolicInduced_eval_surjective T B σ`: for
  `σ : Representation ℂ (B.Levi F.Carrier) V` with `IsSmooth σ`, every
  vector of `V` is the value at the identity `1` of some smooth function in the
  carrier of `T.normalizedParabolicInduced B σ`. That carrier consists of the
  smooth functions for the inflated, half-modulus-twisted representation
  `twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))`
  of the standard parabolic, and evaluation is `Induction.eval`.
- `jacquetEvaluation_id_surjective T B σ`: for smooth `σ`, the intertwiner
  `jacquetEvaluation T B (IntertwiningMap.id (T.normalizedParabolicInduced B σ))`
  from the normalized Jacquet module
  `T.normalizedJacquet B (T.normalizedParabolicInduced B σ)` to `σ` is
  surjective. This is the published evaluation-at-the-identity map of
  [`InducedJacquetEvaluation`](InducedJacquetEvaluation.md).
- `normalizedParabolicInduced_refined_finiteLength F T hlen B S ω`: let
  `hlen : CuspidalInductionLengthTheorem.{uF, uV} F T n`, let
  `S : BlockRefinement B` and `ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)`
  with `ω.ρ` irreducible and `IsLeviCuspidal (B.flatten S) ω.ρ`. Let `σ` be
  `ω.ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom`. Then
  `T.normalizedParabolicInduced B (T.normalizedRefinedInduced B S σ)` has finite
  length as a module over `MonoidAlgebra ℂ (GeneralLinear n F.Carrier)`.
- `refinedCuspidalInductionFiniteLength_of_cuspidalInductionLength F T hlen B S ω`:
  under the same hypotheses (with `hlen` for this one rank `n`), the target's
  conclusion holds for these `B`, `S`, `ω`. With
  `I = Rep.of (T.normalizedRefinedInduced B S σ) : Rep.{max uF uV} ℂ (B.Levi F.Carrier)`,
  `I.ρ` is admissible, `I.ρ.asModule` has finite length over
  `MonoidAlgebra ℂ (B.Levi F.Carrier)`, and `HasCompositionSeriesLength I m`
  holds for some `m : ℕ`. The transport, the induced object and the `Rep.of`
  packaging are those of the target.
- `RefinedCuspidalInductionReductionClause` is the record's named definition.
  It is a proposition (`Prop`) with universe parameters `uF` and `uV`: if
  `CuspidalInductionLengthTheorem.{uF, uV} F T n` holds for every prime `p`
  (with `[Fact p.Prime]`), every `F : PadicField.{uF} p`, every
  `T : F.TopologicalData` and every `n` with `0 < n`, then
  `RefinedCuspidalInductionFiniteLengthStatement.{uF, uV}` holds. The
  hypothesis has the same form as the `CuspidalInductionLengthTheorem` part of
  the published `PadicCuspidalInductionTheorems`.
- `refinedCuspidalInductionReductionClause_holds` proves this clause.

## Implemented proof

1. `normalizedParabolicInduced_eval_surjective`. The inflated and twisted
   representation of the standard parabolic is smooth: inflation along the
   continuous Levi projection `T.blockLeviProjection B` preserves smoothness
   (`isSmooth_comp`), and so does a twist by a character with open kernel
   (`isSmooth_twist_iff`, `T.isOpen_ker_parabolicHalfModulus B`). For a vector
   `v`, the published `Induction.compactLocalSection` (with base point `1` and
   open set `Set.univ` of the coset space) gives a compactly supported smooth
   section, and `Induction.compactLocalSection_apply` says that its value at
   `1` is `v`. Its underlying smooth function is the required preimage.
2. `jacquetEvaluation_id_surjective`. The Jacquet evaluation of the identity
   sends the class `B.jacquetMk _ f` to the value of `f` at `1`. So step 1
   gives surjectivity.
3. `normalizedParabolicInduced_refined_finiteLength`. This is induction in
   stages.
   - `σ` is smooth, by `Parabolic.isAdmissible_flattenedLeviTransport_iff`
     from [`RefinedInductionAdmissibility`](../Parabolic/RefinedInductionAdmissibility.md)
     applied to the admissibility part of `IsLeviCuspidal`.
   - The published natural isomorphism of
     `Parabolic.normalizedRefinementInductionTransitivity`, evaluated at
     `SmoothRep.of σ`, gives a representation equivalence `E₁` from
     `T.normalizedParabolicInduced B (T.normalizedRefinedInduced B S σ)` to
     direct induction `T.normalizedComposedInduced B S σ` from the composed
     parabolic. The functor objects are unfolded by `dsimp`, as in the
     published `Parabolic.OrderedRefinementInduction`.
   - `Parabolic.composedFlattenedInduction` gives an equivalence `E₂` from
     `T.normalizedComposedInduced B S σ` to standard normalized induction
     `T.normalizedParabolicInduced (B.flatten S) (σ.comp e.toMonoidHom)`, where
     `e = flattenedLeviEquiv F.Carrier B S`. Here `σ.comp e.toMonoidHom = ω.ρ`.
   - `hlen`, applied to the flattened shape `B.flatten S` and
     `SmoothRep.of ω.ρ`, says that this standard induction has finite length.
     The composite `E₂ ∘ E₁` is injective, so
     `FiniteLengthAssembly.finiteLength_of_injective` transfers finite length
     to its source.
4. `refinedCuspidalInductionFiniteLength_of_cuspidalInductionLength`.
   Admissibility of `I.ρ` is the published
   `Parabolic.refinedCuspidalInduction_isAdmissible`. The outer induction
   `J = T.normalizedParabolicInduced B I.ρ` is then admissible
   (`Parabolic.normalizedInductionAdmissibility`). By step 3, `J` has finite
   length, so it is Noetherian and hence finitely generated over the group
   algebra (`isFiniteLength_iff_isNoetherian_isArtinian`). The published
   `Parabolic.normalizedJacquetFiniteLength` therefore says that
   `T.normalizedJacquet B J` has finite length over
   `MonoidAlgebra ℂ (B.Levi F.Carrier)`. By step 2, `I.ρ` is a quotient of
   this Jacquet module, because the normalized refined induction is smooth
   (`T.isSmooth_normalizedRefinedInduced`). Finite length passes to the
   quotient (`FiniteLengthAssembly.finiteLength_of_surjective`). The
   composition series comes from finite length by
   `exists_hasCompositionSeriesLength_of_isFiniteLength` from
   [`RefinedCuspidalInductionRankZero`](RefinedCuspidalInductionRankZero.md).
5. `refinedCuspidalInductionReductionClause_holds`. In rank `0`, the published
   `refinedCuspidalInductionFiniteLength_rankZero` from
   [`RefinedCuspidalInductionRankZero`](RefinedCuspidalInductionRankZero.md)
   gives the conclusion without any hypothesis on standard induction. In
   positive rank, step 4 applies with the hypothesis for that rank.

All objects are the actual ones of the target: normalized refined induction
with right translation and positive half-modulus normalization, and the
standard Jacquet module of the standard parabolic. No tensor decomposition of
`ω`, finite dimension, finite generation or chosen series is assumed.

## Provenance

Internal. The target's Markdown records its motivation. The route combines
three standard facts about normalized parabolic induction `i` and the
normalized Jacquet functor `r` in Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups. I* (1977), Proposition 2.3,
printed p.446 (source `bernstein-zelevinsky-1977-induced-i`): `r` is left
adjoint to `i` (part (b)), whose counit at the identity of `i(σ)` is the
surjection `r(i(σ)) → σ` used in step 2; induction in stages (part (c)),
used in step 3; and preservation of admissibility (part (e)), used in step 4.
The Lean proof does not use the adjunction itself, only the evaluation map
and its surjectivity. Finite length of Jacquet modules of finitely generated
admissible representations is the published
`Parabolic.normalizedJacquetFiniteLength`. There is no single source statement
to translate.
