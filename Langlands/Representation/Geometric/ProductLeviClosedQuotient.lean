import Langlands.Representation.Geometric.ProductLeviGeometricLemmaStatement
import Langlands.Representation.Parabolic.ComposedFlattenedInductionProof
import Langlands.Representation.Parabolic.RefinementInductionTransitivityProof
import Langlands.Representation.Parabolic.FlattenedJacquetQuotientProof
import Langlands.Representation.CuspidalSupport.RefinedCuspidalInductionReduction

/-! Natural maps from the ambient composite to the composite in a coarse Levi. -/

noncomputable section

set_option maxHeartbeats 1200000

open CategoryTheory

namespace Langlands.Geometric

open GeneralLinear Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- The function-preserving flattened induction comparisons form a natural
isomorphism on the full smooth category. -/
def composedFlattenedInductionIso (Q : BlockRefinement B) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    T.normalizedComposedInductionFunctor.{uF, uV} B Q ≅
      SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q) ⋙
        T.normalizedParabolicInductionFunctor (B.flatten Q) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := T.generalLinearTopologicalGroup n
  let E := fun A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B Q) =>
    (composedFlattenedInduction p F T n B Q A A.representation).choose
  have hE := fun A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B Q) =>
    (composedFlattenedInduction p F T n B Q A A.representation).choose_spec.1
  refine NatIso.ofComponents (fun A => SmoothRep.mkIso (E A)) ?_
  intro A A' f
  ext φ
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change Induction.eval _ _ (E A' (T.normalizedComposedInducedMap B Q
      (SmoothRep.hom f) φ)) g =
    (SmoothRep.hom f) (Induction.eval _ _ (E A φ) g)
  dsimp only [E]
  rw [hE A' _ g]
  exact congrArg (fun x => (SmoothRep.hom f) x) (hE A φ g).symm

/-- Pullback successively along a group equivalence and its inverse has the
identity linear comparison. -/
def flattenedPullbackCancellation (Q : BlockRefinement B) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    (SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q).symm ⋙
      SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q)) ≅
        𝟭 (SmoothRep.{0, uF, uV} ℂ ((B.flatten Q).Levi F.Carrier)) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  refine NatIso.ofComponents (fun A => SmoothRep.mkIso
    (Representation.Equiv.mk (LinearEquiv.refl ℂ A) ?_)) ?_
  · intro m
    ext v
    change A.representation
      ((flattenedLeviEquiv F.Carrier B Q).symm
        (flattenedLeviEquiv F.Carrier B Q m)) v = A.representation m v
    rw [MulEquiv.symm_apply_apply]
  · intro A A' f
    rfl

/-- Normalized induction from a flattened refinement is naturally induction
in stages through its coarse Levi. -/
def flattenedInductionInStagesIso (Q : BlockRefinement B) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    T.normalizedParabolicInductionFunctor.{uF, uV} (B.flatten Q) ≅
      SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q).symm ⋙
        T.normalizedRefinedInductionFunctor B Q ⋙
        T.normalizedParabolicInductionFunctor B := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  let L := SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q).symm
  let E := (normalizedRefinementInductionTransitivity F T B Q).choose
  exact ((Functor.isoWhiskerLeft L E) ≪≫
    (Functor.isoWhiskerLeft L (composedFlattenedInductionIso T B Q)) ≪≫
    (Functor.isoWhiskerRight (flattenedPullbackCancellation T B Q)
      (T.normalizedParabolicInductionFunctor (B.flatten Q))) ≪≫
    (Functor.leftUnitor _)).symm

/-- The normalized Jacquet quotient into the two successive normalized
Jacquet quotients is natural in the ambient smooth representation. -/
def flattenedJacquetNaturalMap (S : BlockRefinement B) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    T.normalizedJacquetFunctor.{uF, uV} (B.flatten S) ⟶
      T.normalizedJacquetFunctor B ⋙ T.normalizedRefinedJacquetFunctor B S ⋙
        SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B S) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  refine { app := fun A => ?_, naturality := ?_ }
  · exact SmoothRep.ofHom (flattenedJacquetQuotientMap T B S A.representation)
  · intro A A' f
    ext x
    obtain ⟨v, rfl⟩ := (B.flatten S).jacquetMk_surjective A.representation x
    rfl

/-- Evaluation of normalized induction at the identity, after normalized
Jacquet, is a natural map on the full smooth category. -/
def parabolicJacquetEvaluation :
    letI := T.topology
    T.normalizedParabolicInductionFunctor.{uF, max uF uV} B ⋙
      T.normalizedJacquetFunctor B ⟶
        𝟭 (SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  refine { app := fun A => ?_, naturality := ?_ }
  · exact SmoothRep.ofHom (CuspidalSupport.jacquetEvaluation T B
      (Representation.IntertwiningMap.id (T.normalizedParabolicInduced B A.representation)))
  · intro A A' f
    ext x
    obtain ⟨φ, rfl⟩ := B.jacquetMk_surjective
      (T.normalizedParabolicInduced B A.representation) x
    rfl

/-- The ambient normalized composite maps naturally onto the normalized
composite computed inside the coarse product Levi. -/
def productLeviQuotientMap (Q S : BlockRefinement B) :
    letI := T.topology
    jacquetInductionFunctor.{uF, uV} T (B.flatten Q) (B.flatten S) ⟶
      innerJacquetInductionFunctor T B Q S := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  dsimp only [jacquetInductionFunctor, innerJacquetInductionFunctor]
  let I := SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q).symm ⋙
    T.normalizedRefinedInductionFunctor.{uF, uV} B Q
  let R := T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S ⋙
    SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B S) ⋙
      SmoothRep.toRep
  exact Functor.whiskerRight (flattenedInductionInStagesIso.{uF, uV} T B Q).hom
      (T.normalizedJacquetFunctor (B.flatten S) ⋙ SmoothRep.toRep) ≫
    Functor.whiskerLeft (I ⋙ T.normalizedParabolicInductionFunctor B)
      (Functor.whiskerRight (flattenedJacquetNaturalMap.{uF, max uF uV} T B S)
        SmoothRep.toRep) ≫
    Functor.whiskerRight (Functor.whiskerLeft I (parabolicJacquetEvaluation.{uF, uV} T B)) R

/-- Every component of the natural comparison onto the inner composite is
surjective, without admissibility or length assumptions. -/
theorem productLeviQuotientMap_surjective (Q S : BlockRefinement B) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ ((B.flatten Q).Levi F.Carrier),
      Function.Surjective ((productLeviQuotientMap T B Q S).app A).hom := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  intro A
  let I := SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q).symm ⋙
    T.normalizedRefinedInductionFunctor.{uF, uV} B Q
  let X := (T.normalizedParabolicInductionFunctor (B.flatten Q)).obj A
  let E := SmoothRep.equivOfIso ((flattenedInductionInStagesIso T B Q).app A)
  intro w
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective (I.obj A).representation
    (refinedUnipotent F.Carrier B S) w
  obtain ⟨φ, hφ⟩ := CuspidalSupport.normalizedParabolicInduced_eval_surjective
    T B (I.obj A).representation (I.obj A).isSmooth v
  refine ⟨(B.flatten S).jacquetMk X.representation (E.symm φ), ?_⟩
  change refinedJacquetMk B S (I.obj A).representation
    (Induction.eval (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B)
        ((I.obj A).representation.comp (B.leviProjection F.Carrier)))
      (E (E.symm φ)) 1) = refinedJacquetMk B S (I.obj A).representation v
  rw [E.apply_symm_apply φ]
  exact congrArg (refinedJacquetMk B S (I.obj A).representation) hφ

end Langlands.Geometric
