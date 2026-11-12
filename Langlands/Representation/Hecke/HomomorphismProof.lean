import Langlands.Representation.Hecke.HomomorphismStatements
import Langlands.Representation.Hecke.NondegenerateModuleEquivalenceProof
import Langlands.Algebra.NondegenerateFInductionAdjunction
import Langlands.Algebra.NondegeneratePInductionAdjunction
import Langlands.Algebra.RegularTensorContraction

/-! # Renard III.2.1: actual Hecke adjunctions and continuous pullback -/

noncomputable section

open CategoryTheory MeasureTheory MulOpposite

namespace Langlands.Hecke.Homomorphism

open Langlands.Algebra

universe uG uH v

/-- The canonical Chapter I adjunctions specialize to the specified Hecke actions. -/
theorem heckeInductionAdjunctionStatement :
    HeckeInductionAdjunctionStatement.{uG, uH, v} := by
  intro G _ _ _ _ _ _ _ H _ _ _ _ _ _ _ μG _ μH _ φ hφ
  constructor
  · let := leftModule μG μH φ hφ
    let := NonUnitalModule.rightRegular (HeckeAlgebra μG)
    exact NondegenerateInductionAdjunction.FProof.canonical
      (isIdempotented μH) (isIdempotented μG)
      (left_commutes_regular μG μH φ hφ) (left_regular_nondegenerate μG μH φ hφ)
  · let := NonUnitalModule.regular (HeckeAlgebra μG)
    let := rightModule μG μH φ hφ
    exact NondegenerateInductionAdjunction.PProof.canonical
      (isIdempotented μH) (isIdempotented μG)
      (regular_commutes_right μG μH φ hφ) (regular_right_nondegenerate μG μH φ hφ)

section Comparison

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] [T2Space H]
  [NonarchimedeanGroup H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
  (φ : H →* G) (hφ : Continuous φ)

/-- Evaluation of the integrated action intertwines restricted left translation. -/
def actionEvaluation (V : SmoothRep.{0, uG, max uG v} ℂ G) (m : V) :
    (leftRepresentation μG φ).IntertwiningMap (V.representation.comp φ) where
  toFun b := heckeAction μG V.representation V.isSmooth b m
  map_add' a b := congrArg (fun T : Module.End ℂ V => T m)
    ((heckeAction μG V.representation V.isSmooth).map_add a b)
  map_smul' c b := congrArg (fun T : Module.End ℂ V => T m)
    ((heckeAction μG V.representation V.isSmooth).map_smul c b)
  isIntertwining' h := by
    apply LinearMap.ext
    intro b
    exact integratedAction_leftTranslate μG V.representation V.isSmooth (φ h) b m

/-- The original balanced quotient contracts to the integrated pullback module. -/
def contractionHom (V : SmoothRep.{0, uG, max uG v} ℂ G) :
    (F μG μH φ hφ).obj (heckeNondegenerateModule μG V) ⟶
      heckeNondegenerateModule μH ((restriction φ hφ).obj V) := by
  letI := leftModule μG μH φ hφ
  letI := NonUnitalModule.rightRegular (HeckeAlgebra μG)
  letI := heckeNonUnitalModule μG V.representation V.isSmooth
  letI := heckeNonUnitalModule μH (V.representation.comp φ)
    (isSmooth_comp φ hφ V.isSmooth)
  exact ObjectProperty.homMk (NonUnitalBimoduleTensor.leftLift
    (left_commutes_regular μG μH φ hφ)
    (NonUnitalModule.toEndHom (heckeNonUnitalModule μG V.representation V.isSmooth)).toAddMonoidHom
    (RegularTensorContraction.action_balanced (HeckeAlgebra μG) V)
    (fun a b m => integratedAction_intertwiner μH
      (leftRepresentation_isSmooth μG φ hφ) (isSmooth_comp φ hφ V.isSmooth)
      (actionEvaluation μG φ V m) a b))

/-- Local units give injectivity on the actual quotient and surjectivity on V. -/
theorem contractionHom_bijective (V : SmoothRep.{0, uG, max uG v} ℂ G) :
    Function.Bijective (contractionHom μG μH φ hφ V).hom.toAddMonoidHom := by
  let := heckeNonUnitalModule μG V.representation V.isSmooth
  constructor
  · exact RegularTensorContraction.contraction_injective (HeckeAlgebra μG) V
      (isIdempotented μG)
  · intro m
    obtain ⟨e, he⟩ := heckeNonUnitalModule_isNondegenerate μG V.representation V.isSmooth m
    exact ⟨RegularTensorContraction.pure (HeckeAlgebra μG) V (e : HeckeAlgebra μG) m, he⟩

/-- The contraction is an isomorphism for the existing H-Hecke module action. -/
def contractionIso (V : SmoothRep.{0, uG, max uG v} ℂ G) :
    (F μG μH φ hφ).obj (heckeNondegenerateModule μG V) ≅
      heckeNondegenerateModule μH ((restriction φ hφ).obj V) := by
  let f := contractionHom μG μH φ hφ V
  let E := AddEquiv.ofBijective f.hom.toAddMonoidHom
    (contractionHom_bijective μG μH φ hφ V)
  refine
    { hom := f
      inv := ObjectProperty.homMk
        { toAddMonoidHom := E.symm.toAddMonoidHom
          map_smul' := ?_ }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · intro a m
    apply E.injective
    change E (E.symm (a • m)) = f.hom.toAddMonoidHom (a • E.symm m)
    rw [E.apply_symm_apply, f.hom.map_smul]
    change a • m = a • E (E.symm m)
    rw [E.apply_symm_apply]
  · apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro t
    exact E.symm_apply_apply t
  · apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    exact E.apply_symm_apply m

/-- Naturality of contraction uses the original tensor maps on pure tensors. -/
def heckePullbackComparison :
    heckeNondegenerateModuleFunctor.{uG, max uG v} μG ⋙ F μG μH φ hφ ≅
      restriction.{uG, uH, max uG v} φ hφ ⋙ heckeNondegenerateModuleFunctor μH :=
  NatIso.ofComponents (contractionIso μG μH φ hφ) (by
    intro V W f
    let := NonUnitalModule.rightRegular (HeckeAlgebra μG)
    let := heckeNonUnitalModule μG V.representation V.isSmooth
    let := heckeNonUnitalModule μG W.representation W.isSmooth
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    exact DFunLike.congr_fun (NonUnitalModuleTensor.hom_ext (HeckeAlgebra μG)
      (fun b m => (integratedAction_intertwiner μG V.isSmooth W.isSmooth
        (SmoothRep.hom f) b m).symm)))

end Comparison

/-- The actual smooth pullback identifies with the transported tensor functor. -/
def smoothPullbackComparison
    {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
    [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {H : Type uH} [Group H] [TopologicalSpace H] [T2Space H]
    [NonarchimedeanGroup H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
    (φ : H →* G) (hφ : Continuous φ)
    (eH : (heckeNondegenerateModuleFunctor.{uH, max uG v} μH).IsEquivalence) :
    restriction.{uG, uH, max uG v} φ hφ ≅ smoothF μG μH φ hφ eH := by
  letI := eH
  exact (Iso.compInverseIso
    (H := (heckeNondegenerateModuleFunctor μH).asEquivalence)
    (heckePullbackComparison μG μH φ hφ)).symm

/-- The specific III.1.4 equivalences transport both actual Hecke adjunctions. -/
theorem smoothInductionAdjunctionStatement :
    SmoothInductionAdjunctionStatement.{uG, uH, v} := by
  intro G _ _ _ _ _ _ _ H _ _ _ _ _ _ _ μG _ μH _ φ hφ
  let eG : (heckeNondegenerateModuleFunctor.{uG, max uG v} μG).IsEquivalence :=
    heckeNondegenerateModuleEquivalence G μG
  let eH : (heckeNondegenerateModuleFunctor.{uH, max uG v} μH).IsEquivalence :=
    heckeNondegenerateModuleEquivalence H μH
  let := eG
  let := eH
  refine ⟨eG, eH, ⟨smoothPullbackComparison μG μH φ hφ eH⟩, ?_, ?_⟩
  · let := leftModule μG μH φ hφ
    let := NonUnitalModule.rightRegular (HeckeAlgebra μG)
    exact ⟨((heckeNondegenerateModuleFunctor μG).adjunction.comp
      (NondegenerateInductionAdjunction.FProof.adjunction
        (isIdempotented μH) (isIdempotented μG)
        (left_commutes_regular μG μH φ hφ)
        (left_regular_nondegenerate μG μH φ hφ))).comp
      (heckeNondegenerateModuleFunctor μH).asEquivalence.symm.toAdjunction⟩
  · let := NonUnitalModule.regular (HeckeAlgebra μG)
    let := rightModule μG μH φ hφ
    exact ⟨((heckeNondegenerateModuleFunctor μH).adjunction.comp
      (NondegenerateInductionAdjunction.PProof.adjunction
        (isIdempotented μH) (isIdempotented μG)
        (regular_commutes_right μG μH φ hφ)
        (regular_right_nondegenerate μG μH φ hφ))).comp
      (heckeNondegenerateModuleFunctor μG).asEquivalence.symm.toAdjunction⟩

/-- Renard III.2.1, with the canonical Hecke adjunctions and continuous pullback. -/
theorem continuousHomomorphismStatements :
    ContinuousHomomorphismStatements.{uG, uH, v} :=
  ⟨heckeInductionAdjunctionStatement, smoothInductionAdjunctionStatement⟩

end Langlands.Hecke.Homomorphism
