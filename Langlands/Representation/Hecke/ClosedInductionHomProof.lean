import Langlands.Representation.Hecke.CompactInductionComparisonLaws
import Langlands.Representation.Hecke.ClosedInductionStatements
import Langlands.Representation.Hecke.ActionLocalUnits

noncomputable section

open CategoryTheory MeasureTheory

namespace Langlands.Hecke.Homomorphism

open Langlands.Algebra HarmonicAnalysis

universe uG v

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μG : Measure G) [μG.IsHaarMeasure]
  (H : Subgroup G) [LocallyCompactSpace H]
  (μH : Measure H) [μH.IsHaarMeasure]

local instance : NonUnitalModule (HeckeAlgebra μH) (HeckeAlgebra μG) :=
  leftModule μG μH H.subtype continuous_subtype_val

/-- Every original nondegenerate Hom vector has a compact-open right local unit. -/
theorem homInduction_exists_localUnit
    (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (q : ((homInductionHeckeFunctor μG H μH).obj W).obj) :
    ∃ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
      ∀ T : HeckeAlgebra μG,
        homInductionEvaluation μG H μH W q
          (T * HeckeAlgebra.normalizedIndicator μG K hK) =
            homInductionEvaluation μG H μH W q T := by
  classical
  let := heckeNonUnitalModule μH W.representation W.isSmooth
  let f : NonUnitalModuleHom (HeckeAlgebra μH) (HeckeAlgebra μG) W := q.val
  obtain ⟨e, he⟩ :=
    (RenardHomFunctors.mem_inductionPart
      (left_commutes_regular μG μH H.subtype continuous_subtype_val)
      (isIdempotented μG) f).mp q.property
  obtain ⟨K, hK, _, _, hfix⟩ :=
    HeckeAlgebra.finiteFamilyLocalUnits G μG {(e : HeckeAlgebra μG)} ⊤
  refine ⟨K, hK, ?_⟩
  intro T
  change f (T * HeckeAlgebra.normalizedIndicator μG K hK) = f T
  calc
    _ = f ((T * HeckeAlgebra.normalizedIndicator μG K hK) * (e : HeckeAlgebra μG)) :=
      (he _).symm
    _ = f (T * (e : HeckeAlgebra μG)) := by
      congr 1
      rw [mul_assoc, (hfix (e : HeckeAlgebra μG) (Finset.mem_singleton_self _)).1]
    _ = f T := he T

/-- Translated subgroup local units act by the original restricted group action. -/
theorem leftModule_translated_localUnit
    (U : OpenSubgroup H) (hU : IsCompact (U : Set H))
    (h : H) (T : HeckeAlgebra μG)
    (hT : HeckeAlgebra.normalizedIndicator μH U hU • T = T) :
    (show HeckeAlgebra μH from
      GroupAction.leftTests h (HeckeAlgebra.normalizedIndicator μH U hU)) • T =
        leftRepresentation μG H.subtype h T := by
  change integratedAction μH (leftRepresentation μG H.subtype)
    (leftRepresentation_isSmooth μG H.subtype continuous_subtype_val)
    (TestFunction.leftTranslate h (HeckeAlgebra.normalizedIndicator μH U hU)) T = _
  exact (integratedAction_leftTranslate μH (leftRepresentation μG H.subtype)
    (leftRepresentation_isSmooth μG H.subtype continuous_subtype_val) h
    (HeckeAlgebra.normalizedIndicator μH U hU) T).trans
      (congrArg (leftRepresentation μG H.subtype h) hT)

/-- The original Hom carrier, with both prescribed integrated subgroup actions. -/
abbrev closedHom (W : Langlands.SmoothRep.{0, uG, v} ℂ H) :=
  letI := heckeNonUnitalModule μH W.representation W.isSmooth
  NonUnitalModuleHom (HeckeAlgebra μH) (HeckeAlgebra μG) W

/-- Expose a nondegenerate Hom vector as its actual module map. -/
def homInductionRaw (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (q : ((homInductionHeckeFunctor μG H μH).obj W).obj) :
    closedHom μG H μH W := q.val

/-- Module maps on the restricted regular representation are complex linear. -/
theorem closedHom_map_complex (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (q : closedHom μG H μH W) (c : ℂ) (T : HeckeAlgebra μG) :
    q (c • T) = c • q T := by
  let := heckeNonUnitalModule μH W.representation W.isSmooth
  obtain ⟨e, he⟩ := leftModule_isNondegenerate μG μH H.subtype continuous_subtype_val T
  calc
    q (c • T) = q ((c • (e : HeckeAlgebra μH)) • T) := by
      rw [NonUnitalModule.ofLinearEndHom_smul_assoc, he]
    _ = (c • (e : HeckeAlgebra μH)) • q T := q.map_smul _ T
    _ = c • ((e : HeckeAlgebra μH) • q T) :=
      NonUnitalModule.ofLinearEndHom_smul_assoc _ c _ _
    _ = c • q T := by rw [← q.map_smul, he]

/-- The actual module map preserves the subgroup's original group action. -/
theorem closedHom_map_group (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (q : closedHom μG H μH W) (h : H) (T : HeckeAlgebra μG) :
    q (leftRepresentation μG H.subtype h T) = W.representation h (q T) := by
  let := heckeNonUnitalModule μH W.representation W.isSmooth
  obtain ⟨e, he⟩ := leftModule_isNondegenerate μG μH H.subtype continuous_subtype_val T
  have heq : (e : HeckeAlgebra μH) • q T = q T := by rw [← q.map_smul, he]
  have hleft :
      (show HeckeAlgebra μH from GroupAction.leftTests h (e : HeckeAlgebra μH)) • T =
        leftRepresentation μG H.subtype h T :=
    (integratedAction_leftTranslate μH (leftRepresentation μG H.subtype)
      (leftRepresentation_isSmooth μG H.subtype continuous_subtype_val) h
      (e : HeckeAlgebra μH) T).trans
        (congrArg (leftRepresentation μG H.subtype h) he)
  have hright :
      (show HeckeAlgebra μH from GroupAction.leftTests h (e : HeckeAlgebra μH)) • q T =
        W.representation h (q T) :=
    (integratedAction_leftTranslate μH W.representation W.isSmooth h
      (e : HeckeAlgebra μH) (q T)).trans (congrArg (W.representation h) heq)
  rw [← hleft, q.map_smul, hright]

/-- Evaluation at a point as an algebraic linear map on the actual induction. -/
def inducedEvaluationLinear (W : Langlands.SmoothRep.{0, uG, v} ℂ H) (g : G) :
    Induction.SmoothFunctions H W.representation →ₗ[ℂ] W where
  toFun f := Induction.eval H W.representation f g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The forward formula as a complex-linear map on the original Hecke carrier. -/
def closedForwardLinear (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (f : Induction.SmoothFunctions H W.representation) :
    HeckeAlgebra μG →ₗ[ℂ] W where
  toFun T := inducedEvaluationLinear H W 1
    (heckeAction μG (Induction.smoothInduced H W.representation)
      (Induction.smoothInduced_smooth H W.representation) T f)
  map_add' T S := by simp only [map_add, LinearMap.add_apply]
  map_smul' c T := by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]

omit [T2Space G] [LocallyCompactSpace G] [LocallyCompactSpace H] in
/-- Covariance of the forward linear map under the restricted regular action. -/
theorem closedForwardLinear_group (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (f : Induction.SmoothFunctions H W.representation) (h : H) (T : HeckeAlgebra μG) :
    closedForwardLinear μG H W f (leftRepresentation μG H.subtype h T) =
      W.representation h (closedForwardLinear μG H W f T) := by
  let ρ := Induction.smoothInduced H W.representation
  have hρ := Induction.smoothInduced_smooth H W.representation
  have ht := integratedAction_leftTranslate μG ρ hρ (h : G) T f
  have hc : Induction.eval H W.representation
      (ρ (h : G) (integratedAction μG ρ hρ T f)) 1 =
        W.representation h (Induction.eval H W.representation
          (integratedAction μG ρ hρ T f) 1) := by
    let z := integratedAction μG ρ hρ T f
    change z.val.val (1 * (h : G)) = W.representation h (z.val.val 1)
    simpa only [one_mul, mul_one, Subgroup.subtype_apply] using z.val.property h 1
  exact (congrArg (fun z => Induction.eval H W.representation z 1) ht).trans hc

/-- The forward formula is an intertwiner for the restricted regular action. -/
def closedForwardIntertwiner (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (f : Induction.SmoothFunctions H W.representation) :
    (leftRepresentation μG H.subtype).IntertwiningMap W.representation where
  toLinearMap := closedForwardLinear μG H W f
  isIntertwining' h := by
    apply LinearMap.ext
    intro T
    exact closedForwardLinear_group μG H W f h T

/-- The forward formula is linear for the actual subgroup Hecke action. -/
def closedForwardRaw (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (f : Induction.SmoothFunctions H W.representation) :
    closedHom μG H μH W := by
  letI := heckeNonUnitalModule μH W.representation W.isSmooth
  exact
    { toAddMonoidHom := (closedForwardIntertwiner μG H W f).toLinearMap.toAddMonoidHom
      map_smul' := fun a T =>
        integratedAction_intertwiner μH
          (leftRepresentation_isSmooth μG H.subtype continuous_subtype_val)
          W.isSmooth (closedForwardIntertwiner μG H W f) a T }

omit [T2Space G] [LocallyCompactSpace G] [LocallyCompactSpace H] in
/-- Associativity gives the residual right-convolution formula for the forward map. -/
theorem closedForwardLinear_mul (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (f : Induction.SmoothFunctions H W.representation) (T a : HeckeAlgebra μG) :
    closedForwardLinear μG H W f (T * a) =
      closedForwardLinear μG H W
        (heckeAction μG (Induction.smoothInduced H W.representation)
          (Induction.smoothInduced_smooth H W.representation) a f) T := by
  change inducedEvaluationLinear H W 1
      ((heckeAction μG _ _ (T * a)) f) = _
  rw [map_mul]
  rfl

/-- The forward formula belongs to the actual nondegenerate Hom part. -/
def closedForward (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (f : Induction.SmoothFunctions H W.representation) :
    ((homInductionHeckeFunctor μG H μH).obj W).obj := by
  letI := heckeNonUnitalModule μH W.representation W.isSmooth
  refine ⟨closedForwardRaw μG H μH W f, ?_⟩
  apply (RenardHomFunctors.mem_inductionPart
    (left_commutes_regular μG μH H.subtype continuous_subtype_val)
    (isIdempotented μG) _).mpr
  obtain ⟨K, hK, hf⟩ := exists_normalizedIndicator_fixes μG
    (Induction.smoothInduced H W.representation)
    (Induction.smoothInduced_smooth H W.representation) f
  refine ⟨⟨HeckeAlgebra.normalizedIndicator μG K hK,
    HeckeAlgebra.normalizedIndicator_idempotent μG K hK⟩, ?_⟩
  intro T
  change closedForwardLinear μG H W f
    (T * HeckeAlgebra.normalizedIndicator μG K hK) = closedForwardLinear μG H W f T
  rw [closedForwardLinear_mul, hf]

/-- The prescribed forward map is a morphism of the original nonunital modules. -/
def closedForwardHom (W : Langlands.SmoothRep.{0, uG, v} ℂ H) :
    NonUnitalModuleHom (HeckeAlgebra μG) ((inducedHeckeFunctor μG H).obj W).obj
      ((homInductionHeckeFunctor μG H μH).obj W).obj where
  toFun := closedForward μG H μH W
  map_zero' := by
    apply Subtype.ext
    apply NonUnitalModuleHom.ext
    intro T
    exact ((inducedEvaluationLinear H W 1).comp
      (heckeAction μG (Induction.smoothInduced H W.representation)
        (Induction.smoothInduced_smooth H W.representation) T)).map_zero
  map_add' f z := by
    apply Subtype.ext
    apply NonUnitalModuleHom.ext
    intro T
    exact ((inducedEvaluationLinear H W 1).comp
      (heckeAction μG (Induction.smoothInduced H W.representation)
        (Induction.smoothInduced_smooth H W.representation) T)).map_add f z
  map_smul' a f := by
    apply Subtype.ext
    apply NonUnitalModuleHom.ext
    intro T
    exact (closedForwardLinear_mul μG H W f T a).symm

omit [T2Space G] [LocallyCompactSpace G] [LocallyCompactSpace H] in
/-- Evaluation of a translated test function recovers the acted-on function. -/
theorem closedForward_translate (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (f : Induction.SmoothFunctions H W.representation) (g : G) (a : HeckeAlgebra μG) :
    closedForwardLinear μG H W f (GroupAction.leftTests g a) =
      Induction.eval H W.representation
        (heckeAction μG (Induction.smoothInduced H W.representation)
          (Induction.smoothInduced_smooth H W.representation) a f) g := by
  change Induction.eval H W.representation
    (integratedAction μG (Induction.smoothInduced H W.representation)
      (Induction.smoothInduced_smooth H W.representation) (TestFunction.leftTranslate g a) f) 1 = _
  have ht := integratedAction_leftTranslate μG (Induction.smoothInduced H W.representation)
    (Induction.smoothInduced_smooth H W.representation) g a f
  have hv := congrArg (fun z => Induction.eval H W.representation z 1) ht
  change _ = Induction.eval H W.representation (heckeAction μG _ _ a f) (1 * g) at hv
  simpa only [one_mul] using hv

/-- The forward map is injective on the actual smooth functions. -/
theorem closedForward_injective (W : Langlands.SmoothRep.{0, uG, v} ℂ H) :
    Function.Injective (closedForward μG H μH W) := by
  classical
  intro f z hfz
  obtain ⟨K, hK, hfix⟩ := exists_normalizedIndicator_fixes_finset μG
    (Induction.smoothInduced H W.representation)
    (Induction.smoothInduced_smooth H W.representation) {f, z}
  apply Subtype.ext
  apply Subtype.ext
  funext g
  have heq := congrArg (fun q => homInductionEvaluation μG H μH W q
    (GroupAction.leftTests g (HeckeAlgebra.normalizedIndicator μG K hK))) hfz
  change closedForwardLinear μG H W f _ = closedForwardLinear μG H W z _ at heq
  rw [closedForward_translate, closedForward_translate,
    hfix f (by simp), hfix z (by simp)] at heq
  exact heq

omit [T2Space G] [LocallyCompactSpace G] [BorelSpace G] [μG.IsHaarMeasure] in
/-- A compact-open normalized indicator is fixed by the subgroup's left translations. -/
theorem leftTests_normalizedIndicator (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (k : K) :
    GroupAction.leftTests (k : G) (HeckeAlgebra.normalizedIndicator μG K hK) =
      HeckeAlgebra.normalizedIndicator μG K hK := by
  apply TestFunction.ext
  intro x
  exact (HeckeAlgebra.normalizedIndicator_mem_biInvariant μG K hK).1 k⁻¹ x

/-- The inverse formula for a chosen compact-open subgroup is an actual smooth function. -/
def closedInverseAt (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (q : closedHom μG H μH W) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    Induction.SmoothFunctions H W.representation :=
  Induction.smoothFunctionOf H W.representation
    (fun g => q (GroupAction.leftTests g (HeckeAlgebra.normalizedIndicator μG K hK)))
    (by
      intro h x
      rw [map_mul]
      exact closedHom_map_group μG H μH W q h
        (GroupAction.leftTests x (HeckeAlgebra.normalizedIndicator μG K hK)))
    K (by
      intro k x
      rw [map_mul]
      change q (GroupAction.leftTests x
        (GroupAction.leftTests (k : G) (HeckeAlgebra.normalizedIndicator μG K hK))) = _
      rw [leftTests_normalizedIndicator])

/-- The original Hecke-module map with its automatic complex-linear structure. -/
def closedHomLinear (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (q : closedHom μG H μH W) : HeckeAlgebra μG →ₗ[ℂ] W := by
  letI := heckeNonUnitalModule μH W.representation W.isSmooth
  exact
    { toFun := q
      map_add' := q.map_add
      map_smul' := closedHom_map_complex μG H μH W q }

/-- Scalar point evaluation on the actual Hecke carrier. -/
def closedHeckeEvaluation (x : G) : HeckeAlgebra μG →ₗ[ℂ] ℂ where
  toFun T := T x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Integrating the actual left regular representation gives convolution. -/
theorem integrated_leftTests (T a : HeckeAlgebra μG) :
    integratedAction μG GroupAction.leftTests isSmooth_leftTests T a = T * a :=
  integratedAction_leftTests μG T a

/-- The forward map of the inverse formula is right convolution by its indicator. -/
theorem closedForward_inverseAt (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (q : closedHom μG H μH W) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (T : HeckeAlgebra μG) :
    closedForwardLinear μG H W (closedInverseAt μG H μH W q K hK) T =
      q (T * HeckeAlgebra.normalizedIndicator μG K hK) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro L
  rw [map_sub, sub_eq_zero]
  have hf := integratedAction_dual μG (Induction.smoothInduced H W.representation)
    (Induction.smoothInduced_smooth H W.representation) (HeckeAlgebra.toTestFunction μG T)
    (closedInverseAt μG H μH W q K hK) (L.comp (inducedEvaluationLinear H W 1))
  have hq := integratedAction_dual μG GroupAction.leftTests isSmooth_leftTests
    (HeckeAlgebra.toTestFunction μG T) (HeckeAlgebra.normalizedIndicator μG K hK)
    (L.comp (closedHomLinear μG H μH W q))
  calc
    _ = ∫ g, T g * (L.comp (inducedEvaluationLinear H W 1))
        (Induction.smoothInduced H W.representation g
          (closedInverseAt μG H μH W q K hK)) ∂μG := hf
    _ = ∫ g, T g * L (q (GroupAction.leftTests g
        (HeckeAlgebra.normalizedIndicator μG K hK))) ∂μG := by
      apply integral_congr_ae
      filter_upwards [] with g
      change T g * L (q (GroupAction.leftTests (1 * g)
        (HeckeAlgebra.normalizedIndicator μG K hK))) = _
      rw [one_mul]
    _ = (L.comp (closedHomLinear μG H μH W q))
        (integratedAction μG GroupAction.leftTests isSmooth_leftTests
          (HeckeAlgebra.toTestFunction μG T) (HeckeAlgebra.normalizedIndicator μG K hK)) :=
      hq.symm
    _ = _ := congrArg (L.comp (closedHomLinear μG H μH W q))
      (integrated_leftTests μG T (HeckeAlgebra.normalizedIndicator μG K hK))

/-- Every actual nondegenerate Hom vector is in the image of the prescribed forward map. -/
theorem closedForward_surjective (W : Langlands.SmoothRep.{0, uG, v} ℂ H) :
    Function.Surjective (closedForward μG H μH W) := by
  intro q
  obtain ⟨K, hK, hfix⟩ := homInduction_exists_localUnit μG H μH W q
  refine ⟨closedInverseAt μG H μH W (homInductionRaw μG H μH W q) K hK, ?_⟩
  apply Subtype.ext
  apply NonUnitalModuleHom.ext
  intro T
  exact (closedForward_inverseAt μG H μH W (homInductionRaw μG H μH W q) K hK T).trans
    (hfix T)

/-- Choose the inverse using the surjectivity supplied by compact-open local units. -/
def closedInverse (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (q : ((homInductionHeckeFunctor μG H μH).obj W).obj) :
    Induction.SmoothFunctions H W.representation :=
  Classical.choose (closedForward_surjective μG H μH W q)

/-- The chosen inverse returns the original Hom vector. -/
theorem closedForward_inverse (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (q : ((homInductionHeckeFunctor μG H μH).obj W).obj) :
    closedForward μG H μH W (closedInverse μG H μH W q) = q :=
  Classical.choose_spec (closedForward_surjective μG H μH W q)

/-- The inverse is independent of the fixing compact-open local unit. -/
theorem closedInverse_formula (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (q : ((homInductionHeckeFunctor μG H μH).obj W).obj)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hfix : ∀ T : HeckeAlgebra μG,
      homInductionEvaluation μG H μH W q (T * HeckeAlgebra.normalizedIndicator μG K hK) =
        homInductionEvaluation μG H μH W q T) (g : G) :
    Induction.eval H W.representation (closedInverse μG H μH W q) g =
      homInductionEvaluation μG H μH W q
        (GroupAction.leftTests g (HeckeAlgebra.normalizedIndicator μG K hK)) := by
  have heq : closedInverse μG H μH W q =
      closedInverseAt μG H μH W (homInductionRaw μG H μH W q) K hK := by
    apply closedForward_injective μG H μH W
    rw [closedForward_inverse]
    apply Eq.symm
    apply Subtype.ext
    apply NonUnitalModuleHom.ext
    intro T
    exact (closedForward_inverseAt μG H μH W (homInductionRaw μG H μH W q) K hK T).trans
      (hfix T)
  exact congrArg (fun f => Induction.eval H W.representation f g) heq

/-- The inverse also recovers every original smooth function. -/
theorem closedInverse_forward (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (f : Induction.SmoothFunctions H W.representation) :
    closedInverse μG H μH W (closedForward μG H μH W f) = f :=
  closedForward_injective μG H μH W
    (closedForward_inverse μG H μH W (closedForward μG H μH W f))

/-- The inverse inherits additivity and Hecke linearity from the bijective forward map. -/
def closedInverseHom (W : Langlands.SmoothRep.{0, uG, v} ℂ H) :
    NonUnitalModuleHom (HeckeAlgebra μG) ((homInductionHeckeFunctor μG H μH).obj W).obj
      ((inducedHeckeFunctor μG H).obj W).obj := by
  letI := heckeNonUnitalModule μG (Induction.smoothInduced H W.representation)
    (Induction.smoothInduced_smooth H W.representation)
  refine
    { toFun := closedInverse μG H μH W
      map_zero' := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · apply closedForward_injective μG H μH W
    exact (closedForward_inverse μG H μH W 0).trans
      (closedForwardHom μG H μH W).map_zero.symm
  · intro q r
    apply closedForward_injective μG H μH W
    calc
      _ = q + r := closedForward_inverse μG H μH W (q + r)
      _ = closedForward μG H μH W (closedInverse μG H μH W q) +
          closedForward μG H μH W (closedInverse μG H μH W r) :=
        congrArg₂ (· + ·) (closedForward_inverse μG H μH W q).symm
          (closedForward_inverse μG H μH W r).symm
      _ = _ := ((closedForwardHom μG H μH W).map_add _ _).symm
  · intro a q
    apply closedForward_injective μG H μH W
    calc
      _ = a • q := closedForward_inverse μG H μH W (a • q)
      _ = a • closedForward μG H μH W (closedInverse μG H μH W q) :=
        congrArg (a • ·) (closedForward_inverse μG H μH W q).symm
      _ = _ := ((closedForwardHom μG H μH W).map_smul a _).symm

/-- The explicit comparison on each original smooth representation. -/
def closedComponentIso (W : Langlands.SmoothRep.{0, uG, v} ℂ H) :
    (inducedHeckeFunctor μG H).obj W ≅ (homInductionHeckeFunctor μG H μH).obj W where
  hom := ObjectProperty.homMk (closedForwardHom μG H μH W)
  inv := ObjectProperty.homMk (closedInverseHom μG H μH W)
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro f
    exact closedInverse_forward μG H μH W f
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro q
    exact closedForward_inverse μG H μH W q

/-- Postcomposition commutes with the integrated forward formula. -/
theorem closedComponent_naturality
    {W Z : Langlands.SmoothRep.{0, uG, v} ℂ H} (a : W ⟶ Z) :
    (inducedHeckeFunctor μG H).map a ≫ (closedComponentIso μG H μH Z).hom =
      (closedComponentIso μG H μH W).hom ≫ (homInductionHeckeFunctor μG H μH).map a := by
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro f
  apply Subtype.ext
  apply NonUnitalModuleHom.ext
  intro T
  have ht := integratedAction_intertwiner μG
    (Induction.smoothInduced_smooth H W.representation)
    (Induction.smoothInduced_smooth H Z.representation)
    (Induction.smoothInducedMap H (Langlands.SmoothRep.hom a))
    (HeckeAlgebra.toTestFunction μG T) f
  exact (congrArg (fun z => Induction.eval H Z.representation z 1) ht).symm

/-- The natural comparison between the two actual induction functors. -/
def closedComparisonIso : inducedHeckeFunctor.{uG, v} μG H ≅
    homInductionHeckeFunctor.{uG, v} μG H μH :=
  NatIso.ofComponents (closedComponentIso μG H μH)
    (fun a => closedComponent_naturality μG H μH a)

/-- Renard (III.2.5.1)–(III.2.5.5), for the published actual functors in all universes. -/
theorem closedInductionHom : ClosedInductionHomStatement.{uG, v} := by
  intro G _ _ _ _ _ _ _ μG _ H hH
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  intro μH _
  refine ⟨closedComparisonIso μG H μH, ?_, ?_, ?_, ?_⟩
  · intro W f T
    rfl
  · exact homInduction_exists_localUnit μG H μH
  · exact closedInverse_formula μG H μH
  · exact leftModule_translated_localUnit μG H μH

end Langlands.Hecke.Homomorphism
