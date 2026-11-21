import Langlands.Automorphic.BlockConstantTermScalarAction
import Langlands.Automorphic.GeneralLinearBlockConstantTermOperator
import Langlands.Automorphic.TranslatedFunctionSpan
import Langlands.Automorphic.OperatorEquivalence
import Langlands.Representation.Archimedean.RealGKInfinitesimalCharacter

/-! # The actual operator action on sums of block-centre translates of constant terms -/

noncomputable section

universe u

open NumberField
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

section SingleTranslate

variable {R A V X : Type*} [Ring R] [Algebra ℂ R] [Monoid A] [AddCommGroup V] [Module ℂ V]
  (β₀ : Representation ℂ A (X → ℂ)) (φ₀ : V →ₗ[ℂ] (X → ℂ))
  (ρ₀ : R →ₐ[ℂ] Module.End ℂ V)
  (h₀ : ∀ a v, v ∈ LinearMap.ker (translatedFunctionSum β₀ φ₀) →
    finsuppCoefficientEnd A V (ρ₀ a) v ∈ LinearMap.ker (translatedFunctionSum β₀ φ₀))

/-- Take a specified translated function as an intertwiner from the original coefficient action. -/
def translatedFunctionOperatorMap (z : A) :
    Representation.IntertwiningMap ρ₀.toMonoidHom
      (translatedFunctionOperatorAction β₀ φ₀ ρ₀ h₀).toMonoidHom where
  toLinearMap := (LinearMap.ker (translatedFunctionSum β₀ φ₀)).mkQ.comp (Finsupp.lsingle z)
  isIntertwining' a := LinearMap.ext fun f => by
    let P₀ := LinearMap.ker (translatedFunctionSum β₀ φ₀)
    change P₀.mkQ (Finsupp.single z (ρ₀ a f)) =
      P₀.mkQ (finsuppCoefficientEnd A V (ρ₀ a) (Finsupp.single z f))
    rw [finsuppCoefficientEnd_single]

theorem translatedFunctionOperatorMap_iSup_range :
    (⨆ z : A, (translatedFunctionOperatorMap β₀ φ₀ ρ₀ h₀ z).toLinearMap.range) = ⊤ := by
  let T := ⨆ z : A, (translatedFunctionOperatorMap β₀ φ₀ ρ₀ h₀ z).toLinearMap.range
  let P₀ := LinearMap.ker (translatedFunctionSum β₀ φ₀)
  apply top_unique
  intro v _
  refine Submodule.Quotient.induction_on P₀ v ?_
  intro w
  change P₀.mkQ w ∈ T
  induction w using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact T.zero_mem
  | add a b ha hb => rw [map_add]; exact T.add_mem ha hb
  | single z f =>
    exact Submodule.mem_iSup_of_mem z (LinearMap.mem_range_self (translatedFunctionOperatorMap β₀ φ₀ ρ₀ h₀ z).toLinearMap f)

end SingleTranslate

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GeneralLinear
  Global.RankinSelbergGlobal.WhittakerCurve

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : OperatorRealization F n)

local instance translatedBlockTermRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedBlockTermContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedBlockTermFiniteSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedBlockTermFormsAddCommGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance translatedBlockTermStableAddCommGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedBlockTermRealizationAddCommGroup : AddCommGroup S.Space := Submodule.addCommGroup _

local notation "G" => AdelicGL F n
local notation "Cen" => (Fin B.length → Ideles F)
local notation "U" => automorphicOperatorAlgebra F n
local notation "V" => FiniteSmoothRationalFunctions F n
local notation "H" => (AdelicGL F n → ℂ)
local notation "β" => blockConstantTermScalarAction F B

/-- Take the actual matrix constant term of a realized form. -/
def realizedBlockConstantTerm : S.Space →ₗ[ℂ] H :=
  (blockShapeConstantTermLinear F B).comp
    ((automorphicSubrepresentation F n).toSubmodule.subtype.comp S.formInclusion.toLinearMap)

local notation "φ" => realizedBlockConstantTerm F B S
local notation "E" => translatedFunctionSum β φ
local notation "P" => LinearMap.ker (translatedFunctionSum β φ)

/-- The coefficient action of the original automorphic operator algebra. -/
def blockTermCoefficientAction : U →ₐ[ℂ] Module.End ℂ (Cen →₀ S.Space) :=
  (finsuppCoefficientEnd Cen S.Space).comp S.operatorAction

local notation "ρ" => blockTermCoefficientAction F B S

/-- The matrix-coordinate formula for the derivative of the normalized block period. -/
theorem blockShapeConstantTerm_hasDerivAt (X : RealLieAlgebra F n) (f : V) (g : G) (t : ℝ) :
    HasDerivAt (fun s => blockShapeConstantTerm B F f
      (g * AdelicGL.ofInfinite F n (infiniteOneParameter F n X s)))
      (blockShapeConstantTerm B F
        (finiteSmoothEnvelopingAction F n (envelopingGenerator F n (complexify F n X)) f)
        (g * AdelicGL.ofInfinite F n (infiniteOneParameter F n X t))) t := by
  let e := GeneralLinearGroupPoints.adelicEquiv F n
  have he (s : ℝ) : e.symm (g * AdelicGL.ofInfinite F n (infiniteOneParameter F n X s)) =
      e.symm g * adelicOneParameter F n X s := e.symm.map_mul _ _
  change HasDerivAt (fun s => finiteSmoothBlockConstantTerm F (standardBlockWeight B.cuts) f
      (e.symm (g * AdelicGL.ofInfinite F n (infiniteOneParameter F n X s))))
    (finiteSmoothBlockConstantTerm F (standardBlockWeight B.cuts)
      (finiteSmoothEnvelopingAction F n (envelopingGenerator F n (complexify F n X)) f)
      (e.symm (g * AdelicGL.ofInfinite F n (infiniteOneParameter F n X t)))) t
  simp only [he]
  exact finiteSmoothBlockConstantTerm_hasDerivAt F (standardBlockWeight B.cuts) X f (e.symm g) t

set_option maxHeartbeats 450000 in
private theorem blockTermCoefficient_rightAction (a : U) (h : G)
    (ha : ∀ f, S.ambient (S.operatorAction a f) = finiteSmoothRightAction F n h (S.ambient f))
    (v : Cen →₀ S.Space) (g : G) : E (ρ a v) g = E v (g * h) := by
  let L (x : G) : H →ₗ[ℂ] ℂ := LinearMap.proj x
  have he : (L g).comp ((E).comp (ρ a)) = (L (g * h)).comp E := by
    apply Finsupp.lhom_ext
    intro z f
    change E (finsuppCoefficientEnd Cen S.Space (S.operatorAction a) (Finsupp.single z f)) g = _
    rw [finsuppCoefficientEnd_single]
    simp only [LinearMap.comp_apply, L, LinearMap.proj_apply, translatedFunctionSum_single,
      blockConstantTermScalarAction_apply]
    let s := B.leviEmbedding (Adeles F) (blockLeviScalars F B z)
    change blockShapeConstantTerm B F (S.ambient (S.operatorAction a f)) (s * g) =
      blockShapeConstantTerm B F (S.ambient f) (s * (g * h))
    rw [ha, blockShapeConstantTerm_rightAction, mul_assoc]
  exact LinearMap.congr_fun he v

/-- Finite translation of a sum is right translation of the represented function. -/
theorem blockTermCoefficient_finite (d : FiniteAdelicGL F n) (v : Cen →₀ S.Space) (g : G) :
    E (ρ (finiteOperator F n d) v) g = E v (g * AdelicGL.ofFinite F n d) :=
  blockTermCoefficient_rightAction F B S _ _ (fun _ => rfl) v g

/-- Compact translation of a sum is right translation of the represented function. -/
theorem blockTermCoefficient_compact (k : standardInfiniteCompact F n) (v : Cen →₀ S.Space) (g : G) :
    E (ρ (compactOperator F n k) v) g = E v (g * AdelicGL.ofInfinite F n k.val) :=
  blockTermCoefficient_rightAction F B S _ _ (fun _ => rfl) v g

set_option maxHeartbeats 550000 in
/-- The actual derivative along each right Lie curve acts coefficientwise on the sum. -/
theorem hasDerivAt_blockTermCoefficient (X : RealLieAlgebra F n) (v : Cen →₀ S.Space)
    (g : G) (t : ℝ) :
    HasDerivAt (fun s => E v (g * AdelicGL.ofInfinite F n (infiniteOneParameter F n X s)))
      (E (ρ (differentialOperator F n (envelopingGenerator F n (complexify F n X))) v)
        (g * AdelicGL.ofInfinite F n (infiniteOneParameter F n X t))) t := by
  induction v using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero, Pi.zero_apply]
    exact hasDerivAt_const t 0
  | add a b ha hb =>
    simp only [map_add, Pi.add_apply]
    exact ha.add hb
  | single z f =>
    change HasDerivAt (fun s => E (Finsupp.single z f)
        (g * AdelicGL.ofInfinite F n (infiniteOneParameter F n X s)))
      (E (finsuppCoefficientEnd Cen S.Space (S.envelopingAction _) (Finsupp.single z f))
        (g * AdelicGL.ofInfinite F n (infiniteOneParameter F n X t))) t
    rw [finsuppCoefficientEnd_single]
    simp only [translatedFunctionSum_single, blockConstantTermScalarAction_apply]
    let p := B.leviEmbedding (Adeles F) (blockLeviScalars F B z)
    change HasDerivAt (fun s => blockShapeConstantTerm B F (S.ambient f)
      (p * (g * AdelicGL.ofInfinite F n (infiniteOneParameter F n X s))))
      (blockShapeConstantTerm B F (S.ambient (S.envelopingAction _ f))
        (p * (g * AdelicGL.ofInfinite F n (infiniteOneParameter F n X t)))) t
    simp only [S.ambient_envelopingAction, ← mul_assoc]
    exact blockShapeConstantTerm_hasDerivAt F B X (S.ambient f) (p * g) t

private theorem derivative_mem_ker {Y W : Type*} [AddCommGroup W] [Module ℂ W]
    (E₀ : W →ₗ[ℂ] (Y → ℂ)) (D : Module.End ℂ W) (c : Y → ℝ → Y)
    (hzero : ∀ g, c g 0 = g) (v : W) (hv : v ∈ LinearMap.ker E₀)
    (hd : ∀ g, HasDerivAt (fun t => E₀ v (c g t)) (E₀ (D v) (c g 0)) 0) :
    D v ∈ LinearMap.ker E₀ := by
  apply LinearMap.mem_ker.mpr
  funext g
  have h := hd g
  rw [LinearMap.mem_ker.mp hv, hzero g] at h
  exact h.unique (hasDerivAt_const 0 (0 : ℂ))

set_option maxHeartbeats 650000 in
private theorem blockTermCoefficient_realGenerator_mem (X : RealLieAlgebra F n)
    (v : Cen →₀ S.Space) (hv : v ∈ P) :
    ρ (differentialOperator F n (envelopingGenerator F n (complexify F n X))) v ∈ P := by
  let c (g : G) (t : ℝ) := g * AdelicGL.ofInfinite F n (infiniteOneParameter F n X t)
  apply derivative_mem_ker E (ρ (differentialOperator F n (envelopingGenerator F n (complexify F n X))))
    c (fun g => by simp only [c, infiniteOneParameter_zero, map_one, mul_one]) v hv
  intro g
  exact hasDerivAt_blockTermCoefficient F B S X v g 0

omit [NumberField F] in
private theorem envelopingAction_stable_of_real {W : Type*} [AddCommGroup W] [Module ℂ W]
    (D : EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ W) (T : Submodule ℂ W)
    (hreal : ∀ (X : RealLieAlgebra F n) v, v ∈ T →
      D (envelopingGenerator F n (complexify F n X)) v ∈ T) (a : EnvelopingAlgebra F n) :
    ∀ v ∈ T, D a v ∈ T := by
  have hgen (X : ComplexLieAlgebra F n) : ∀ v ∈ T, D (envelopingGenerator F n X) v ∈ T := by
    induction X using TensorProduct.inductionOn with
    | tmul c X =>
      intro v hv
      have h : c ⊗ₜ[ℝ] X = c • complexify F n X := by
        simp only [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h, map_smul (envelopingGenerator F n), map_smul D, LinearMap.smul_apply]
      exact T.smul_mem c (hreal X v hv)
    | add X Y hX hY =>
      intro v hv
      rw [map_add (envelopingGenerator F n), map_add D, LinearMap.add_apply]
      exact T.add_mem (hX v hv) (hY v hv)
  induction a using Langlands.Archimedean.InfinitesimalCharacter.envInduction with
  | algebraMap c =>
    intro v hv
    rw [D.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact T.smul_mem c hv
  | «ι» X => exact hgen X
  | mul a b ha hb =>
    intro v hv
    rw [map_mul, Module.End.mul_apply]
    exact ha _ (hb _ hv)
  | add a b ha hb =>
    intro v hv
    rw [map_add, LinearMap.add_apply]
    exact T.add_mem (ha _ hv) (hb _ hv)

private theorem blockTermCoefficient_differential_mem (a : EnvelopingAlgebra F n)
    (v : Cen →₀ S.Space) (hv : v ∈ P) : ρ (differentialOperator F n a) v ∈ P :=
  envelopingAction_stable_of_real F ((ρ).comp (differentialOperator F n)) P
    (blockTermCoefficient_realGenerator_mem F B S) a v hv

private theorem action_stable_of_adjoin {D W : Type*} [Ring D] [Algebra ℂ D] [AddCommGroup W] [Module ℂ W]
    (s : Set D) (R : Algebra.adjoin ℂ s →ₐ[ℂ] Module.End ℂ W) (T : Submodule ℂ W)
    (h : ∀ d (hd : d ∈ s) v, v ∈ T → R ⟨d, Algebra.subset_adjoin hd⟩ v ∈ T)
    (a : Algebra.adjoin ℂ s) : ∀ v ∈ T, R a v ∈ T := by
  refine Algebra.adjoin_induction (p := fun a ha => ∀ v ∈ T, R ⟨a, ha⟩ v ∈ T) h ?_ ?_ ?_ a.property
  · intro c v hv
    change R (algebraMap ℂ (Algebra.adjoin ℂ s) c) v ∈ T
    rw [R.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact T.smul_mem c hv
  · intro a b ha hb hA hB v hv
    change R (⟨a, ha⟩ + ⟨b, hb⟩) v ∈ T
    rw [map_add, LinearMap.add_apply]
    exact T.add_mem (hA _ hv) (hB _ hv)
  · intro a b ha hb hA hB v hv
    change R (⟨a, ha⟩ * ⟨b, hb⟩) v ∈ T
    rw [map_mul, Module.End.mul_apply]
    exact hA _ (hB _ hv)

set_option maxHeartbeats 450000 in
/-- The kernel of full translated-period evaluation is stable under every original operator. -/
theorem blockTermCoefficient_kernel_stable (a : U) (v : Cen →₀ S.Space) (hv : v ∈ P) :
    ρ a v ∈ P := by
  refine action_stable_of_adjoin (automorphicOperatorGenerators F n) (ρ) P ?_ a v hv
  rintro a ((⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨w, rfl⟩) h hh
  · apply LinearMap.mem_ker.mpr
    funext g
    have hz : E h = 0 := hh
    exact (blockTermCoefficient_finite F B S d h g).trans (congrFun hz _)
  · apply LinearMap.mem_ker.mpr
    funext g
    have hz : E h = 0 := hh
    exact (blockTermCoefficient_compact F B S k h g).trans (congrFun hz _)
  · exact blockTermCoefficient_differential_mem F B S w h hh

/-- The actual span of translated constant terms, with the full original algebra action. -/
abbrev TranslatedBlockConstantTerms := TranslatedFunctionSpan β φ

set_option maxHeartbeats 950000 in
/-- Coefficient operators descend to the actual translated constant-term space. -/
def translatedBlockTermOperatorAction : U →ₐ[ℂ] Module.End ℂ (TranslatedBlockConstantTerms F B S) := by
  refine translatedFunctionOperatorAction (R := U) β φ S.operatorAction ?_
  intro a v hv
  change ρ a v ∈ P
  exact blockTermCoefficient_kernel_stable F B S a v hv

local notation "ev" => translatedFunctionEmbedding β φ
local notation "M" => AdelicBlockParabolic.FullLevi F B
local notation "Lemb" => B.leviEmbedding (Adeles F)

/-- Restrict the represented translated period to the actual Levi at ambient argument one. -/
def translatedBlockLeviRestriction : TranslatedBlockConstantTerms F B S →ₗ[ℂ] (M → ℂ) where
  toFun v m := ev v (Lemb m)
  map_add' v w := funext fun m => congrFun ((ev).map_add v w) (Lemb m)
  map_smul' c v := funext fun m => congrFun ((ev).map_smul c v) (Lemb m)

end Langlands.Automorphic
