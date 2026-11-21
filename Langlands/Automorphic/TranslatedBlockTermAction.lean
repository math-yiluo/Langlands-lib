import Langlands.Automorphic.TranslatedBlockConstantTermOperators
import Langlands.Automorphic.BlockShapeLeviSlices
import Langlands.Representation.Smooth.SmoothPart.Definitions
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Automorphic.CompactDerivativeTransfer

/-! # Evaluation and compact differentiation of translated block periods -/

noncomputable section

universe u

open NumberField
open scoped Classical

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GeneralLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : OperatorRealization F n)

local instance translatedTermActionRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedTermActionContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedTermActionFiniteSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedTermActionFormsAddCommGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance translatedTermActionStableAddCommGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedTermActionRealizationAddCommGroup : AddCommGroup S.Space := Submodule.addCommGroup _

local notation "G" => AdelicGL F n
local notation "Cen" => (Fin B.length → Ideles F)
local notation "U" => automorphicOperatorAlgebra F n
local notation "T" => TranslatedBlockConstantTerms F B S
local notation "β" => blockConstantTermScalarAction F B
local notation "φ" => realizedBlockConstantTerm F B S
local notation "P" => LinearMap.ker (translatedFunctionSum β φ)
local notation "E" => translatedFunctionSum β φ
local notation "ev" => translatedFunctionEmbedding β φ
local notation "α" => translatedBlockTermOperatorAction F B S
local notation "Lemb" => B.leviEmbedding (Adeles F)

/-- Evaluate the original period after one block-centre translate, as a map for the full algebra. -/
def blockTermTranslationMap (z : Cen) : S.representation.IntertwiningMap (AlgHom.toMonoidHom' α) := by
  let : Ring U := Subalgebra.toRing U
  unfold translatedBlockTermOperatorAction
  refine translatedFunctionOperatorMap (R := U) β φ S.operatorAction ?_ z
  intro a v hv
  exact blockTermCoefficient_kernel_stable F B S a v hv

/-- The whole translated period space is spanned by the actual translates. -/
theorem blockTermTranslationMap_iSup_range :
    (⨆ z : Cen, (blockTermTranslationMap F B S z).toLinearMap.range) = ⊤ := by
  let : Ring U := Subalgebra.toRing U
  unfold blockTermTranslationMap
  exact translatedFunctionOperatorMap_iSup_range (R := U) β φ S.operatorAction _

theorem translatedBlockTermCenterAction_commute (z : Cen) (a : U) :
    Commute (translatedFunctionAction β φ z) (α a) := by
  let : Ring U := Subalgebra.toRing U
  unfold translatedBlockTermOperatorAction
  exact translatedFunctionOperatorAction_commute (R := U) β φ S.operatorAction _ z a

theorem translatedBlockTermOperatorAction_mkQ (a : U) (v : Cen →₀ S.Space) :
    α a ((P).mkQ v) = (P).mkQ (blockTermCoefficientAction F B S a v) := rfl

theorem translatedBlockTermEval_mkQ (v : Cen →₀ S.Space) :
    ev ((P).mkQ v) = E v := rfl

private theorem quotient_evaluate_action {A X : Type*} [AddCommGroup A] [Module ℂ A]
    (E₀ : A →ₗ[ℂ] (X → ℂ)) (D : Module.End ℂ A)
    (hD : LinearMap.ker E₀ ≤ (LinearMap.ker E₀).comap D) (s : X → X)
    (he : ∀ v x, E₀ (D v) x = E₀ v (s x)) (v : A ⧸ LinearMap.ker E₀) (x : X) :
    ((LinearMap.ker E₀).liftQ E₀ le_rfl)
      ((LinearMap.ker E₀).mapQ (LinearMap.ker E₀) D hD v) x =
        ((LinearMap.ker E₀).liftQ E₀ le_rfl) v (s x) := by
  obtain ⟨w, rfl⟩ := (LinearMap.ker E₀).mkQ_surjective v
  exact he w x

/-- The descended finite action agrees with actual right translation. -/
theorem translatedBlockTermEval_finite (d : FiniteAdelicGL F n) (v : T) (g : G) :
    ev (α (finiteOperator F n d) v) g = ev v (g * AdelicGL.ofFinite F n d) := by
  let D := blockTermCoefficientAction F B S (finiteOperator F n d)
  exact quotient_evaluate_action E D
    (fun w hw => blockTermCoefficient_kernel_stable F B S (finiteOperator F n d) w hw)
    (fun g => g * AdelicGL.ofFinite F n d) (blockTermCoefficient_finite F B S d) v g

/-- The descended compact action agrees with actual right translation. -/
theorem translatedBlockTermEval_compact (k : standardInfiniteCompact F n) (v : T) (g : G) :
    ev (α (compactOperator F n k) v) g = ev v (g * AdelicGL.ofInfinite F n k.val) := by
  let D := blockTermCoefficientAction F B S (compactOperator F n k)
  exact quotient_evaluate_action E D
    (fun w hw => blockTermCoefficient_kernel_stable F B S (compactOperator F n k) w hw)
    (fun g => g * AdelicGL.ofInfinite F n k.val) (blockTermCoefficient_compact F B S k) v g

set_option maxHeartbeats 350000 in
/-- The actual derivative of the represented function along an infinite right Lie curve. -/
theorem translatedBlockTermEval_hasDerivAt (X : RealLieAlgebra F n) (v : T) (g : G) (t : ℝ) :
    HasDerivAt (fun s => ev v (g * AdelicGL.ofInfinite F n (infiniteOneParameter F n X s)))
      (ev (α (differentialOperator F n (envelopingGenerator F n (complexify F n X))) v)
        (g * AdelicGL.ofInfinite F n (infiniteOneParameter F n X t))) t := by
  refine Submodule.Quotient.induction_on (P) v ?_
  exact fun u => hasDerivAt_blockTermCoefficient F B S X u g t

/-- The compact action of the actual translated period space. -/
def translatedBlockTermCompactAction : Representation ℂ (standardInfiniteCompact F n) T :=
  (AlgHom.toMonoidHom' α).comp (compactOperator F n)

/-- The complex Lie action of the actual translated period space. -/
def translatedBlockTermComplexLieAction : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ T :=
  (AlgHom.toLieHom ((α).comp (differentialOperator F n))).comp (UniversalEnvelopingAlgebra.ι ℂ)

local notation "κ" => translatedBlockTermCompactAction F B S
local notation "D" => translatedBlockTermComplexLieAction F B S

private def blockTermTranslationCompactMap (z : Cen) : S.compactRepresentation.IntertwiningMap κ where
  toLinearMap := (blockTermTranslationMap F B S z).toLinearMap
  isIntertwining' k := (blockTermTranslationMap F B S z).isIntertwining' (compactOperator F n k)

set_option maxHeartbeats 550000 in
/-- All represented translated periods are compact-finite for their original compact action. -/
theorem translatedBlockTerm_compactFinite (v : T) : FiniteVectors.IsFiniteVector κ v := by
  let V₀ := (FiniteVectors.subrepresentation κ).toSubmodule
  have hv : v ∈ (⨆ z : Cen, (blockTermTranslationMap F B S z).toLinearMap.range) := by
    exact (blockTermTranslationMap_iSup_range F B S).symm ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ T))
  have hle : (⨆ z : Cen, (blockTermTranslationMap F B S z).toLinearMap.range) ≤ V₀ := by
    refine iSup_le fun z _ hv => ?_
    obtain ⟨w, rfl⟩ := hv
    exact (S.compactRepresentation_isFiniteVector w).map (blockTermTranslationCompactMap F B S z)
  exact hle hv

/-- Compact curves differentiate to the actual descended complex Lie action. -/
theorem translatedBlockTerm_compactDualDerivative : CompactDualDerivative κ D := by
  refine CompactDualDerivative.of_spanning_ranges κ D
    (fun _ : Cen => S.compactRepresentation) (fun _ => S.complexLieAction)
    (fun _ => S.compactDualDerivative) (blockTermTranslationCompactMap F B S) ?_ ?_
  · intro z X f
    exact Representation.IntertwiningMap.isIntertwining _ _ (blockTermTranslationMap F B S z)
      (differentialOperator F n (envelopingGenerator F n X)) f
  · exact blockTermTranslationMap_iSup_range F B S

private theorem scalarTranslate_parabolic (z : Cen) (f : S.Space)
    (p : AdelicBlockParabolic.Full F B) (g : G) :
    β z (φ f) (p.val * g) = β z (φ f) (Lemb (B.leviProjection (Adeles F) p) * g) := by
  let s := B.leviInParabolic (Adeles F) (blockLeviScalars F B z)
  change blockShapeConstantTerm B F (S.ambient f) (s.val * (p.val * g)) =
    blockShapeConstantTerm B F (S.ambient f) (s.val * (Lemb (B.leviProjection (Adeles F) p) * g))
  rw [← mul_assoc s.val p.val g, ← Subgroup.coe_mul, blockShapeConstantTerm_parabolic_mul,
    map_mul, B.leviProjection_section]
  simp only [blockShapeLeviSlice, map_mul, mul_assoc, s, B.leviInParabolic_val]

private theorem quotient_evaluations_eq {A X : Type*} [AddCommGroup A] [Module ℂ A]
    (E₀ : A →ₗ[ℂ] (X → ℂ)) (x y : X) (he : ∀ w, E₀ w x = E₀ w y)
    (v : A ⧸ LinearMap.ker E₀) :
    ((LinearMap.ker E₀).liftQ E₀ le_rfl) v x =
      ((LinearMap.ker E₀).liftQ E₀ le_rfl) v y := by
  obtain ⟨w, rfl⟩ := (LinearMap.ker E₀).mkQ_surjective v
  exact he w

set_option maxHeartbeats 450000 in
/-- The actual block parabolic acts on the left through its Levi projection. -/
theorem translatedBlockTermEval_parabolic (v : T) (p : AdelicBlockParabolic.Full F B) (g : G) :
    ev v (p.val * g) = ev v (Lemb (B.leviProjection (Adeles F) p) * g) := by
  apply quotient_evaluations_eq E _ _ _ v
  intro w
  induction w using Finsupp.induction_linear with
  | zero => simp only [map_zero, Pi.zero_apply]
  | add a b ha hb =>
    rw [(E).map_add]
    exact congrArg₂ (· + ·) ha hb
  | single z f =>
    rw [translatedFunctionSum_single]
    exact scalarTranslate_parabolic F B S z f p g

set_option maxHeartbeats 450000 in
/-- The restriction to the Levi at all compact and finite transforms detects the entire quotient. -/
theorem translatedBlockTerm_zero_of_compact_finite_restrictions (v : T)
    (h : ∀ (k : standardInfiniteCompact F n) (d : FiniteAdelicGL F n),
      translatedBlockLeviRestriction F B S (α (compactOperator F n k) (α (finiteOperator F n d) v)) = 0) :
    v = 0 := by
  apply translatedFunctionEmbedding_injective β φ
  funext g
  change ev v g = 0
  obtain ⟨b, k, hg, hb, hk⟩ := PrimitiveAdelicHeight.exists_infinite_iwasawa F n (AdelicGL.infinite F n g)
  let p := AdelicBlockParabolic.pair F B ⟨b, B.mem_parabolic_of_isUpperTriangular b hb⟩ 1
  let d := AdelicGL.finite F n g
  let k' : standardInfiniteCompact F n := ⟨k, hk⟩
  let m := B.leviProjection (Adeles F) p
  let a := AdelicGL.ofInfinite F n k
  let b' := AdelicGL.ofFinite F n d
  have harg : g = p.val * (AdelicGL.ofInfinite F n k * AdelicGL.ofFinite F n d) := by
    change g = AdelicGL.pair F n b 1 * (AdelicGL.ofInfinite F n k * AdelicGL.ofFinite F n d)
    simp only [AdelicGL.ofInfinite_eq_pair, AdelicGL.ofFinite_eq_pair, AdelicGL.pair_mul, mul_one, one_mul,
      ← hg, d, AdelicGL.pair_projections]
  calc
    ev v g = ev v (p.val * (a * b')) := congrArg (ev v) harg
    _ = ev v (Lemb m * (a * b')) := translatedBlockTermEval_parabolic F B S v p _
    _ = ev v ((Lemb m * a) * b') := congrArg (ev v) (mul_assoc _ _ _).symm
    _ = ev (α (finiteOperator F n d) v) (Lemb m * a) :=
      (translatedBlockTermEval_finite F B S d v _).symm
    _ = ev (α (compactOperator F n k') (α (finiteOperator F n d) v)) (Lemb m) :=
      (translatedBlockTermEval_compact F B S k' _ _).symm
    _ = 0 := congrFun (h k' d) m

/-- The action of the actual ambient finite adelic group on the period quotient. -/
def translatedBlockTermFiniteAction : Representation ℂ (FiniteAdelicGL F n) T :=
  (AlgHom.toMonoidHom' α).comp (finiteOperator F n)

local notation "ρ" => translatedBlockTermFiniteAction F B S

set_option maxHeartbeats 1400000 in
/-- The finite right action on translated periods is smooth. -/
theorem translatedBlockTerm_finiteSmooth : IsSmooth ρ := by
  let W := smoothVectors ρ
  intro v
  have hv : v ∈ (⨆ z : Cen, (blockTermTranslationMap F B S z).toLinearMap.range) :=
    (blockTermTranslationMap_iSup_range F B S).symm ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ T))
  refine (iSup_le (fun z => ?_) : (⨆ z : Cen, (blockTermTranslationMap F B S z).toLinearMap.range) ≤ W) hv
  intro w hw
  obtain ⟨f, rfl⟩ := hw
  let g : S.finiteRepresentation.IntertwiningMap ρ :=
    { toLinearMap := (blockTermTranslationMap F B S z).toLinearMap
      isIntertwining' := fun d => (blockTermTranslationMap F B S z).isIntertwining' (finiteOperator F n d) }
  exact isSmoothVector_map g (S.finiteRepresentation_isSmooth f)

end Langlands.Automorphic
