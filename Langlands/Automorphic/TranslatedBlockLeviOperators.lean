import Langlands.Automorphic.TranslatedBlockTermAction
import Langlands.Automorphic.TranslatedBlockLeviSlices
import Langlands.Automorphic.BlockShapeRealPeriodLie
import Langlands.Representation.Smooth.SmoothPart.Definitions
import Langlands.Representation.Smooth.Transfer.SubquotientProof

/-! # Actions on the block slices of translated periods -/

noncomputable section

universe u

open NumberField
open scoped Classical

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GeneralLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : OperatorRealization F n)

local instance leviOperatorsRationalGroup (d : ℕ) : AddCommGroup (RationalInvariantFunctions F d) :=
  Submodule.addCommGroup _
local instance leviOperatorsContinuousGroup (d : ℕ) : AddCommGroup (ContinuousRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance leviOperatorsFiniteSmoothGroup (d : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance leviOperatorsFormGroup : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance leviOperatorsStableGroup : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance leviOperatorsRealizationGroup : AddCommGroup S.Space := Submodule.addCommGroup _

local notation "M" => AdelicBlockParabolic.FullLevi F B
local notation "Cen" => (Fin B.length → Ideles F)
local notation "T" => TranslatedBlockConstantTerms F B S
local notation "β" => blockConstantTermScalarAction F B
local notation "φ" => realizedBlockConstantTerm F B S
local notation "ev" => translatedFunctionEmbedding β φ
local notation "α" => translatedBlockTermOperatorAction F B S
local notation "Q" => translatedBlockLeviRestriction F B S
local notation "Lemb" => B.leviEmbedding (Adeles F)
local notation "ρ" => translatedBlockTermFiniteAction F B S

/-- An actual one-block finite group, included continuously in the ambient finite group. -/
def blockShapeFiniteBlockEmbedding (i : Fin B.length) :
    FiniteAdelicGL F (B.size i) →ₜ* FiniteAdelicGL F n where
  toMonoidHom := blockShapeSingleEmbedding B (FiniteAdeles F) i
  continuous_toFun := (B.leviEmbeddingContinuous (FiniteAdeles F)).continuous.comp
    (continuous_mulSingle (A := fun j => FiniteAdelicGL F (B.size j)) i)

/-- A one-block Levi finite translate is the associated finite translate in the ambient group. -/
theorem blockShapeLeviEmbedding_singleFinite (i : Fin B.length) (d : FiniteAdelicGL F (B.size i)) :
    Lemb (Pi.mulSingle i (AdelicGL.ofFinite F (B.size i) d)) =
      AdelicGL.ofFinite F n (blockShapeFiniteBlockEmbedding F B i d) := by
  let a : M := Pi.mulSingle i (AdelicGL.ofFinite F (B.size i) d)
  have hInf : AdelicBlockParabolic.leviInfinite F B a = 1 := by
    funext j
    change AdelicGL.infinite F (B.size j) (a j) = _
    by_cases hj : j = i
    · subst j
      simp only [a, Pi.mulSingle_eq_same, AdelicGL.infinite_ofFinite, Pi.one_apply]
    · simp only [a, Pi.mulSingle_eq_of_ne hj, map_one, Pi.one_apply]
  have hFin : AdelicBlockParabolic.leviFinite F B a = Pi.mulSingle i d := by
    funext j
    change AdelicGL.finite F (B.size j) (a j) = _
    by_cases hj : j = i
    · subst j
      simp only [a, Pi.mulSingle_eq_same, AdelicGL.finite_ofFinite]
    · simp only [a, Pi.mulSingle_eq_of_ne hj, map_one]
  have hi := congrArg Subtype.val (AdelicBlockParabolic.infinite_leviInParabolic F B a)
  have hf := congrArg Subtype.val (AdelicBlockParabolic.finite_leviInParabolic F B a)
  apply AdelicGL.ext_infinite_finite F n
  · change AdelicGL.infinite F n (Lemb a) = _
    rw [show AdelicGL.infinite F n (Lemb a) =
      B.leviEmbedding (InfiniteAdeles F) (AdelicBlockParabolic.leviInfinite F B a) from hi,
      hInf, map_one, AdelicGL.infinite_ofFinite]
  · change AdelicGL.finite F n (Lemb a) = _
    rw [show AdelicGL.finite F n (Lemb a) =
      B.leviEmbedding (FiniteAdeles F) (AdelicBlockParabolic.leviFinite F B a) from hf,
      hFin, AdelicGL.finite_ofFinite]
    rfl

set_option maxHeartbeats 650000 in
/-- Finite parabolic covariance of the actual unnormalized Levi coefficient. -/
theorem translatedBlockLeviRestriction_finiteParabolic
    (p : AdelicBlockParabolic.Finite F B) (v : T) (m : M) :
    Q (ρ p.val v) m = Q v
      (m * fun i => AdelicGL.ofFinite F (B.size i) (B.leviProjection (FiniteAdeles F) p i)) := by
  let P := AdelicBlockParabolic.pair F B 1 p
  let R := B.leviInParabolic (Adeles F) m * P
  have hw : B.leviProjection (Adeles F) R =
      m * fun i => AdelicGL.ofFinite F (B.size i) (B.leviProjection (FiniteAdeles F) p i) := by
    change B.leviProjection (Adeles F) (B.leviInParabolic (Adeles F) m *
      AdelicBlockParabolic.pair F B 1 p) = _
    rw [map_mul, B.leviProjection_section, AdelicBlockParabolic.leviProjection_pair, map_one]
    rfl
  calc
    _ = ev v (Lemb m * AdelicGL.ofFinite F n p.val) :=
      translatedBlockTermEval_finite F B S p.val v (Lemb m)
    _ = ev v (R.val * 1) := (congrArg (ev v) (mul_one _)).symm
    _ = ev v (Lemb (B.leviProjection (Adeles F) R) * 1) :=
      translatedBlockTermEval_parabolic F B S v R 1
    _ = _ := congrArg (ev v) ((mul_one _).trans (congrArg Lemb hw))

variable (i : Fin B.length)

local notation "d" => B.size i
local notation "e" => finiteSmoothFunctionEvaluation F d
local notation "slice" => translatedBlockLeviSlice F B S i

set_option maxHeartbeats 650000 in
/-- The finite action on an individual actual block slice is the corresponding ambient action. -/
theorem translatedBlockLeviSlice_finite (m : M) (a : FiniteAdelicGL F d) (v : T) :
    slice m (ρ (blockShapeFiniteBlockEmbedding F B i a) v) =
      finiteSmoothFiniteRightAction F d a (slice m v) := by
  apply finiteSmoothFunctionEvaluation_injective F d
  funext x
  let b := blockShapeFiniteBlockEmbedding F B i a
  let z := Function.update m i x
  let g := AdelicGL.ofFinite F d a
  have hz : Lemb (Function.update m i (x * g)) = Lemb z * AdelicGL.ofFinite F n b :=
    (congrArg Lemb (blockLevi_update_mulSingle F B i m x g)).trans
      (((Lemb).map_mul z (Pi.mulSingle i g)).trans
        (congrArg (Lemb z * ·) (blockShapeLeviEmbedding_singleFinite F B i a)))
  calc
    _ = ev (α (finiteOperator F n b) v) (Lemb z) :=
      translatedBlockLeviSlice_evaluation F B S i m _ x
    _ = ev v (Lemb z * AdelicGL.ofFinite F n b) :=
      translatedBlockTermEval_finite F B S b v (Lemb z)
    _ = ev v (Lemb (Function.update m i (x * g))) := congrArg (ev v) hz.symm
    _ = _ := (translatedBlockLeviSlice_evaluation F B S i m v (x * g)).symm

set_option maxHeartbeats 650000 in
/-- The compact action on a slice is the ambient action of the included block compact. -/
theorem translatedBlockLeviSlice_compact (m : M) (a : standardInfiniteCompact F d) (v : T) :
    slice m (α (compactOperator F n (blockShapeInfiniteCompactEmbedding B F i a)) v) =
      finiteSmoothCompactRightAction F d a (slice m v) := by
  apply finiteSmoothFunctionEvaluation_injective F d
  funext x
  let b := blockShapeInfiniteCompactEmbedding B F i a
  let z := Function.update m i x
  let g := AdelicGL.ofInfinite F d a.val
  have hz : Lemb (Function.update m i (x * g)) = Lemb z * AdelicGL.ofInfinite F n b.val :=
    (congrArg Lemb (blockLevi_update_mulSingle F B i m x g)).trans
      (((Lemb).map_mul z (Pi.mulSingle i g)).trans
        (congrArg (Lemb z * ·) (blockShapeLeviEmbedding_singleInfinite F B i a.val)))
  calc
    _ = ev (α (compactOperator F n b) v) (Lemb z) :=
      translatedBlockLeviSlice_evaluation F B S i m _ x
    _ = ev v (Lemb z * AdelicGL.ofInfinite F n b.val) :=
      translatedBlockTermEval_compact F B S b v (Lemb z)
    _ = ev v (Lemb (Function.update m i (x * g))) := congrArg (ev v) hz.symm
    _ = _ := (translatedBlockLeviSlice_evaluation F B S i m v (x * g)).symm

private theorem hasDerivAt_finiteSmoothEvaluation (a : ℕ) (X : RealLieAlgebra F a)
    (f : FiniteSmoothRationalFunctions F a) (x : AdelicGL F a) :
    HasDerivAt (fun t => finiteSmoothFunctionEvaluation F a f
      (x * AdelicGL.ofInfinite F a (infiniteOneParameter F a X t)))
      (finiteSmoothFunctionEvaluation F a
        (finiteSmoothEnvelopingAction F a (envelopingGenerator F a (complexify F a X)) f) x) 0 := by
  have h := hasDerivAt_smooth_oneParameter F a (finiteSmoothSlice F a (AdelicGL.finite F a x) f)
    X (AdelicGL.infinite F a x) 0
  simp only [infiniteOneParameter_zero, mul_one] at h
  rw [← envelopingAction_real_generator, ← finiteSmoothSlice_envelopingAction] at h
  simpa only [finiteSmoothFunctionEvaluation, LinearMap.coe_mk, AddHom.coe_mk, finiteSmoothSlice_apply,
    OperatorRealization.mul_ofInfinite_eq_pair, AdelicGL.pair_projections] using h

set_option maxHeartbeats 2200000 in
/-- A block real Lie generator differentiates its variable in the actual slice. -/
theorem translatedBlockLeviSlice_realGenerator (m : M) (X : RealLieAlgebra F d) (v : T) :
    slice m (α (differentialOperator F n (envelopingGenerator F n
      (complexify F n (blockShapeRealLieInclusion F B i X)))) v) =
      finiteSmoothEnvelopingAction F d (envelopingGenerator F d (complexify F d X)) (slice m v) := by
  apply finiteSmoothFunctionEvaluation_injective F d
  funext x
  let Y := blockShapeRealLieInclusion F B i X
  let z := Function.update m i x
  let g (t : ℝ) := AdelicGL.ofInfinite F d (infiniteOneParameter F d X t)
  have hz (t : ℝ) : Lemb (Function.update m i (x * g t)) =
      Lemb z * AdelicGL.ofInfinite F n (infiniteOneParameter F n Y t) :=
    (congrArg Lemb (blockLevi_update_mulSingle F B i m x (g t))).trans
      (((Lemb).map_mul z (Pi.mulSingle i (g t))).trans
        (congrArg (Lemb z * ·) ((blockShapeLeviEmbedding_singleInfinite F B i _).trans
          (congrArg (AdelicGL.ofInfinite F n)
            (infiniteOneParameter_blockShapeRealLieInclusion F B i X t).symm))))
  have h := translatedBlockTermEval_hasDerivAt F B S Y v (Lemb z) 0
  have hzero : Lemb z * AdelicGL.ofInfinite F n (infiniteOneParameter F n Y 0) = Lemb z :=
    (congrArg (fun a => Lemb z * AdelicGL.ofInfinite F n a) (infiniteOneParameter_zero F n Y)).trans
      ((congrArg (Lemb z * ·) (map_one (AdelicGL.ofInfinite F n))).trans (mul_one _))
  have hfun : (fun t => e (slice m v) (x * g t)) =
      fun t => ev v (Lemb z * AdelicGL.ofInfinite F n (infiniteOneParameter F n Y t)) := by
    funext t
    exact (translatedBlockLeviSlice_evaluation F B S i m v (x * g t)).trans (congrArg (ev v) (hz t))
  let w := α (differentialOperator F n (envelopingGenerator F n (complexify F n Y))) v
  have h' : HasDerivAt (fun t => e (slice m v) (x * g t)) (ev w (Lemb z)) 0 :=
    hfun.symm ▸ (congrArg (ev w) hzero ▸ h)
  exact (translatedBlockLeviSlice_evaluation F B S i m _ x).trans
    (h'.unique (hasDerivAt_finiteSmoothEvaluation F d X (slice m v) x))

set_option maxHeartbeats 1400000 in
/-- The actual Levi restriction of the radical Lie derivative vanishes. -/
theorem translatedBlockLeviRestriction_strictUpper (X : RealLieAlgebra F n)
    (hX : IsStrictUpperBlockLie F B X) (v : T) :
    Q (α (differentialOperator F n (envelopingGenerator F n (complexify F n X))) v) = 0 := by
  let E := translatedFunctionSum β φ
  let P := LinearMap.ker E
  let D := differentialOperator F n (envelopingGenerator F n (complexify F n X))
  refine Submodule.Quotient.induction_on (LinearMap.ker (translatedFunctionSum β φ)) v ?_
  intro w
  let H : (Cen →₀ S.Space) →ₗ[ℂ] (M → ℂ) :=
    (Q).comp (P.mkQ.comp (blockTermCoefficientAction F B S D))
  calc
    _ = H w := congrArg Q (translatedBlockTermOperatorAction_mkQ F B S D w)
    _ = 0 := ?_
  induction w using Finsupp.induction_linear with
  | zero => exact H.map_zero
  | add a b ha hb => rw [H.map_add, ha, hb, add_zero]
  | single z f =>
    funext m
    let G := fun u : Cen →₀ S.Space => E u (Lemb m)
    have h := blockLeviTermRestriction_strictUpperBlockLie F B X hX (S.ambient f)
    calc
      H (Finsupp.single z f) m = G (Finsupp.single z (S.operatorAction D f)) :=
        congrArg G (finsuppCoefficientEnd_single (S.operatorAction D) z f)
      _ = β z (φ (S.operatorAction D f)) (Lemb m) :=
        congrFun (translatedFunctionSum_single β φ z (S.operatorAction D f)) (Lemb m)
      _ = φ (S.operatorAction D f) (Lemb (blockLeviScalars F B z * m)) :=
        congrArg (φ (S.operatorAction D f)) ((Lemb).map_mul _ _).symm
      _ = 0 := by
        let a := Lemb (blockLeviScalars F B z * m)
        let g := finiteSmoothEnvelopingAction F n (envelopingGenerator F n (complexify F n X)) (S.ambient f)
        change blockShapeConstantTerm B F g a = 0
        have ha : blockShapeConstantTerm B F g (a * 1) = 0 :=
          congrFun h (blockLeviScalars F B z * m)
        exact (congrArg (blockShapeConstantTerm B F g) (mul_one a).symm).trans ha

end Langlands.Automorphic
