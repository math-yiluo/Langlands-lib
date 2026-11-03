import Langlands.Global.FunctionFieldAbsoluteValueCompletions
import Langlands.Global.CurvePlaceAdeleDiagonal

/-! # Function-field adeles over all real absolute-value places -/

noncomputable section

universe u

open Filter Topology
open scoped RestrictedProduct

namespace Langlands.Global

variable {F : Type u} [Field F]

/-- The actual absolute-value completion of a chosen representative of a place. -/
abbrev realAbsoluteValuePlaceCompletion (q : RealAbsoluteValuePlace (F := F)) :=
  q.out.val.Completion

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]

/-- The norm unit ball in the chosen absolute-value completion. -/
abbrev realAbsoluteValuePlaceCompletionIntegers (q : RealAbsoluteValuePlace (F := F)) :=
  absoluteValueCompletionIntegers q.out.val
    (finiteConstants_absoluteValue_isNonarchimedean k F q.out.val)

@[simp]
theorem mem_realAbsoluteValuePlaceCompletionIntegers
    (q : RealAbsoluteValuePlace (F := F)) (x : realAbsoluteValuePlaceCompletion q) :
    x ∈ realAbsoluteValuePlaceCompletionIntegers k F q ↔ ‖x‖ ≤ 1 :=
  mem_absoluteValueCompletionIntegers _ _ _

theorem isOpen_realAbsoluteValuePlaceCompletionIntegers
    (q : RealAbsoluteValuePlace (F := F)) :
    IsOpen (realAbsoluteValuePlaceCompletionIntegers k F q :
      Set (realAbsoluteValuePlaceCompletion q)) :=
  (Valued.isOpen_valuationSubring _).preimage
    (continuous_absoluteValueValuationCompletionEquiv q.out.val
      (finiteConstants_absoluteValue_isNonarchimedean k F q.out.val))

/-- The cofinite restricted product over the quotient of all nontrivial real
absolute values, with actual completions and their norm unit balls. -/
abbrev RealAbsoluteValueAdeleRing :=
  Πʳ q : RealAbsoluteValuePlace (F := F),
    [realAbsoluteValuePlaceCompletion q, realAbsoluteValuePlaceCompletionIntegers k F q]

instance : IsTopologicalRing (RealAbsoluteValueAdeleRing k F) := by
  have : Fact (∀ q : RealAbsoluteValuePlace (F := F),
      IsOpen (realAbsoluteValuePlaceCompletionIntegers k F q :
        Set (realAbsoluteValuePlaceCompletion q))) :=
    ⟨isOpen_realAbsoluteValuePlaceCompletionIntegers k F⟩
  exact RestrictedProduct.isTopologicalRing _

/-- The actual subring integral at every absolute-value place outside `S`. -/
def realAbsoluteValueAdeleLevel (S : Finset (RealAbsoluteValuePlace (F := F))) :
    Subring (RealAbsoluteValueAdeleRing k F) where
  carrier := {a | ∀ q, q ∉ S → a q ∈ realAbsoluteValuePlaceCompletionIntegers k F q}
  zero_mem' q _ := (realAbsoluteValuePlaceCompletionIntegers k F q).zero_mem
  one_mem' q _ := (realAbsoluteValuePlaceCompletionIntegers k F q).one_mem
  add_mem' ha hb q hq :=
    (realAbsoluteValuePlaceCompletionIntegers k F q).toSubring.add_mem (ha q hq) (hb q hq)
  mul_mem' ha hb q hq :=
    (realAbsoluteValuePlaceCompletionIntegers k F q).toSubring.mul_mem (ha q hq) (hb q hq)
  neg_mem' ha q hq :=
    (realAbsoluteValuePlaceCompletionIntegers k F q).toSubring.neg_mem (ha q hq)

@[simp]
theorem mem_realAbsoluteValueAdeleLevel (S : Finset (RealAbsoluteValuePlace (F := F)))
    (a : RealAbsoluteValueAdeleRing k F) :
    a ∈ realAbsoluteValueAdeleLevel k F S ↔
      ∀ q, q ∉ S → ‖a q‖ ≤ 1 := by
  change (∀ q, q ∉ S → a q ∈ realAbsoluteValuePlaceCompletionIntegers k F q) ↔ _
  simp only [mem_realAbsoluteValuePlaceCompletionIntegers]

theorem isOpen_realAbsoluteValueAdeleLevel (S : Finset (RealAbsoluteValuePlace (F := F))) :
    IsOpen (realAbsoluteValueAdeleLevel k F S : Set (RealAbsoluteValueAdeleRing k F)) :=
  RestrictedProduct.isOpen_forall_imp_mem
    (isOpen_realAbsoluteValuePlaceCompletionIntegers k F)

theorem realAbsoluteValueAdeleLevel_mono
    {S T : Finset (RealAbsoluteValuePlace (F := F))} (hST : S ⊆ T) :
    realAbsoluteValueAdeleLevel k F S ≤ realAbsoluteValueAdeleLevel k F T :=
  fun _ ha q hq => ha q (fun h => hq (hST h))

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

theorem functionFieldPlaceOfAbsoluteValue_out (q : RealAbsoluteValuePlace (F := F)) :
    functionFieldPlaceOfAbsoluteValue k F q.out =
      realAbsoluteValuePlaceCurvePlaceEquiv k F q :=
  congrArg (realAbsoluteValuePlaceCurvePlaceEquiv k F) (Quotient.out_eq q)

private def completionCast {v w : AlgebraicCurve.Place k F} (h : v = w) :
    curvePlaceCompletion v ≃+* curvePlaceCompletion w where
  toFun x := h ▸ x
  invFun x := h.symm ▸ x
  left_inv x := by subst w; rfl
  right_inv x := by subst w; rfl
  map_mul' x y := by subst w; rfl
  map_add' x y := by subst w; rfl

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] in
private theorem continuous_completionCast {v w : AlgebraicCurve.Place k F}
    (h : v = w) : Continuous (completionCast k F h) := by
  subst w
  exact continuous_id

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] in
private theorem continuous_completionCast_symm {v w : AlgebraicCurve.Place k F}
    (h : v = w) : Continuous (completionCast k F h).symm := by
  subst w
  exact continuous_id

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] in
private theorem completionCast_mem_iff {v w : AlgebraicCurve.Place k F}
    (h : v = w) (x : curvePlaceCompletion v) :
    completionCast k F h x ∈ curvePlaceCompletionIntegers w ↔
      x ∈ curvePlaceCompletionIntegers v := by
  subst w
  exact Iff.rfl

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] in
private theorem completionCast_algebraMap {v w : AlgebraicCurve.Place k F}
    (h : v = w) (x : F) :
    completionCast k F h (algebraMap F (curvePlaceCompletion v) x) =
      algebraMap F (curvePlaceCompletion w) x := by
  subst w
  rfl

/-- Compare a quotient place's actual absolute-value completion with its actual
curve-place completion. -/
def functionFieldAbsoluteValuePlaceCompletionEquiv
    (q : RealAbsoluteValuePlace (F := F)) :
    realAbsoluteValuePlaceCompletion q ≃+*
      curvePlaceCompletion (realAbsoluteValuePlaceCurvePlaceEquiv k F q) :=
  (functionFieldAbsoluteValueCompletionEquiv k F q.out).trans
    (completionCast k F (functionFieldPlaceOfAbsoluteValue_out k F q))

theorem continuous_functionFieldAbsoluteValuePlaceCompletionEquiv
    (q : RealAbsoluteValuePlace (F := F)) :
    Continuous (functionFieldAbsoluteValuePlaceCompletionEquiv k F q) :=
  (continuous_completionCast k F _).comp
    (continuous_functionFieldAbsoluteValueCompletionEquiv k F q.out)

theorem continuous_functionFieldAbsoluteValuePlaceCompletionEquiv_symm
    (q : RealAbsoluteValuePlace (F := F)) :
    Continuous (functionFieldAbsoluteValuePlaceCompletionEquiv k F q).symm :=
  (continuous_functionFieldAbsoluteValueCompletionEquiv_symm k F q.out).comp
    (continuous_completionCast_symm k F _)

theorem functionFieldAbsoluteValuePlaceCompletionEquiv_mem_iff
    (q : RealAbsoluteValuePlace (F := F)) (x : realAbsoluteValuePlaceCompletion q) :
    functionFieldAbsoluteValuePlaceCompletionEquiv k F q x ∈
      curvePlaceCompletionIntegers (realAbsoluteValuePlaceCurvePlaceEquiv k F q) ↔
        x ∈ realAbsoluteValuePlaceCompletionIntegers k F q := by
  change completionCast k F _ (functionFieldAbsoluteValueCompletionEquiv k F q.out x) ∈
    curvePlaceCompletionIntegers _ ↔ _
  rw [completionCast_mem_iff,
    functionFieldAbsoluteValueCompletionEquiv_mem_integers_iff,
    mem_realAbsoluteValuePlaceCompletionIntegers]

theorem functionFieldAbsoluteValuePlaceCompletionEquiv_coe
    (q : RealAbsoluteValuePlace (F := F)) (x : F) :
    functionFieldAbsoluteValuePlaceCompletionEquiv k F q
      ((WithAbs.toAbs q.out.val x : WithAbs q.out.val) :
        realAbsoluteValuePlaceCompletion q) =
      algebraMap F (curvePlaceCompletion (realAbsoluteValuePlaceCurvePlaceEquiv k F q)) x := by
  change completionCast k F _ (functionFieldAbsoluteValueCompletionEquiv k F q.out _) = _
  rw [functionFieldAbsoluteValueCompletionEquiv_coe, completionCast_algebraMap]

private theorem eventually_cofinite_equiv {ι κ : Type*} (e : ι ≃ κ) (P : κ → Prop) :
    (∀ᶠ i in cofinite, P (e i)) ↔ ∀ᶠ j in cofinite, P j := by
  constructor
  · intro h
    simpa only [e.apply_symm_apply] using e.symm.injective.tendsto_cofinite.eventually h
  · exact e.injective.tendsto_cofinite.eventually

private def absoluteValuePlacePiEquiv :
    (∀ q : RealAbsoluteValuePlace (F := F), realAbsoluteValuePlaceCompletion q) ≃
      (∀ v : AlgebraicCurve.Place k F, curvePlaceCompletion v) :=
  Equiv.piCongr (realAbsoluteValuePlaceCurvePlaceEquiv k F)
    (fun q => (functionFieldAbsoluteValuePlaceCompletionEquiv k F q).toEquiv)

private theorem absoluteValuePlacePiEquiv_integral_iff
    (x : ∀ q : RealAbsoluteValuePlace (F := F), realAbsoluteValuePlaceCompletion q) :
    (∀ᶠ q in cofinite, x q ∈ realAbsoluteValuePlaceCompletionIntegers k F q) ↔
      ∀ᶠ v in cofinite, absoluteValuePlacePiEquiv k F x v ∈
        curvePlaceCompletionIntegers v := by
  rw [← eventually_cofinite_equiv (realAbsoluteValuePlaceCurvePlaceEquiv k F)]
  apply Filter.eventually_congr
  apply Filter.Eventually.of_forall
  intro q
  rw [absoluteValuePlacePiEquiv, Equiv.piCongr_apply_apply]
  exact (functionFieldAbsoluteValuePlaceCompletionEquiv_mem_iff k F q (x q)).symm

private def absoluteValuePlaceRestrictedEquiv :
    RealAbsoluteValueAdeleRing k F ≃ CurvePlaceAdeleRing k F :=
  (absoluteValuePlacePiEquiv k F).subtypeEquiv
    (absoluteValuePlacePiEquiv_integral_iff k F)

/-- The actual absolute-value-place and curve-place restricted products are
ring equivalent. -/
def functionFieldAbsoluteValueAdeleEquiv :
    RealAbsoluteValueAdeleRing k F ≃+* CurvePlaceAdeleRing k F where
  __ := absoluteValuePlaceRestrictedEquiv k F
  map_mul' a b := by
    apply RestrictedProduct.ext
    intro v
    obtain ⟨q, rfl⟩ := (realAbsoluteValuePlaceCurvePlaceEquiv k F).surjective v
    change absoluteValuePlacePiEquiv k F (a * b).val
        (realAbsoluteValuePlaceCurvePlaceEquiv k F q) =
      absoluteValuePlacePiEquiv k F a.val (realAbsoluteValuePlaceCurvePlaceEquiv k F q) *
        absoluteValuePlacePiEquiv k F b.val (realAbsoluteValuePlaceCurvePlaceEquiv k F q)
    simp only [absoluteValuePlacePiEquiv, Equiv.piCongr_apply_apply]
    exact (functionFieldAbsoluteValuePlaceCompletionEquiv k F q).map_mul (a q) (b q)
  map_add' a b := by
    apply RestrictedProduct.ext
    intro v
    obtain ⟨q, rfl⟩ := (realAbsoluteValuePlaceCurvePlaceEquiv k F).surjective v
    change absoluteValuePlacePiEquiv k F (a + b).val
        (realAbsoluteValuePlaceCurvePlaceEquiv k F q) =
      absoluteValuePlacePiEquiv k F a.val (realAbsoluteValuePlaceCurvePlaceEquiv k F q) +
        absoluteValuePlacePiEquiv k F b.val (realAbsoluteValuePlaceCurvePlaceEquiv k F q)
    simp only [absoluteValuePlacePiEquiv, Equiv.piCongr_apply_apply]
    exact (functionFieldAbsoluteValuePlaceCompletionEquiv k F q).map_add (a q) (b q)

theorem functionFieldAbsoluteValueAdeleEquiv_apply (a : RealAbsoluteValueAdeleRing k F)
    (q : RealAbsoluteValuePlace (F := F)) :
    functionFieldAbsoluteValueAdeleEquiv k F a (realAbsoluteValuePlaceCurvePlaceEquiv k F q) =
      functionFieldAbsoluteValuePlaceCompletionEquiv k F q (a q) :=
  Equiv.piCongr_apply_apply _ _ _ _

theorem functionFieldAbsoluteValueAdeleEquiv_symm_apply (a : CurvePlaceAdeleRing k F)
    (q : RealAbsoluteValuePlace (F := F)) :
    (functionFieldAbsoluteValueAdeleEquiv k F).symm a q =
      (functionFieldAbsoluteValuePlaceCompletionEquiv k F q).symm
        (a (realAbsoluteValuePlaceCurvePlaceEquiv k F q)) := rfl

theorem continuous_functionFieldAbsoluteValueAdeleEquiv_symm :
    Continuous (functionFieldAbsoluteValueAdeleEquiv k F).symm := by
  exact RestrictedProduct.mapAlong_continuous
    (fun v : AlgebraicCurve.Place k F => curvePlaceCompletion v)
    (fun q : RealAbsoluteValuePlace (F := F) => realAbsoluteValuePlaceCompletion q)
    (realAbsoluteValuePlaceCurvePlaceEquiv k F)
    (realAbsoluteValuePlaceCurvePlaceEquiv k F).injective.tendsto_cofinite
    (fun q => (functionFieldAbsoluteValuePlaceCompletionEquiv k F q).symm)
    (Filter.Eventually.of_forall fun q x hx =>
      (functionFieldAbsoluteValuePlaceCompletionEquiv_mem_iff k F q _).mp
        (((functionFieldAbsoluteValuePlaceCompletionEquiv k F q).apply_symm_apply x).symm ▸ hx))
    (continuous_functionFieldAbsoluteValuePlaceCompletionEquiv_symm k F)

theorem continuous_functionFieldAbsoluteValueAdeleEquiv :
    Continuous (functionFieldAbsoluteValueAdeleEquiv k F) := by
  let E := realAbsoluteValuePlaceCurvePlaceEquiv k F
  let φ := fun v : AlgebraicCurve.Place k F =>
    completionCast k F (E.apply_symm_apply v) ∘
      functionFieldAbsoluteValuePlaceCompletionEquiv k F (E.symm v)
  have hφ : ∀ᶠ v in cofinite, Set.MapsTo (φ v)
      (realAbsoluteValuePlaceCompletionIntegers k F (E.symm v))
      (curvePlaceCompletionIntegers v) :=
    Filter.Eventually.of_forall fun v x hx =>
      (completionCast_mem_iff k F _ _).mpr
        ((functionFieldAbsoluteValuePlaceCompletionEquiv_mem_iff k F (E.symm v) x).mpr hx)
  have hc := RestrictedProduct.mapAlong_continuous
    (A₁ := fun q : RealAbsoluteValuePlace (F := F) =>
      (realAbsoluteValuePlaceCompletionIntegers k F q : Set _))
    (A₂ := fun v : AlgebraicCurve.Place k F => (curvePlaceCompletionIntegers v : Set _))
    (fun q : RealAbsoluteValuePlace (F := F) => realAbsoluteValuePlaceCompletion q)
    (fun v : AlgebraicCurve.Place k F => curvePlaceCompletion v)
    E.symm E.symm.injective.tendsto_cofinite φ hφ
    (fun v => (continuous_completionCast k F _).comp
      (continuous_functionFieldAbsoluteValuePlaceCompletionEquiv k F (E.symm v)))
  convert hc using 1
  funext a
  apply RestrictedProduct.ext
  intro v
  rfl

/-- The comparison preserves both existing restricted-product topologies. -/
def functionFieldAbsoluteValueAdeleHomeomorph :
    RealAbsoluteValueAdeleRing k F ≃ₜ CurvePlaceAdeleRing k F where
  toEquiv := (functionFieldAbsoluteValueAdeleEquiv k F).toEquiv
  continuous_toFun := continuous_functionFieldAbsoluteValueAdeleEquiv k F
  continuous_invFun := continuous_functionFieldAbsoluteValueAdeleEquiv_symm k F

theorem functionFieldAbsoluteValueAdeleEquiv_mem_level_iff
    (S : Finset (RealAbsoluteValuePlace (F := F))) (a : RealAbsoluteValueAdeleRing k F) :
    functionFieldAbsoluteValueAdeleEquiv k F a ∈
      curvePlaceAdeleLevel k F (S.map (realAbsoluteValuePlaceCurvePlaceEquiv k F).toEmbedding) ↔
        a ∈ realAbsoluteValueAdeleLevel k F S := by
  constructor
  · intro h q hq
    apply (functionFieldAbsoluteValuePlaceCompletionEquiv_mem_iff k F q _).mp
    rw [← functionFieldAbsoluteValueAdeleEquiv_apply]
    exact h _ (by simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hq)
  · intro h v hv
    obtain ⟨q, rfl⟩ := (realAbsoluteValuePlaceCurvePlaceEquiv k F).surjective v
    rw [functionFieldAbsoluteValueAdeleEquiv_apply,
      functionFieldAbsoluteValuePlaceCompletionEquiv_mem_iff]
    exact h q (by simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hv)

/-- Restrict the adelic comparison to any corresponding finite levels. -/
def functionFieldAbsoluteValueAdeleLevelEquiv
    (S : Finset (RealAbsoluteValuePlace (F := F))) :
    realAbsoluteValueAdeleLevel k F S ≃+*
      curvePlaceAdeleLevel k F (S.map (realAbsoluteValuePlaceCurvePlaceEquiv k F).toEmbedding) :=
  (functionFieldAbsoluteValueAdeleEquiv k F).restrict _ _
    fun a => (functionFieldAbsoluteValueAdeleEquiv_mem_level_iff k F S a).symm

@[simp]
theorem coe_functionFieldAbsoluteValueAdeleLevelEquiv
    (S : Finset (RealAbsoluteValuePlace (F := F))) (a : realAbsoluteValueAdeleLevel k F S) :
    (functionFieldAbsoluteValueAdeleLevelEquiv k F S a : CurvePlaceAdeleRing k F) =
      functionFieldAbsoluteValueAdeleEquiv k F a := rfl

/-- The corresponding finite-level subrings have homeomorphic subspace topologies. -/
def functionFieldAbsoluteValueAdeleLevelHomeomorph
    (S : Finset (RealAbsoluteValuePlace (F := F))) :
    realAbsoluteValueAdeleLevel k F S ≃ₜ
      curvePlaceAdeleLevel k F (S.map (realAbsoluteValuePlaceCurvePlaceEquiv k F).toEmbedding) where
  toEquiv := (functionFieldAbsoluteValueAdeleLevelEquiv k F S).toEquiv
  continuous_toFun :=
    ((continuous_functionFieldAbsoluteValueAdeleEquiv k F).comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_functionFieldAbsoluteValueAdeleEquiv_symm k F).comp
      continuous_subtype_val).subtype_mk _

/-- The diagonal of the global field in the actual absolute-value restricted product. -/
def realAbsoluteValueAdeleDiagonal : F →+* RealAbsoluteValueAdeleRing k F :=
  (functionFieldAbsoluteValueAdeleEquiv k F).symm.toRingHom.comp (curvePlaceAdeleDiagonal k F)

@[simp]
theorem realAbsoluteValueAdeleDiagonal_apply (x : F) (q : RealAbsoluteValuePlace (F := F)) :
    realAbsoluteValueAdeleDiagonal k F x q =
      ((WithAbs.toAbs q.out.val x : WithAbs q.out.val) : realAbsoluteValuePlaceCompletion q) := by
  change (functionFieldAbsoluteValuePlaceCompletionEquiv k F q).symm
    (algebraMap F _ x) = _
  apply (functionFieldAbsoluteValuePlaceCompletionEquiv k F q).injective
  rw [RingEquiv.apply_symm_apply, functionFieldAbsoluteValuePlaceCompletionEquiv_coe]

@[simp]
theorem functionFieldAbsoluteValueAdeleEquiv_diagonal (x : F) :
    functionFieldAbsoluteValueAdeleEquiv k F (realAbsoluteValueAdeleDiagonal k F x) =
      curvePlaceAdeleDiagonal k F x :=
  (functionFieldAbsoluteValueAdeleEquiv k F).apply_symm_apply _

instance : Algebra F (RealAbsoluteValueAdeleRing k F) :=
  (realAbsoluteValueAdeleDiagonal k F).toAlgebra

instance : Algebra k (RealAbsoluteValueAdeleRing k F) :=
  ((realAbsoluteValueAdeleDiagonal k F).comp (algebraMap k F)).toAlgebra

instance : IsScalarTower k F (RealAbsoluteValueAdeleRing k F) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The comparison also preserves the canonical global-field algebra structure. -/
def functionFieldAbsoluteValueAdeleAlgEquiv :
    RealAbsoluteValueAdeleRing k F ≃ₐ[F] CurvePlaceAdeleRing k F where
  __ := functionFieldAbsoluteValueAdeleEquiv k F
  commutes' := functionFieldAbsoluteValueAdeleEquiv_diagonal k F

end Langlands.Global
