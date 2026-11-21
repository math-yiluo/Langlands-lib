import Langlands.Global.RankinSelberg.InfiniteWhittakerReference
import Langlands.Global.RankinSelberg.InfiniteWhittakerMatrixSlice
import Langlands.Global.ArchimedeanEnvelopingJetProof

/-! # Determination of a one-place Whittaker slice by identity evaluation -/

noncomputable section
open NumberField
open scoped Classical TensorProduct CategoryTheory.MonObj Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal.InfiniteWhittakerSlice

open Langlands.Automorphic ContinuousRationalFunctions InfinitePlaceFamily
  Langlands.Global.CuspidalPairFunctionalEquation ArchimedeanGL
  ArchimedeanWhittakerEvaluation

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  {T : CuspidalOperatorRealization F r}

local notation "n" => r + 1
local notation "V" => T.placeDensityModels.subspace

private local instance (m : ℕ) : AlgebraicGeometry.IsAffine (Scheme F m).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
private local instance (m : ℕ) : AlgebraicGeometry.Smooth (Scheme F m).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
private local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance : AddCommGroup T.Space := Submodule.addCommGroup _
private local instance (i : Index F) : AddCommGroup (V i) := Submodule.addCommGroup _

variable (P : CuspidalSpectralPresentation.{u, uQ} T)
  (hP : HasIrreducibleAdmissibleComponents P) (χ : AddChar (Adeles F) ℂ)
  (hχ : IsStandardAdditiveCharacter F χ)

/-- The one-place coefficient, pulled back to the mixed infinite group. -/
def smoothSlice (a : FiniteTensor P) (i : Index F) (b : ∀ j, V j)
    (g : PlaceTuple (F := F) n) : V i →ₗ[ℂ] SmoothFunctions F n :=
  (freezeSmooth n i g).comp ((coefficient T χ hχ 1).comp (sliceVector P hP a i b))

private theorem smoothSlice_apply_tuple (a : FiniteTensor P) (i : Index F) (b : ∀ j, V j)
    (g y : PlaceTuple (F := F) n) (v : V i) :
    (smoothSlice P hP χ hχ a i b g v).val ((archimedeanGLCoordinates F n).symm (tupleGL n y)) =
      sliceMap P hP χ hχ a i b g v (y i) := by
  rw [smoothSlice, LinearMap.comp_apply, LinearMap.comp_apply, freezeSmooth_apply,
    ContinuousMulEquiv.apply_symm_apply, freezeGL_tupleGL, coefficient_apply,
    ContinuousMulEquiv.apply_symm_apply, sliceMap_apply]
  rfl

theorem smoothSlice_apply_one (a : FiniteTensor P) (i : Index F) (b : ∀ j, V j)
    (g : PlaceTuple (F := F) n) (v : V i) :
    (smoothSlice P hP χ hχ a i b g v).val 1 = sliceMap P hP χ hχ a i b g v 1 := by
  rw [smoothSlice, LinearMap.comp_apply, LinearMap.comp_apply, freezeSmooth_apply,
    map_one, freezeGL_one, coefficient_apply, ContinuousMulEquiv.apply_symm_apply, sliceMap_apply]
  rfl

theorem smoothSlice_analytic (a : FiniteTensor P) (i : Index F) (b : ∀ j, V j)
    (g : PlaceTuple (F := F) n) (v : V i) (x : ArchimedeanGL F n) :
    AnalyticAt ℝ (coordinateExtension F n (smoothSlice P hP χ hχ a i b g v)) x.val :=
  freezeSmooth_analytic n i g _ (jointFiniteAnalyticity F n _
    (coefficient_jointFinite T χ hχ 1 (sliceVector P hP a i b v))) x

/-- Varying a single vector gives an intertwiner for its place Lie action. -/
theorem sliceVector_lie (a : FiniteTensor P) (i : Index F) (b : ∀ j, V j)
    (X : Lie n i) (v : V i) :
    sliceVector P hP a i b (T.placeDensityModels.sourceLie i X v) =
      T.realization.placeLieFamily i X (sliceVector P hP a i b v) := by
  change P.allPlaceTensorEquiv hP
      (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update b i (T.placeDensityModels.sourceLie i X v))) =
    T.realization.placeLieFamily i X
      (P.allPlaceTensorEquiv hP (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update b i v)))
  apply P.allPlaceTensorEquiv_lie hP
  · intro j hj
    rw [Function.update_of_ne hj, Function.update_of_ne hj]
  · simp only [Function.update_self]

theorem smoothSlice_lie (a : FiniteTensor P) (i : Index F) (b : ∀ j, V j)
    (g : PlaceTuple (F := F) n) (X : RealLieAlgebra F n) (v : V i) :
    smoothDifferential F n X (smoothSlice P hP χ hχ a i b g v) =
      smoothSlice P hP χ hχ a i b g (T.placeDensityModels.sourceLie i (placeGenerator n i X) v) := by
  simp only [smoothSlice, LinearMap.comp_apply, smoothDifferential_freezeSmooth,
    ← coefficient_lie, sliceVector_lie]
  congr 2
  simp only [OperatorRealization.placeLieFamily, LieHom.comp_apply, lieInclusion_placeGenerator,
    OperatorRealization.complexLieAction_apply]

/-- The same varying-vector map intertwines the compact action at that place. -/
theorem sliceVector_compact (a : FiniteTensor P) (i : Index F) (b : ∀ j, V j)
    (k : Compact n i) (v : V i) :
    sliceVector P hP a i b (T.placeDensityModels.sourceCompact i k v) =
      T.realization.compactRepresentation (compactInclusion n i k) (sliceVector P hP a i b v) := by
  change P.allPlaceTensorEquiv hP
      (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update b i (T.placeDensityModels.sourceCompact i k v))) =
    T.realization.placeCompactFamily i k
      (P.allPlaceTensorEquiv hP (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update b i v)))
  apply P.allPlaceTensorEquiv_compact hP
  · intro j hj
    rw [Function.update_of_ne hj, Function.update_of_ne hj]
  · simp only [Function.update_self]

set_option maxHeartbeats 6500000 in
private theorem exists_smoothSlice_apply_compact (i : Index F) (k : standardInfiniteCompact F n) :
    ∃ l : Compact n i, ∀ (a : FiniteTensor P) (b : ∀ j, V j) (g : PlaceTuple (F := F) n) (v : V i),
      (smoothSlice P hP χ hχ a i b g v).val k.val =
        (smoothSlice P hP χ hχ a i b g (T.placeDensityModels.sourceCompact i l v)).val 1 := by
  have hfreeze : ∃ l : Compact n i, ∀ g : PlaceTuple (F := F) n,
      freezeGL n i g (archimedeanGLCoordinates F n k.val) =
        freezeGL n i g 1 * archimedeanGLCoordinates F n (compactInclusion n i l).val :=
    exists_freezeGL_compact (F := F) n i k
  obtain ⟨l, hl⟩ := hfreeze
  refine ⟨l, fun a b g v => ?_⟩
  let e := archimedeanGLCoordinates F n
  let kᵢ : standardInfiniteCompact F n := compactInclusion n i l
  let p := e.symm (freezeGL n i g 1)
  let w : T.Space := sliceVector P hP a i b v
  let w' : T.Space := sliceVector P hP a i b (T.placeDensityModels.sourceCompact i l v)
  let f : SmoothFunctions F n := coefficient T χ hχ 1 w
  let f' : SmoothFunctions F n := coefficient T χ hχ 1 w'
  have hpoint : e.symm (freezeGL n i g (e k.val)) = p * kᵢ.val := by
    calc
      _ = e.symm (freezeGL n i g 1 * e kᵢ.val) := congrArg e.symm (hl g)
      _ = _ := by rw [map_mul, ContinuousMulEquiv.symm_apply_apply]
  have hidentity : e.symm (freezeGL n i g (e 1)) = p :=
    congrArg (e.symm ∘ freezeGL n i g) (map_one e)
  have hcompact : f' = smoothRightAction F n kᵢ.val f :=
    (congrArg (coefficient T χ hχ 1) (sliceVector_compact P hP a i b l v)).trans
      (coefficient_compact T χ hχ 1 kᵢ w)
  change (freezeSmooth n i g f).val k.val = (freezeSmooth n i g f').val 1
  calc
    _ = f.val (e.symm (freezeGL n i g (e k.val))) := freezeSmooth_apply n i g f k.val
    _ = f.val (p * kᵢ.val) := congrArg f.val hpoint
    _ = (smoothRightAction F n kᵢ.val f).val p := (smoothRightAction_apply F n _ _ f).symm
    _ = f'.val p := congrArg (fun q : SmoothFunctions F n => q.val p) hcompact.symm
    _ = f'.val (e.symm (freezeGL n i g (e 1))) := congrArg f'.val hidentity.symm
    _ = _ := (freezeSmooth_apply n i g f' 1).symm

private theorem exists_smoothSlice_enveloping (i : Index F)
    (D : EnvelopingAlgebra F n) (v : V i) :
    ∃ w : V i, ∀ (a : FiniteTensor P) (b : ∀ j, V j) (g : PlaceTuple (F := F) n),
      envelopingAction F n D (smoothSlice P hP χ hχ a i b g v) =
        smoothSlice P hP χ hχ a i b g w := by
  induction D using enveloping_real_left_induction F n with
  | h1 =>
    exact ⟨v, fun a b g => by rw [envelopingAction_one]⟩
  | hadd D E hD hE =>
    obtain ⟨w, hw⟩ := hD
    obtain ⟨w', hw'⟩ := hE
    exact ⟨w + w', fun a b g => by simp only [map_add, LinearMap.add_apply, hw, hw']⟩
  | hsmul c D hD =>
    obtain ⟨w, hw⟩ := hD
    exact ⟨c • w, fun a b g => by simp only [map_smul, LinearMap.smul_apply, hw]⟩
  | hgen X D hD =>
    obtain ⟨w, hw⟩ := hD
    refine ⟨T.placeDensityModels.sourceLie i (placeGenerator n i X) w, fun a b g => ?_⟩
    let d := envelopingGenerator F n (complexify F n X)
    let f := smoothSlice P hP χ hχ a i b g v
    let f' := smoothSlice P hP χ hχ a i b g w
    calc
      _ = envelopingAction F n d (envelopingAction F n D f) := envelopingAction_mul F n d D f
      _ = envelopingAction F n d f' := congrArg (envelopingAction F n d) (hw a b g)
      _ = smoothDifferential F n X f' :=
        DFunLike.congr_fun (envelopingAction_real_generator F n X) f'
      _ = _ := smoothSlice_lie P hP χ hχ a i b g X w

/-- An identity-evaluation relation on all vectors of a fixed local source extends
to a relation of the actual coefficient functions. -/
theorem sliceMap_eq_smul_of_eval_one (i : Index F) (a a' : FiniteTensor P)
    (b b' : ∀ j, V j) (g g' : PlaceTuple (F := F) n) (c : ℂ)
    (h : ∀ v : V i, sliceMap P hP χ hχ a i b g v 1 = c * sliceMap P hP χ hχ a' i b' g' v 1) :
    sliceMap P hP χ hχ a i b g = c • sliceMap P hP χ hχ a' i b' g' := by
  apply LinearMap.ext
  intro v
  funext y
  let x := (archimedeanGLCoordinates F n).symm (tupleGL n (Function.update 1 i y))
  let S := smoothSlice P hP χ hχ a i b g v
  let S' := smoothSlice P hP χ hχ a' i b' g' v
  let A := S - c • S'
  have ha (z : ArchimedeanGL F n) : AnalyticAt ℝ (coordinateExtension F n A) z.val := by
    change AnalyticAt ℝ (coordinateExtension F n S - fun q => c * coordinateExtension F n S' q) z.val
    exact (smoothSlice_analytic P hP χ hχ a i b g v z).sub
      (analyticAt_const.mul (smoothSlice_analytic P hP χ hχ a' i b' g' v z))
  obtain ⟨k, hk⟩ := compactComponentCoverage F n x
  obtain ⟨l, hl⟩ := exists_smoothSlice_apply_compact P hP χ hχ i k
  have hz (D : EnvelopingAlgebra F n) : (envelopingAction F n D A).val k.val = 0 := by
    obtain ⟨w, hw⟩ := exists_smoothSlice_enveloping P hP χ hχ i D v
    simp only [A, S, S', map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, hw, hl, smoothSlice_apply_one, h, sub_self]
  have hzero := analyticMatrixJetUniqueness F n A k.val ha (envelopingZeroJet F n A k.val hz) x hk
  simpa only [A, S, S', x, Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, smoothSlice_apply_tuple, Function.update_self, sub_eq_zero, LinearMap.smul_apply]
    using hzero

private def tupleOn {I : Type*} [DecidableEq I] {A : I → Type*}
    (b b₀ : ∀ i, A i) (E : Finset I) (i : I) : A i :=
  if i ∈ E then b i else b₀ i

private theorem tupleOn_insert {I : Type*} [DecidableEq I] {A : I → Type*}
    (b b₀ : ∀ i, A i) (E : Finset I) (i : I) :
    tupleOn b b₀ (insert i E) = Function.update (tupleOn b b₀ E) i (b i) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [tupleOn]
  · simp [tupleOn, h]

private theorem tupleOn_empty {I : Type*} [DecidableEq I] {A : I → Type*}
    (b b₀ : ∀ i, A i) : tupleOn b b₀ ∅ = b₀ := by
  funext i
  simp [tupleOn]

private theorem tupleOn_univ {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    (b b₀ : ∀ i, A i) : tupleOn b b₀ Finset.univ = b := by
  funext i
  simp [tupleOn]

private theorem product_update {I : Type*} [Fintype I] [DecidableEq I]
    {A B : I → Type*} (M : ∀ i, A i → B i → ℂ)
    (b : ∀ j, A j) (g : ∀ j, B j) (i : I) (v : A i) (y : B i) :
    (∏ j, M j (Function.update b i v j) (Function.update g i y j)) =
      (∏ j ∈ Finset.univ.erase i, M j (b j) (g j)) * M i v y := by
  rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i),
    Function.update_self, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji := (Finset.mem_erase.mp hj).1
  rw [Function.update_of_ne hji, Function.update_of_ne hji]

private theorem eq_product_at_identity {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} (C : (∀ i, A i) → ℂ) (f : ∀ i, A i → ℂ) (b₀ : ∀ i, A i)
    (hn : ∀ i, f i (b₀ i) = 1)
    (h : ∀ i b, ∃ c : ℂ, ∀ v, C (Function.update b i v) = c * f i v)
    (b : ∀ i, A i) : C b = C b₀ * ∏ j, f j (b j) := by
  have hstep (i : I) (d : ∀ j, A j) (v : A i) :
      C (Function.update d i v) = C (Function.update d i (b₀ i)) * f i v := by
    obtain ⟨c, hc⟩ := h i d
    rw [hc v, hc (b₀ i), hn i, mul_one]
  have hpartial (E : Finset I) : C (tupleOn b b₀ E) = C b₀ * ∏ j ∈ E, f j (b j) := by
    induction E using Finset.induction_on with
    | empty => rw [tupleOn_empty, Finset.prod_empty, mul_one]
    | @insert i E hi ih =>
      have hreset : Function.update (tupleOn b b₀ E) i (b₀ i) = tupleOn b b₀ E :=
        Function.update_eq_self_iff.mpr (ite_eq_right hi).symm
      rw [tupleOn_insert, hstep, hreset, ih, Finset.prod_insert hi]
      ac_rfl
  simpa only [tupleOn_univ] using hpartial Finset.univ

private theorem eq_product_of_identity {I : Type*} [Fintype I] [DecidableEq I]
    {A B : I → Type*} [∀ i, One (B i)] (C : (∀ i, A i) → (∀ i, B i) → ℂ)
    (M : ∀ i, A i → B i → ℂ) (b₀ : ∀ i, A i)
    (hn : ∀ i, M i (b₀ i) 1 = 1)
    (h : ∀ i b, ∃ c : ℂ, ∀ v, C (Function.update b i v) 1 = c * M i v 1)
    (hadvance : ∀ i b g (c : ℂ),
      (∀ v, C (Function.update b i v) (Function.update g i 1) = c * M i v 1) →
      ∀ v y, C (Function.update b i v) (Function.update g i y) = c * M i v y)
    (b : ∀ i, A i) (g : ∀ i, B i) : C b g = C b₀ 1 * ∏ j, M j (b j) (g j) := by
  have hpartial (E : Finset I) (d : ∀ i, A i) :
      C d (tupleOn g 1 E) = C b₀ 1 * ∏ j, M j (d j) (tupleOn g 1 E j) := by
    induction E using Finset.induction_on generalizing d with
    | empty =>
      rw [tupleOn_empty]
      exact eq_product_at_identity (fun d => C d 1) (fun i v => M i v 1) b₀ hn h d
    | @insert i E hi ih =>
      let z := tupleOn g 1 E
      let c := C b₀ 1 * ∏ j ∈ Finset.univ.erase i, M j (d j) (z j)
      have hreset : Function.update z i 1 = z := Function.update_eq_self_iff.mpr (ite_eq_right hi).symm
      have hvalue (v : A i) : C (Function.update d i v) (Function.update z i 1) = c * M i v 1 := by
        calc
          _ = C (Function.update d i v) z := congrArg (C (Function.update d i v)) hreset
          _ = C b₀ 1 * ∏ j, M j (Function.update d i v j) (z j) := ih _
          _ = C b₀ 1 * ∏ j, M j (Function.update d i v j) (Function.update z i 1 j) := by
            rw [hreset]
          _ = _ := by rw [product_update, mul_assoc]
      have hall := hadvance i d z c hvalue (d i) (g i)
      have hd : Function.update d i (d i) = d := Function.update_eq_self_iff.mpr rfl
      rw [tupleOn_insert]
      calc
        _ = c * M i (d i) (g i) := by simpa only [hd] using hall
        _ = C b₀ 1 * ∏ j, M j (Function.update d i (d i) j) (Function.update z i (g i) j) := by
          rw [product_update, mul_assoc]
        _ = _ := by rw [hd]
  simpa only [tupleOn_univ] using hpartial Finset.univ b

/-- For the normalized reference slices, proportionality at the full adelic
identity already implies a product formula at every infinite tuple. -/
theorem tensorWhittaker_eq_product_of_identity (a₀ : FiniteTensor P) (b₀ : ∀ j, V j)
    (h₀ : tensorWhittaker P hP χ a₀ b₀ 1 ≠ 0)
    (h : ∀ (a : FiniteTensor P) (i : Index F) (b : ∀ j, V j),
      ∃ c : ℂ, ∀ v : V i,
        sliceMap P hP χ hχ a i b 1 v 1 = c * sliceMap P hP χ hχ a₀ i b₀ 1 v 1)
    (a : FiniteTensor P) (b : ∀ j, V j) (g : PlaceTuple (F := F) n) :
    tensorWhittaker P hP χ a b g =
      tensorWhittaker P hP χ a b₀ 1 * ∏ j, referenceModel P hP χ hχ a₀ b₀ j (b j) (g j) := by
  let τ := tensorWhittaker P hP χ a₀ b₀ 1
  let M (i : Index F) (v : V i) (y : PlaceGroup n i) := referenceModel P hP χ hχ a₀ b₀ i v y
  let C := tensorWhittaker P hP χ a
  refine eq_product_of_identity C M b₀ (referenceModel_normalized P hP χ hχ a₀ b₀ h₀) ?_ ?_ b g
  · intro i d
    obtain ⟨c, hc⟩ := h a i d
    refine ⟨c * τ, fun v => ?_⟩
    have he : Function.update (1 : PlaceTuple (F := F) n) i 1 = 1 := Function.update_eq_self_iff.mpr rfl
    have href : sliceMap P hP χ hχ a₀ i b₀ 1 v 1 = τ * M i v 1 := by
      change _ = τ * (τ⁻¹ * _)
      rw [← mul_assoc, mul_inv_cancel₀ h₀, one_mul]
    calc
      _ = sliceMap P hP χ hχ a i d 1 v 1 := (congrArg (C (Function.update d i v)) he).symm
      _ = c * sliceMap P hP χ hχ a₀ i b₀ 1 v 1 := hc v
      _ = _ := by rw [href, mul_assoc]
  · intro i d z c hc v y
    have hmap := sliceMap_eq_smul_of_eval_one P hP χ hχ i a a₀ d b₀ z 1 (c * τ⁻¹)
      (fun w => (hc w).trans (mul_assoc c τ⁻¹ _).symm)
    exact (congrArg (fun L : V i →ₗ[ℂ] (PlaceGroup n i → ℂ) => L v y) hmap).trans
      (mul_assoc c τ⁻¹ _)

/-- A nonzero reference pure tensor and proportionality of its one-place identity
functionals to the other identity functionals give the normalized local model data. -/
theorem nonempty_modelData_of_eval_one (a₀ : FiniteTensor P) (b₀ : ∀ j, V j)
    (h₀ : tensorWhittaker P hP χ a₀ b₀ 1 ≠ 0)
    (h : ∀ (a : FiniteTensor P) (i : Index F) (b : ∀ j, V j),
      ∃ c : ℂ, ∀ v : V i,
        sliceMap P hP χ hχ a i b 1 v 1 = c * sliceMap P hP χ hχ a₀ i b₀ 1 v 1) :
    Nonempty (ModelData P hP χ) := by
  let M := referenceModel P hP χ hχ a₀ b₀
  refine ⟨⟨M, fun i => ⟨b₀ i, referenceModel_normalized P hP χ hχ a₀ b₀ h₀ i⟩, ?_⟩⟩
  intro a i b g
  refine ⟨tensorWhittaker P hP χ a b₀ 1 * ∏ j ∈ Finset.univ.erase i, M j (b j) (g j),
    fun v y => ?_⟩
  calc
    _ = tensorWhittaker P hP χ a b₀ 1 *
        ∏ j, M j (Function.update b i v j) (Function.update g i y j) :=
      tensorWhittaker_eq_product_of_identity P hP χ hχ a₀ b₀ h₀ h a _ _
    _ = _ := by rw [product_update (fun i v y => M i v y), ← mul_assoc]

end Langlands.Global.RankinSelbergGlobal.InfiniteWhittakerSlice
