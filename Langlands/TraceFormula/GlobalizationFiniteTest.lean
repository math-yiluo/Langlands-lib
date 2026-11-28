import Langlands.TraceFormula.GlobalizationTensor
import Langlands.TraceFormula.CompactSmoothAdelicGLTest
import Langlands.TraceFormula.NormOneThreePlaceOrbital
import Langlands.TraceFormula.GeneralLinearLocalOrbitalTransport
import Langlands.TraceFormula.GeneralLinearCuspFormLocalVanishingProof
import Langlands.Global.AdelicGLInverseTranspose
import Langlands.BaseChange.CuspForm

/-!
# Finite adelic tensor tests with prescribed local factors

See `GlobalizationFiniteTest.md`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Set Topology
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.HarmonicAnalysis

namespace Langlands.TraceFormula.GlobalizationTensor

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance : DecidableEq (Langlands.Global.FinitePlace K) := Classical.decEq _

variable (S : Finset (Langlands.Global.FinitePlace K))
  (F : ∀ v : Langlands.Global.FinitePlace K, SchwartzBruhat (FiniteLocalGL K n v))

theorem isLocallyConstant_finsetProd {X : Type*} [TopologicalSpace X] {Idx : Type*}
    (T : Finset Idx) (g : Idx → X → ℂ) (hg : ∀ i ∈ T, IsLocallyConstant (g i)) :
    IsLocallyConstant fun x => ∏ i ∈ T, g i x := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact IsLocallyConstant.const 1
  | insert a T ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hg a (Finset.mem_insert_self a T)).mul
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

set_option maxHeartbeats 950000 in
/-- The finite adelic test `y ↦ ∏_{v ∈ S} F_v(y_v) · 1_{∏_{v ∉ S} GL_n(𝒪_v)}(y)`. -/
def finiteTest : CompactFiniteGLTest K n := by
  let E := FiniteAdelicGL.splitAtPlaces K n (· ∈ S)
  let h := awayCharacteristic K n S
  let P : (∀ v : S, FiniteLocalGL K n v) × FiniteAdelicGL.AwayRestrictedProduct K n (· ∈ S) →
      ℂ := fun z => (∏ v : S, F v (z.1 v)) * h z.2
  have hP : IsLocallyConstant P := by
    apply IsLocallyConstant.mul
    · exact isLocallyConstant_finsetProd (Finset.univ : Finset S)
        (fun (v : S) (z : (∀ v : S, FiniteLocalGL K n v) ×
          FiniteAdelicGL.AwayRestrictedProduct K n (· ∈ S)) => F v (z.1 v)) fun v _ =>
        (F v).2.1.comp_continuous ((continuous_apply v).comp continuous_fst)
    · exact h.2.1.comp_continuous continuous_snd
  have hlocals : IsCompact (Set.univ.pi (fun v : S => tsupport (F v))) :=
    isCompact_univ_pi fun v => (F v).2.2
  have hsupport := hlocals.prod h.2.2
  have hPc : HasCompactSupport P := by
    refine HasCompactSupport.intro' hsupport
      ((isClosed_set_pi fun _ _ => isClosed_closure).prod isClosed_closure) ?_
    intro z hz
    by_contra hn
    simp only [P, mul_eq_zero, not_or] at hn
    refine hz ⟨Set.mem_univ_pi.mpr fun v => subset_tsupport _
      (fun he => hn.1 (Finset.prod_eq_zero (Finset.mem_univ v) he)), subset_tsupport _ hn.2⟩
  exact ⟨⟨P ∘ E, hP.comp_continuous E.continuous⟩, hPc.comp_homeomorph E.toHomeomorph⟩

theorem finiteTest_apply (y : FiniteAdelicGL K n) :
    (finiteTest K n S F).val y =
      (∏ v : S, F v (FiniteAdelicGL.localProjection K n v y)) *
        awayCharacteristic K n S ((FiniteAdelicGL.splitAtPlaces K n (· ∈ S) y).2) :=
  rfl

/-- The tensor of an archimedean kernel and the finite test, on adelic matrices. -/
theorem adelicTestTensor_finiteTest (a : ArchimedeanGL.SmoothCompactKernel K n)
    (g : AdelicGL K n) :
    adelicTestTensor K n a (finiteTest K n S F) g =
      ArchimedeanGL.kernelToContinuousMap K n a (AdelicGL.infinite K n g) *
        ((∏ v : S, F v (finiteComponent K n v g)) * awayCharacteristic K n S (awayComponent K n S g)) :=
  rfl

/-- The finite test, translated on both sides and restricted to one place `v ∈ S`, is a constant
times a two-sided translate of the local factor at `v`. -/
theorem finiteTest_localSlice (v : Langlands.Global.FinitePlace K) (hv : v ∈ S)
    (x y : FiniteAdelicGL K n) :
    (fun g : FiniteLocalGL K n v =>
        (finiteTest K n S F).val (x * FiniteAdelicGL.localInclusion K n v g * y)) =
      fun g => (∏ w ∈ S.erase v, F w (FiniteAdelicGL.localProjection K n w (x * y))) *
          awayCharacteristic K n S ((FiniteAdelicGL.splitAtPlaces K n (· ∈ S) (x * y)).2) *
        F v (FiniteAdelicGL.localProjection K n v x * g * FiniteAdelicGL.localProjection K n v y) := by
  funext g
  rw [finiteTest_apply, Finset.prod_coe_sort S
    (fun w => F w (FiniteAdelicGL.localProjection K n w (x * FiniteAdelicGL.localInclusion K n v g * y))),
    ← Finset.mul_prod_erase S _ hv]
  have hloc : FiniteAdelicGL.localProjection K n v (x * FiniteAdelicGL.localInclusion K n v g * y) =
      FiniteAdelicGL.localProjection K n v x * g * FiniteAdelicGL.localProjection K n v y := by
    rw [map_mul, map_mul, FiniteAdelicGL.localProjection_localInclusion]
  have hprod : (∏ w ∈ S.erase v, F w (FiniteAdelicGL.localProjection K n w
      (x * FiniteAdelicGL.localInclusion K n v g * y))) =
      ∏ w ∈ S.erase v, F w (FiniteAdelicGL.localProjection K n w (x * y)) := by
    apply Finset.prod_congr rfl
    intro w hw
    have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
    rw [map_mul, map_mul, map_mul, FiniteAdelicGL.localProjection_localInclusion_of_ne K n v w hwv,
      mul_one]
  have haway : (FiniteAdelicGL.splitAtPlaces K n (· ∈ S)
      (x * FiniteAdelicGL.localInclusion K n v g * y)).2 =
      (FiniteAdelicGL.splitAtPlaces K n (· ∈ S) (x * y)).2 := by
    have h1 : (FiniteAdelicGL.splitAtPlaces K n (· ∈ S) (FiniteAdelicGL.localInclusion K n v g)).2 =
        1 := by
      apply RestrictedProduct.ext
      intro w
      have hw : w.val ≠ v := fun he => w.property (he.symm ▸ hv)
      rw [FiniteAdelicGL.splitAtPlaces_apply_snd, FiniteAdelicGL.localProjection_localInclusion_of_ne K n v
        w.val hw]
      rfl
    simp only [map_mul, Prod.snd_mul, h1, mul_one]
  rw [hloc, hprod, haway]
  ring

set_option maxHeartbeats 1600000 in
/-- **Cuspidality of the finite test at a place.** If the local factor at `v ∈ S` has vanishing
constant terms, then the finite test integrates to zero along every two-sided translate of every
two-block unipotent radical at `v`. -/
theorem finiteTest_twoBlock_vanishing (v : Langlands.Global.FinitePlace K) (hv : v ∈ S)
    (hF : BaseChange.HasVanishingConstantTerms (F v : FiniteLocalGL K n v → ℂ))
    (p q : ℕ) (hpq : p + q = n) (hp : 0 < p) (hq : 0 < q) :
    letI : MeasurableSpace (Matrix (Fin p) (Fin q) (FiniteCompletion K v)) := borel _
    ∀ ν : MeasureTheory.Measure (Matrix (Fin p) (Fin q) (FiniteCompletion K v)),
      ν.IsAddHaarMeasure → ∀ x y : FiniteAdelicGL K n,
        ∫ Z, (finiteTest K n S F).val
          (x * FiniteAdelicGL.localInclusion K n v (GeneralLinear.blockUnipotent hpq Z) * y) ∂ν = 0 := by
  intro ν hν x y
  have key := generalLinearCuspFormLocalVanishing K n v
    (fun g => (finiteTest K n S F).val (AdelicGL.finite K n g)) (by
      intro X Y
      have h := finiteTest_localSlice K n S F v hv (AdelicGL.finite K n X) (AdelicGL.finite K n Y)
      have heq : (fun g : GeneralLinear n (FiniteCompletion K v) =>
          (finiteTest K n S F).val (AdelicGL.finite K n
            (X * AdelicGL.ofFinite K n (FiniteAdelicGL.localInclusion K n v g) * Y))) =
          fun g => (finiteTest K n S F).val (AdelicGL.finite K n X *
            FiniteAdelicGL.localInclusion K n v g * AdelicGL.finite K n Y) := by
        funext g
        congr 1
        rw [map_mul (AdelicGL.finite K n), map_mul (AdelicGL.finite K n), AdelicGL.finite_ofFinite]
      change BaseChange.HasVanishingConstantTerms (fun g : GeneralLinear n (FiniteCompletion K v) =>
        (finiteTest K n S F).val (AdelicGL.finite K n
          (X * AdelicGL.ofFinite K n (FiniteAdelicGL.localInclusion K n v g) * Y)))
      rw [heq, h]
      exact (((hF.comp_mul_right (FiniteAdelicGL.localProjection K n v (AdelicGL.finite K n Y))).comp_mul_left
        (FiniteAdelicGL.localProjection K n v (AdelicGL.finite K n X))).const_mul _)) p q hpq hp hq ν hν
      (AdelicGL.ofFinite K n x) (AdelicGL.ofFinite K n y)
  simpa only [map_mul (AdelicGL.finite K n), AdelicGL.finite_ofFinite] using key

/-- On the closed support of the full tensor test, the component at each place `v ∈ S` lies in
the closed support of the local factor `F_v`. -/
theorem finiteComponent_mem_tsupport (a : ArchimedeanGL.SmoothCompactKernel K n)
    (v : Langlands.Global.FinitePlace K) (hv : v ∈ S) (g : AdelicGL K n)
    (hg : g ∈ tsupport (adelicTestTensor K n a (finiteTest K n S F))) :
    FiniteAdelicGL.localProjection K n v (AdelicGL.finite K n g) ∈
      tsupport (F v : FiniteLocalGL K n v → ℂ) := by
  have hclosed : IsClosed {g : AdelicGL K n |
      finiteComponent K n v g ∈ tsupport (F v : FiniteLocalGL K n v → ℂ)} :=
    isClosed_closure.preimage (finiteComponent K n v).continuous
  refine closure_minimal (fun g hg => ?_) hclosed hg
  apply subset_tsupport
  intro h0
  apply hg
  rw [adelicTestTensor_finiteTest, Finset.prod_coe_sort S
    (fun w => F w (finiteComponent K n w g)), ← Finset.mul_prod_erase S _ hv]
  change ArchimedeanGL.kernelToContinuousMap K n a (AdelicGL.infinite K n g) *
    (F v (finiteComponent K n v g) * _ * _) = 0
  rw [show F v (finiteComponent K n v g) = 0 from h0]
  simp only [zero_mul, mul_zero]

set_option maxHeartbeats 1600000 in
/-- **Adelic cuspidality of the full tensor test.** If the local factor at `v ∈ S` has vanishing
constant terms, the tensor `a ⊗ finiteTest S F` integrates to zero along every two-sided translate
of every two-block unipotent radical at `v`. -/
theorem adelicTestTensor_finiteTest_twoBlock_vanishing (a : ArchimedeanGL.SmoothCompactKernel K n)
    (v : Langlands.Global.FinitePlace K) (hv : v ∈ S)
    (hF : BaseChange.HasVanishingConstantTerms (F v : FiniteLocalGL K n v → ℂ))
    (p q : ℕ) (hpq : p + q = n) (hp : 0 < p) (hq : 0 < q) :
    letI : MeasurableSpace (Matrix (Fin p) (Fin q) (FiniteCompletion K v)) := borel _
    ∀ ν : MeasureTheory.Measure (Matrix (Fin p) (Fin q) (FiniteCompletion K v)),
      ν.IsAddHaarMeasure → ∀ x y : AdelicGL K n,
        ∫ Z, adelicTestTensor K n a (finiteTest K n S F)
          (x * AdelicGL.ofFinite K n
            (FiniteAdelicGL.localInclusion K n v (GeneralLinear.blockUnipotent hpq Z)) * y) ∂ν =
          0 := by
  intro ν hν x y
  have h (Z : Matrix (Fin p) (Fin q) (FiniteCompletion K v)) :
      adelicTestTensor K n a (finiteTest K n S F) (x * AdelicGL.ofFinite K n
        (FiniteAdelicGL.localInclusion K n v (GeneralLinear.blockUnipotent hpq Z)) * y) =
      ArchimedeanGL.kernelToContinuousMap K n a (AdelicGL.infinite K n (x * y)) *
        (finiteTest K n S F).val (AdelicGL.finite K n x *
          FiniteAdelicGL.localInclusion K n v (GeneralLinear.blockUnipotent hpq Z) *
            AdelicGL.finite K n y) := by
    change ArchimedeanGL.kernelToContinuousMap K n a (AdelicGL.infinite K n _) *
      (finiteTest K n S F).val (AdelicGL.finite K n _) = _
    rw [map_mul (AdelicGL.infinite K n), map_mul (AdelicGL.infinite K n),
      AdelicGL.infinite_ofFinite, mul_one, map_mul (AdelicGL.finite K n),
      map_mul (AdelicGL.finite K n), AdelicGL.finite_ofFinite, map_mul (AdelicGL.infinite K n)]
  simp only [h]
  rw [MeasureTheory.integral_const_mul,
    finiteTest_twoBlock_vanishing K n S F v hv hF p q hpq hp hq ν hν, mul_zero]

section GroupScheme

local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

local instance : IsAffine (GLG).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

/-- The two insertions of a finite local point agree. -/
theorem finitePlacePointInclusion_eq_ofPlace (v : Langlands.Global.FinitePlace K)
    (x : PlaceGroupPoints K GLG (.inr v)) :
    finitePlacePointInclusion K GLG v x = AdelicGroupPoints.ofPlace K GLG (.inr v) x := by
  apply AdelicGroupPoints.ext_atPlace K GLG
  intro i
  by_cases hi : i = .inr v
  · subst i
    rw [atPlace_finitePlacePointInclusion, AdelicGroupPoints.atPlace_ofPlace_same]
  · rw [atPlace_finitePlacePointInclusion_of_ne K GLG v i hi,
      AdelicGroupPoints.atPlace_ofPlace_of_ne K GLG _ _ hi]

/-- The full adelic test on group-scheme points. -/
def fullTest (a : ArchimedeanGL.SmoothCompactKernel K n) (x : AdelicGroupPoints K GLG) : ℂ :=
  adelicTestTensor K n a (finiteTest K n S F) (GeneralLinearGroupPoints.adelicHomeomorph K n x)

/-- The part of the full test away from three places of `S`. -/
def fullTestExterior (a : ArchimedeanGL.SmoothCompactKernel K n)
    (v₀ v₁ v₂ : Langlands.Global.FinitePlace K) (x : AdelicGroupPoints K GLG) : ℂ :=
  let g := GeneralLinearGroupPoints.adelicHomeomorph K n x
  ArchimedeanGL.kernelToContinuousMap K n a (AdelicGL.infinite K n g) *
    ((∏ v ∈ ((S.erase v₀).erase v₁).erase v₂, F v (finiteComponent K n v g)) *
      awayCharacteristic K n S (awayComponent K n S g))

/-- The full test is the tensor of the three local factors and the exterior part. -/
theorem fullTest_eq_threePlaceTensor (a : ArchimedeanGL.SmoothCompactKernel K n)
    (v₀ v₁ v₂ : Langlands.Global.FinitePlace K) (h0 : v₀ ∈ S) (h1 : v₁ ∈ S) (h2 : v₂ ∈ S)
    (h01 : v₀ ≠ v₁) (h02 : v₀ ≠ v₂) (h12 : v₁ ≠ v₂) :
    fullTest K n S F a = threePlaceTensor K GLG v₀ v₁ v₂
      (fun y => F v₀ (localMatrixHomeomorph K n v₀ y))
      (fun y => F v₁ (localMatrixHomeomorph K n v₁ y))
      (fun y => F v₂ (localMatrixHomeomorph K n v₂ y))
      (fullTestExterior K n S F a v₀ v₁ v₂) := by
  funext x
  have hc (v : Langlands.Global.FinitePlace K) :
      localMatrixHomeomorph K n v (AdelicGroupPoints.atPlace K GLG (.inr v) x) =
        finiteComponent K n v (GeneralLinearGroupPoints.adelicHomeomorph K n x) :=
    (finiteComponent_adelicHomeomorph K n v x).symm
  have h1' : v₁ ∈ S.erase v₀ := Finset.mem_erase.mpr ⟨Ne.symm h01, h1⟩
  have h2' : v₂ ∈ (S.erase v₀).erase v₁ :=
    Finset.mem_erase.mpr ⟨Ne.symm h12, Finset.mem_erase.mpr ⟨Ne.symm h02, h2⟩⟩
  have hprod : (∏ v : S, F v (finiteComponent K n v
        (GeneralLinearGroupPoints.adelicHomeomorph K n x))) =
      F v₀ (finiteComponent K n v₀ (GeneralLinearGroupPoints.adelicHomeomorph K n x)) *
        (F v₁ (finiteComponent K n v₁ (GeneralLinearGroupPoints.adelicHomeomorph K n x)) *
        (F v₂ (finiteComponent K n v₂ (GeneralLinearGroupPoints.adelicHomeomorph K n x)) *
          ∏ v ∈ ((S.erase v₀).erase v₁).erase v₂,
            F v (finiteComponent K n v (GeneralLinearGroupPoints.adelicHomeomorph K n x)))) := by
    rw [Finset.prod_coe_sort S (fun v => F v (finiteComponent K n v
        (GeneralLinearGroupPoints.adelicHomeomorph K n x))),
      ← Finset.mul_prod_erase S _ h0, ← Finset.mul_prod_erase _ _ h1',
      ← Finset.mul_prod_erase _ _ h2']
  unfold fullTest threePlaceTensor fullTestExterior
  rw [adelicTestTensor_finiteTest, hprod]
  simp only [hc]
  ring

/-- The exterior part is invariant under right insertion at each of the three places. -/
theorem fullTestExterior_mul_finitePlacePointInclusion (a : ArchimedeanGL.SmoothCompactKernel K n)
    (v₀ v₁ v₂ v : Langlands.Global.FinitePlace K) (hv : v ∈ S)
    (hv' : v = v₀ ∨ v = v₁ ∨ v = v₂) (z : AdelicGroupPoints K GLG)
    (y : PlaceGroupPoints K GLG (.inr v)) :
    fullTestExterior K n S F a v₀ v₁ v₂ (z * finitePlacePointInclusion K GLG v y) =
      fullTestExterior K n S F a v₀ v₁ v₂ z := by
  let k : FiniteLocalGL K n v := GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n)
    (CommRingCat.of K) (placeCompletion K (.inr v)) y
  have hg : GeneralLinearGroupPoints.adelicHomeomorph K n (z * finitePlacePointInclusion K GLG v y) =
      GeneralLinearGroupPoints.adelicHomeomorph K n z * includeFinite K n v k := by
    rw [map_mul, finitePlacePointInclusion_eq_ofPlace, adelicHomeomorph_ofPlace]
  have haway : awayComponent K n S (includeFinite K n v k) = 1 := by
    apply RestrictedProduct.ext
    intro w
    have hw : w.val ≠ v := fun he => w.property (he.symm ▸ hv)
    rw [awayComponent_apply, finiteComponent_includeFinite_of_ne K n hw]
    rfl
  have hmem : v ∉ ((S.erase v₀).erase v₁).erase v₂ := by
    simp only [Finset.mem_erase]
    rcases hv' with h | h | h <;> subst h <;> tauto
  unfold fullTestExterior
  simp only [hg, map_mul, infinite_includeFinite, mul_one, haway]
  congr 2
  apply Finset.prod_congr rfl
  intro w hw
  have hwv : w ≠ v := fun h => hmem (h ▸ hw)
  rw [finiteComponent_includeFinite_of_ne K n hwv, mul_one]

end GroupScheme

end Langlands.TraceFormula.GlobalizationTensor
