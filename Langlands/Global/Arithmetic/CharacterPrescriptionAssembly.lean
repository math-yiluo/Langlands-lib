import Langlands.Global.Arithmetic.PrescriptionFiniteQuotientStatement
import Langlands.Global.HeckeCharacterFiniteOrder
import Langlands.Topology.FiniteQuotientCharacterExtension

/-! # Local kernels and the finite-quotient reduction for prescription -/

noncomputable section

universe u v

namespace Langlands.Global

/-- The kernel of a continuous complex character with positive bounded order,
viewed as an open subgroup. -/
def complexCharacterOpenKernel
    {A : Type v} [CommGroup A] [TopologicalSpace A]
    (η : A →ₜ* ℂˣ) (n : ℕ) (hn : 0 < n) (hη : η ^ n = 1) :
    OpenSubgroup A where
  toSubgroup := η.toMonoidHom.ker
  isOpen' := by
    apply (isLocallyConstant_of_complexUnits_pow_eq_one (f := fun a => η a) η.continuous hn
      (fun a => ?_)).isOpen_fiber 1
    simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun, Pi.one_apply] using
      DFunLike.congr_fun hη a

theorem complexCharacterOpenKernel_finiteIndex
    {A : Type v} [CommGroup A] [TopologicalSpace A]
    (η : A →ₜ* ℂˣ) (n : ℕ) (hn : 0 < n) (hη : η ^ n = 1) :
    (complexCharacterOpenKernel η n hn hη).toSubgroup.FiniteIndex := by
  let : NeZero n := ⟨hn.ne'⟩
  have hmem (a : A) : η a ∈ rootsOfUnity n ℂ := by
    apply (mem_rootsOfUnity n (η a)).mpr
    simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun, Pi.one_apply] using
      DFunLike.congr_fun hη a
  let η' := η.toMonoidHom.codRestrict (rootsOfUnity n ℂ) hmem
  have hfinite : η'.ker.FiniteIndex := inferInstance
  change η.toMonoidHom.ker.FiniteIndex
  simpa only [η', MonoidHom.ker_codRestrict] using hfinite

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))

theorem prescriptionLocalCharacter_pow_eq_one
    (η : (v : {v // v ∈ S}) → (FiniteCompletion K v.1)ˣ →ₜ* ℂˣ)
    (ηInf : (InfiniteAdeles K)ˣ →ₜ* ℂˣ)
    (n : ℕ) (hη : ∀ v, η v ^ n = 1) (hInf : ηInf ^ n = 1) :
    prescriptionLocalCharacter K S η ηInf ^ n = 1 := by
  classical
  apply ContinuousMonoidHom.ext
  intro a
  have hi : ηInf a.1 ^ n = 1 := by
    simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun, Pi.one_apply] using
      DFunLike.congr_fun hInf a.1
  have hv (v : {v // v ∈ S}) : η v (a.2 v) ^ n = 1 := by
    simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun, Pi.one_apply] using
      DFunLike.congr_fun (hη v) (a.2 v)
  simp only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun]
  change (ηInf a.1 * ∏ v, η v (a.2 v)) ^ n = 1
  rw [mul_pow, ← Finset.prod_pow]
  simp [hi, hv]

set_option maxHeartbeats 800000 in
/-- The remaining arithmetic finite-quotient assertion suffices for the
unchanged prescription statement. -/
theorem finiteOrderCharacterPrescription_of_finiteQuotient
    (hquot : PrescriptionFiniteQuotientStatement.{u}) :
    FiniteOrderCharacterPrescriptionStatement.{u} := by
  classical
  intro K _ _ S n hn η ηInf hη hInf
  let θ := prescriptionLocalCharacter K S η ηInf
  have hθ : θ ^ n = 1 := prescriptionLocalCharacter_pow_eq_one K S η ηInf n hη hInf
  let U := complexCharacterOpenKernel θ n hn hθ
  have hU : U.toSubgroup.FiniteIndex :=
    complexCharacterOpenKernel_finiteIndex θ n hn hθ
  have hpU (a : PrescriptionLocalProduct K S) : a ^ n ∈ U := by
    change θ (a ^ n) = 1
    rw [map_pow]
    simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun, Pi.one_apply] using
      DFunLike.congr_fun hθ a
  obtain ⟨N, hNfinite, hNpow, hNpre⟩ := hquot K S n hn U hU hpU
  let : N.toSubgroup.FiniteIndex := hNfinite
  have hker : N.toSubgroup.comap (prescriptionClassMap K S).toMonoidHom ≤
      θ.toMonoidHom.ker := by
    rw [hNpre]
    exact le_refl _
  obtain ⟨χ, hχpow, hχcomp⟩ :=
    Langlands.Topology.exists_character_of_open_finite_quotient
      (A := PrescriptionLocalProduct K S) (C := IdeleClasses K)
      (prescriptionClassMap K S) θ N.toSubgroup N.isOpen' (2 * n) hNpow hker
  refine ⟨χ, hχpow, ?_, ?_⟩
  · intro v
    apply ContinuousMonoidHom.ext
    intro a
    have h := DFunLike.congr_fun hχcomp
      ((1 : (InfiniteAdeles K)ˣ),
        Pi.mulSingle (M := fun w : {v // v ∈ S} => (FiniteCompletion K w.1)ˣ) v a)
    change χ (prescriptionClassMap K S (1, Pi.mulSingle v a)) =
      θ (1, Pi.mulSingle v a) at h
    change χ (finiteClassInclusion K v.1 a) = η v a
    simpa only [θ, prescriptionClassMap_finite, prescriptionLocalCharacter_finite] using h
  · apply ContinuousMonoidHom.ext
    intro a
    have h := DFunLike.congr_fun hχcomp (a, 1)
    change χ (prescriptionClassMap K S (a, 1)) = θ (a, 1) at h
    change χ (ideleClassMap K (infiniteIdelesInclusion K a)) = ηInf a
    simpa only [θ, prescriptionClassMap_infinity, prescriptionLocalCharacter_infinity] using h

end Langlands.Global
