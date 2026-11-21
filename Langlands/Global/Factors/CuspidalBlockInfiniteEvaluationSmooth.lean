import Langlands.Global.Factors.CuspidalBlockInfiniteEvaluation
import Langlands.Global.AdelicBlockSmoothCompactSlices
import Mathlib.LinearAlgebra.PiTensorProduct.Finite

/-! # Smooth scalar evaluations of the actual infinite standard tensor -/

noncomputable section

open scoped Classical ContDiff Manifold Matrix.Norms.Operator TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 180000

universe u v w

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic _root_.Langlands.Archimedean LocalFactor.Archimedean
open ArchimedeanCompactBlocks ArchimedeanGL InfinitePlaceFamily NumberField
open AdelicBlockScalarSections (compactMatrix)

private theorem isFiniteVector_comp {H G V : Type*} [Monoid H] [Monoid G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {x : V}
    (h : FiniteVectors.IsFiniteVector ρ x) (e : H →* G) :
    FiniteVectors.IsFiniteVector (ρ.comp e) x := by
  let : FiniteDimensional ℂ (FiniteVectors.orbitSpan ρ x) := h
  apply Submodule.finiteDimensional_of_le (S₂ := FiniteVectors.orbitSpan ρ x)
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact FiniteVectors.action_mem_orbitSpan ρ (e g) x

private theorem isFiniteVector_external {I : Type u} [Finite I]
    {G : I → Type v} [∀ i, Group (G i)] {V : I → Type w}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (G i) (V i))
    (hfin : ∀ i v, FiniteVectors.IsFiniteVector (ρ i) v) (x : ⨂[ℂ] i, V i) :
    FiniteVectors.IsFiniteVector (FiniteTensor.external ρ) x := by
  induction x using PiTensorProduct.induction_on with
  | add x y hx hy => exact hx.add hy
  | smul_tprod c x =>
    apply FiniteVectors.IsFiniteVector.smul _ c
    let U (i : I) := FiniteVectors.orbitSpan (ρ i) (x i)
    let : ∀ i, Module.Finite ℂ (U i) := fun i => hfin i (x i)
    let L : (⨂[ℂ] i, U i) →ₗ[ℂ] (⨂[ℂ] i, V i) := PiTensorProduct.map fun i => (U i).subtype
    let : FiniteDimensional ℂ (LinearMap.range L) :=
      Module.Finite.of_surjective L.rangeRestrict L.surjective_rangeRestrict
    apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L)
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    let y (i : I) : U i := ⟨ρ i (g i) (x i), FiniteVectors.action_mem_orbitSpan (ρ i) (g i) (x i)⟩
    refine ⟨PiTensorProduct.tprod ℂ y, ?_⟩
    exact (PiTensorProduct.map_tprod (fun i => (U i).subtype) y).trans
      (FiniteTensor.external_tprod ρ g x).symm

private theorem standardBlock_scalar_extension {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    {B : GeneralLinear.BlockShape n} {W : Submodule ℂ (GeneralLinear n 𝕜 → ℂ)}
    {V : ∀ i, Submodule ℂ (GeneralLinear (B.size i) 𝕜 → ℂ)}
    (D : StandardBlockEvaluation 𝕜 B W V)
    (ρ : Representation ℂ (unitaryCompact 𝕜 n) W)
    (hρ : ∀ (q : unitaryCompact 𝕜 n) (f : W) (g : GeneralLinear n 𝕜),
      (ρ q f).val g = f.val (g * q.val))
    (f : W) (hfin : FiniteVectors.IsFiniteVector ρ f)
    (hf : ContMDiff (matrixModel 𝕜 n) 𝓘(ℝ, ℂ) ∞ f.val)
    (ℓ : (⨂[ℂ] i, V i) →ₗ[ℂ] ℂ) :
    ∃ φ : Matrix (Fin n) (Fin n) 𝕜 → ℂ,
      (∀ g : GeneralLinear n 𝕜, ContDiffAt ℝ ∞ φ g.val) ∧
      ∀ q : unitaryCompact 𝕜 n, φ q.val.val = ℓ (D.evaluation q f) := by
  obtain ⟨a, m, c, h⟩ := D.exists_sum_of_levi_values ρ hρ f hfin ℓ
  let ψ (j : Fin a) : GeneralLinear n 𝕜 → ℂ := fun g => f.val (B.leviEmbedding 𝕜 (m j) * g)
  refine ⟨fun x => ∑ j, c j * unitsExtension (ψ j) x, fun g => ?_, fun q => ?_⟩
  · apply ContDiffAt.sum
    intro j _
    have hψ : ContMDiff (matrixModel 𝕜 n) 𝓘(ℝ, ℂ) ∞ (ψ j) := hf.comp contMDiff_mul_left
    exact contDiffAt_const.mul ((contDiffOn_unitsExtension hψ).contDiffAt
      (isOpen_setOf_isUnit_matrix.mem_nhds g.isUnit))
  · simp only [unitsExtension_val, ψ]
    exact (h q).symm

private theorem tensor_scalar_extension
    {I : Type u} [Fintype I] {V : I → Type v} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] {K : Type w} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x : E) (p : K → E) (z : ∀ i, K → V i)
    (hfin : ∀ i, ∃ S : Submodule ℂ (V i), FiniteDimensional ℂ S ∧ ∀ q, z i q ∈ S)
    (hsm : ∀ i (ℓ : V i →ₗ[ℂ] ℂ), ∃ φ : E → ℂ,
      ContDiffAt ℝ ∞ φ x ∧ ∀ q, φ (p q) = ℓ (z i q))
    (ℓ : (⨂[ℂ] i, V i) →ₗ[ℂ] ℂ) :
    ∃ φ : E → ℂ, ContDiffAt ℝ ∞ φ x ∧
      ∀ q, φ (p q) = ℓ (PiTensorProduct.tprod ℂ fun i => z i q) := by
  classical
  choose S hS hz using hfin
  let : ∀ i, FiniteDimensional ℂ (S i) := hS
  let J (i : I) := Fin (Module.finrank ℂ (S i))
  let b (i : I) : Module.Basis (J i) ℂ (S i) := Module.finBasis ℂ (S i)
  choose a ha using fun (i : I) (j : J i) => LinearMap.exists_extend ((b i).coord j)
  choose ψ hψ hval using fun (i : I) (j : J i) => hsm i (a i j)
  let t (j : ∀ i, J i) : ⨂[ℂ] i, V i := PiTensorProduct.tprod ℂ fun i => (b i (j i)).val
  refine ⟨fun y => ∑ j : ∀ i, J i, (∏ i, ψ i (j i) y) * ℓ (t j), ?_, fun q => ?_⟩
  · apply ContDiffAt.sum
    intro j _
    apply ContDiffAt.mul _ contDiffAt_const
    exact contDiffAt_prod fun i _ => hψ i (j i)
  · let M := ℓ.compMultilinearMap (PiTensorProduct.tprod ℂ)
    have hexp (i : I) : ∑ j : J i, ψ i j (p q) • (b i j).val = z i q := by
      let s : S i := ⟨z i q, hz i q⟩
      have hs := congrArg (S i).subtype ((b i).sum_repr s)
      have he (j : J i) : ψ i j (p q) = (b i).repr s j :=
        (hval i j q).trans (LinearMap.congr_fun (ha i j) s)
      simpa only [he, map_sum, map_smul, Submodule.subtype_apply] using hs
    have hm := M.map_sum (fun (i : I) (j : J i) => ψ i j (p q) • (b i j).val)
    simp only [hexp, MultilinearMap.map_smul_univ, smul_eq_mul] at hm
    exact hm.symm

private theorem tensor_map_scalar_extension
    {I : Type u} [Fintype I] {V : I → Type v} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] {W : I → Type w} [∀ i, AddCommGroup (W i)]
    [∀ i, Module ℂ (W i)] {K E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x : E) (p : K → E) (e : ∀ i, K → V i →ₗ[ℂ] W i)
    (hfin : ∀ i a, ∃ S : Submodule ℂ (W i), FiniteDimensional ℂ S ∧ ∀ q, e i q a ∈ S)
    (hsm : ∀ i a (ℓ : W i →ₗ[ℂ] ℂ), ∃ φ : E → ℂ,
      ContDiffAt ℝ ∞ φ x ∧ ∀ q, φ (p q) = ℓ (e i q a))
    (a : ⨂[ℂ] i, V i) (ℓ : (⨂[ℂ] i, W i) →ₗ[ℂ] ℂ) :
    ∃ φ : E → ℂ, ContDiffAt ℝ ∞ φ x ∧
      ∀ q, φ (p q) = ℓ (PiTensorProduct.map (fun i => e i q) a) := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod c a =>
    obtain ⟨φ, hφ, he⟩ := tensor_scalar_extension x p
      (fun i q => e i q (a i)) (fun i => hfin i (a i)) (fun i => hsm i (a i)) ℓ
    refine ⟨fun y => c * φ y, contDiffAt_const.mul hφ, fun q => ?_⟩
    dsimp only
    rw [he, map_smul, map_smul, smul_eq_mul, PiTensorProduct.map_tprod]
  | add a b h₁ h₂ =>
    obtain ⟨φ, hφ, he⟩ := h₁
    obtain ⟨ψ, hψ, hh⟩ := h₂
    refine ⟨fun y => φ y + ψ y, hφ.add hψ, fun q => ?_⟩
    dsimp only
    rw [he, hh, map_add, map_add]

variable {F : Type u} [Field F] [NumberField F]
variable {r k : ℕ}
variable (real : {v : InfinitePlace F // v.IsReal} → Fin k → List RealBlock)
variable (complex : {v : InfinitePlace F // v.IsComplex} → Fin k → List ComplexCharacterData)

local notation "A" => infiniteStandardSpace r real complex
local notation "flat" => (fun d => List.flatten (List.ofFn d))

theorem infiniteStandardLocalAction_isFiniteVector (i : Index F) (a : A i) :
    FiniteVectors.IsFiniteVector (infiniteStandardLocalAction r real complex i) a := by
  cases i with
  | inl v => exact (isRealGKModule_realStandardModule (r + 1) (flat (real v))).1 a
  | inr v => exact (isComplexGKModule_complexStandardModule (r + 1) (flat (complex v))).1 a

/-- The original-order tensor is compact-finite for the actual infinite compact group. -/
theorem infiniteStandardAction_isFiniteVector (a : ⨂[ℂ] i, A i) :
    FiniteVectors.IsFiniteVector (infiniteStandardAction r real complex) a :=
  isFiniteVector_comp
    (isFiniteVector_external (infiniteStandardLocalAction r real complex)
      (infiniteStandardLocalAction_isFiniteVector real complex) a)
    (infiniteCompactCoordinates F (r + 1)).toMonoidHom

variable [CompactSpace (AdeleQuotient F)] {m : Fin k → ℕ}
variable (hm : ∑ i, (m i + 1) = r + 1)
variable (T : ∀ i, CuspidalOperatorRealization F (m i))
variable (hr : ∀ v i, (T i).realization.HasRealPlaceParameter v (real v i))
variable (hc : ∀ v i, (T i).realization.HasComplexPlaceParameter v (complex v i))

private local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance {n : ℕ} (R : OperatorRealization F n) : AddCommGroup R.Space := Submodule.addCommGroup _
private local instance (i : Fin k) (p : Index F) : AddCommGroup ((T i).placeDensityModels.subspace p) :=
  Submodule.addCommGroup _

local notation "C" => (fun p : Index F => ⨂[ℂ] i, OperatorRealization.PlaceDensityModels.subspace
  (CuspidalOperatorRealization.placeDensityModels (T i)) p)
local notation "B" =>
  GeneralLinear.BlockShape.mk k (fun i => m i + 1) (fun i => Nat.succ_pos (m i)) hm
local notation "K" => standardInfiniteCompact F (r + 1)
local notation "E" => ArchimedeanMatrix F (r + 1)
local notation "e" => infiniteLocalEvaluation real complex hm T hr hc
local notation "coords" => infiniteCompactCoordinates F (r + 1)

set_option backward.isDefEq.respectTransparency true in
private theorem infiniteLocalEvaluation_scalar_extension (i : Index F) (a : A i)
    (ℓ : C i →ₗ[ℂ] ℂ) (q : K) :
    ∃ φ : E → ℂ, ContDiffAt ℝ ∞ φ (compactMatrix F q) ∧
      ∀ t : K, φ (compactMatrix F t) = ℓ (e i (coords t i) a) := by
  cases i with
  | inl v =>
    change realStandardKFinite (r + 1) (flat (real v)) at a
    let ds := flat (real v)
    let D := realStandardBlockEvaluationOfShape B (real v) (fun i => (hr v i).1)
    let ρ := realCompactAction (r + 1) ds
    let ℓ₀ : (⨂[ℂ] j, realStandardKFinite (m j + 1) (real v j)) →ₗ[ℂ] ℂ :=
      ℓ.comp (realCoefficientTensorEquiv T v (real v) (hr v)).toLinearMap
    have hfin : FiniteVectors.IsFiniteVector ρ a :=
      isFiniteVector_comp ((isRealGKModule_realStandardModule (r + 1) ds).1 a) _
    have hsm := contMDiff_of_mem_realStandardModule a.2.1
    have h_ext := @standardBlock_scalar_extension ℝ _ (r + 1) B
      (realStandardKFinite (r + 1) ds) (fun j => realStandardKFinite (m j + 1) (real v j))
      D ρ (realCompactAction_apply (r + 1) ds) a hfin hsm ℓ₀
    obtain ⟨ψ, hψ, hval⟩ := h_ext
    let p : E →L[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
      ((realPlaceScalarProjection F v).mapMatrix).toLinearMap.toContinuousLinearMap
    have hp (t : K) :
        (matrixUnitaryToCompact ℝ (r + 1) (coords t (.inl v))).val.val = p (compactMatrix F t) :=
      infiniteCompactCoordinates_apply_real F (r + 1) t v
    refine ⟨ψ ∘ p, ?_, fun t => ?_⟩
    · exact ((hp q) ▸ hψ ((matrixUnitaryToCompact ℝ (r + 1) (coords q (.inl v))).val)).comp _
        p.contDiff.contDiffAt
    · exact (congrArg ψ (hp t).symm).trans (hval (matrixUnitaryToCompact ℝ (r + 1) (coords t (.inl v))))
  | inr v =>
    change complexStandardKFinite (r + 1) (flat (complex v)) at a
    let ds := flat (complex v)
    let D := complexStandardBlockEvaluationOfShape B (complex v) (fun i => (hc v i).1)
    let ρ := complexCompactAction (r + 1) ds
    let ℓ₀ : (⨂[ℂ] j, complexStandardKFinite (m j + 1) (complex v j)) →ₗ[ℂ] ℂ :=
      ℓ.comp (complexCoefficientTensorEquiv T v (complex v) (hc v)).toLinearMap
    have hfin : FiniteVectors.IsFiniteVector ρ a :=
      isFiniteVector_comp ((isComplexGKModule_complexStandardModule (r + 1) ds).1 a) _
    have hsm := a.2.1.1
    have h_ext := @standardBlock_scalar_extension ℂ _ (r + 1) B
      (complexStandardKFinite (r + 1) ds) (fun j => complexStandardKFinite (m j + 1) (complex v j))
      D ρ (complexCompactAction_apply (r + 1) ds) a hfin hsm ℓ₀
    obtain ⟨ψ, hψ, hval⟩ := h_ext
    let p : E →L[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
      ((complexPlaceScalarProjection F v).mapMatrix).toLinearMap.toContinuousLinearMap
    have hp (t : K) :
        (matrixUnitaryToCompact ℂ (r + 1) (coords t (.inr v))).val.val = p (compactMatrix F t) :=
      infiniteCompactCoordinates_apply_complex F (r + 1) t v
    refine ⟨ψ ∘ p, ?_, fun t => ?_⟩
    · exact ((hp q) ▸ hψ ((matrixUnitaryToCompact ℂ (r + 1) (coords q (.inr v))).val)).comp _
        p.contDiff.contDiffAt
    · exact (congrArg ψ (hp t).symm).trans (hval (matrixUnitaryToCompact ℂ (r + 1) (coords t (.inr v))))

private theorem infiniteLocalEvaluation_finiteRange (i : Index F) (a : A i) :
    ∃ S : Submodule ℂ (C i), FiniteDimensional ℂ S ∧ ∀ q : K, e i (coords q i) a ∈ S := by
  let ρ := infiniteStandardLocalAction r real complex i
  let U := FiniteVectors.orbitSpan ρ a
  let : FiniteDimensional ℂ U := infiniteStandardLocalAction_isFiniteVector real complex i a
  refine ⟨U.map (e i 1), inferInstance, fun t => ?_⟩
  let d := coords t i
  refine ⟨ρ d a, FiniteVectors.action_mem_orbitSpan ρ d a, ?_⟩
  exact (infiniteLocalEvaluation_right real complex hm T hr hc i 1 d a).trans
    (congrArg (fun g => e i g a) (one_mul d))

private theorem exists_infiniteEvaluationScalarExtension (a : ⨂[ℂ] i, A i)
    (ℓ : (⨂[ℂ] i, C i) →ₗ[ℂ] ℂ) (q : K) :
    ∃ φ : E → ℂ, ContDiffAt ℝ ∞ φ (compactMatrix F q) ∧
      ∀ t : K, φ (compactMatrix F t) = ℓ (infiniteEvaluation real complex hm T hr hc t a) := by
  classical
  let : Fintype (Index F) := Fintype.ofFinite _
  exact tensor_map_scalar_extension (I := Index F) (V := A) (W := C)
    (compactMatrix F q) (compactMatrix F) (fun i t => e i (coords t i))
    (infiniteLocalEvaluation_finiteRange real complex hm T hr hc)
    (fun i b L => infiniteLocalEvaluation_scalar_extension real complex hm T hr hc i b L q)
    a ℓ

/-- A scalar extension of the infinite compact evaluation, smooth near the
chosen compact matrix. -/
def infiniteEvaluationScalarExtension (a : ⨂[ℂ] i, A i)
    (ℓ : (⨂[ℂ] i, C i) →ₗ[ℂ] ℂ) (q : K) :
    {φ : E → ℂ // ContDiffAt ℝ ∞ φ (compactMatrix F q) ∧
      ∀ t : K, φ (compactMatrix F t) = ℓ (infiniteEvaluation real complex hm T hr hc t a)} :=
  let h := exists_infiniteEvaluationScalarExtension real complex hm T hr hc a ℓ q
  ⟨h.choose, h.choose_spec⟩

end Langlands.Global.CuspidalBlockInduction
