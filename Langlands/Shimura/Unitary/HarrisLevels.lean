import Langlands.Shimura.Unitary.Adelic
import Langlands.Shimura.Unitary.Domain
import Langlands.Shimura.Levels
import Langlands.Global.CMType
import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Matrix.Basis
import Mathlib.FieldTheory.PrimitiveElement

/-! # CM-compatible signature charts and the actual unitary adelic level tower -/

noncomputable section

universe u v w t

namespace Langlands.Shimura

open CategoryTheory NumberField Algebra
open scoped TensorProduct Classical

section MatrixConj

/-- Entrywise complex conjugation of complex matrices, as a real algebra automorphism. -/
def matrixConj (n : ℕ) : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  Complex.conjAe.mapMatrix

@[simp] theorem matrixConj_apply (n : ℕ) (x : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    matrixConj n x i j = star (x i j) := rfl

theorem matrixConj_signatureMatrix (n r : ℕ) :
    matrixConj n (signatureMatrix n r) = signatureMatrix n r := by
  ext i j
  simp only [matrixConj_apply, signatureMatrix, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem matrixConj_star (n : ℕ) (x : Matrix (Fin n) (Fin n) ℂ) :
    matrixConj n (star x) = star (matrixConj n x) := by
  ext i j
  simp [Matrix.star_apply]

/-- Entrywise conjugation commutes with every diagonal signature adjoint. -/
theorem matrixConj_signatureAdjoint (n r : ℕ) (x : Matrix (Fin n) (Fin n) ℂ) :
    matrixConj n (signatureAdjoint n r x) = signatureAdjoint n r (matrixConj n x) := by
  change matrixConj n (signatureMatrix n r * star x * signatureMatrix n r) =
    signatureMatrix n r * star (matrixConj n x) * signatureMatrix n r
  rw [map_mul, map_mul, matrixConj_signatureMatrix, matrixConj_star]

theorem matrixConj_scalar (n : ℕ) (z : ℂ) :
    matrixConj n (Matrix.scalar (Fin n) z) = Matrix.scalar (Fin n) (star z) := by
  ext i j
  simp only [matrixConj_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

end MatrixConj

variable {E : Type u} {K : Type v} {A : Type w}
variable [Field E] [Field K]
variable [Ring A] [Algebra K A] [Algebra E A]

section Charts

variable {n : ℕ} {τ : E →+* ℝ}

/-- The embedded CM center commutes with the scalar extension. -/
theorem tmul_center_commute (k : K) (x : (letI := τ.toAlgebra; ℝ ⊗[E] A)) :
    letI : Algebra E ℝ := τ.toAlgebra
    x * ((1 : ℝ) ⊗ₜ[E] algebraMap K A k) = ((1 : ℝ) ⊗ₜ[E] algebraMap K A k) * x := by
  let : Algebra E ℝ := τ.toAlgebra
  induction x with
  | tmul r b =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul, Algebra.commutes]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]

/-- A real algebra isomorphism to complex matrices sends the embedded CM center
to scalar matrices. -/
theorem chart_center_mem_range
    (e : (letI := τ.toAlgebra; (ℝ ⊗[E] A) ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ)) (k : K) :
    letI : Algebra E ℝ := τ.toAlgebra
    e ((1 : ℝ) ⊗ₜ[E] algebraMap K A k) ∈ Set.range (Matrix.scalar (Fin n)) := by
  let : Algebra E ℝ := τ.toAlgebra
  rw [← Matrix.center_eq_range, Semigroup.mem_center_iff]
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [← map_mul, ← map_mul, tmul_center_commute]

variable [NeZero n]

theorem chart_center_eq
    (e : (letI := τ.toAlgebra; (ℝ ⊗[E] A) ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ)) (k : K) :
    letI : Algebra E ℝ := τ.toAlgebra
    e ((1 : ℝ) ⊗ₜ[E] algebraMap K A k) =
      Matrix.scalar (Fin n) (e ((1 : ℝ) ⊗ₜ[E] algebraMap K A k) 0 0) := by
  let : Algebra E ℝ := τ.toAlgebra
  obtain ⟨z, hz⟩ := chart_center_mem_range e k
  rw [← hz]
  simp [Matrix.scalar_apply]

/-- The complex embedding of the CM center determined by a chart. -/
def chartCenter
    (e : (letI := τ.toAlgebra; (ℝ ⊗[E] A) ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ)) :
    K →+* ℂ :=
  letI : Algebra E ℝ := τ.toAlgebra
  { toFun := fun k => e ((1 : ℝ) ⊗ₜ[E] algebraMap K A k) 0 0
    map_one' := by
      change e ((1 : ℝ) ⊗ₜ[E] algebraMap K A 1) 0 0 = 1
      rw [map_one, ← Algebra.TensorProduct.one_def, map_one, Matrix.one_apply_eq]
    map_mul' := fun k l => by
      obtain ⟨a, ha⟩ := chart_center_mem_range e k
      obtain ⟨b, hb⟩ := chart_center_mem_range e l
      have hkl : (1 : ℝ) ⊗ₜ[E] algebraMap K A (k * l) =
          ((1 : ℝ) ⊗ₜ[E] algebraMap K A k) * ((1 : ℝ) ⊗ₜ[E] algebraMap K A l) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_mul]
      change e ((1 : ℝ) ⊗ₜ[E] algebraMap K A (k * l)) 0 0 =
        e ((1 : ℝ) ⊗ₜ[E] algebraMap K A k) 0 0 * e ((1 : ℝ) ⊗ₜ[E] algebraMap K A l) 0 0
      rw [hkl, map_mul, ← ha, ← hb]
      simp [Matrix.scalar_apply]
    map_zero' := by
      change e ((1 : ℝ) ⊗ₜ[E] algebraMap K A 0) 0 0 = 0
      rw [map_zero, TensorProduct.tmul_zero, map_zero, Matrix.zero_apply]
    map_add' := fun k l => by
      change e ((1 : ℝ) ⊗ₜ[E] algebraMap K A (k + l)) 0 0 =
        e ((1 : ℝ) ⊗ₜ[E] algebraMap K A k) 0 0 + e ((1 : ℝ) ⊗ₜ[E] algebraMap K A l) 0 0
      rw [map_add, TensorProduct.tmul_add, map_add, Matrix.add_apply] }

theorem chart_center_eq_scalar
    (e : (letI := τ.toAlgebra; (ℝ ⊗[E] A) ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ)) (k : K) :
    letI : Algebra E ℝ := τ.toAlgebra
    e ((1 : ℝ) ⊗ₜ[E] algebraMap K A k) = Matrix.scalar (Fin n) (chartCenter e k) :=
  chart_center_eq e k

/-- On the totally real subfield the chart embedding is the given real embedding. -/
theorem chartCenter_comp [Algebra E K] [IsScalarTower E K A]
    (e : (letI := τ.toAlgebra; (ℝ ⊗[E] A) ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ)) :
    (chartCenter e).comp (algebraMap E K) = Complex.ofRealHom.comp τ := by
  let : Algebra E ℝ := τ.toAlgebra
  ext x
  change e ((1 : ℝ) ⊗ₜ[E] algebraMap K A (algebraMap E K x)) 0 0 = (τ x : ℂ)
  rw [← IsScalarTower.algebraMap_apply E K A x, ← Algebra.TensorProduct.algebraMap_apply',
    IsScalarTower.algebraMap_apply E ℝ (ℝ ⊗[E] A) x, e.commutes]
  simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply_eq, RingHom.algebraMap_toAlgebra]

end Charts

variable [Algebra E K]

variable (E K) in
/-- A CM-type section: one complex embedding of the CM field above each real
embedding of its totally real subfield. -/
def IsCMSection (Φ : (E →+* ℝ) → (K →+* ℂ)) : Prop :=
  ∀ τ : E →+* ℝ, (Φ τ).comp (algebraMap E K) = Complex.ofRealHom.comp τ


variable [NumberField E] [IsTotallyReal E] [NumberField K] [IsTotallyComplex K]
variable [IsQuadraticExtension E K]

section Embeddings

/-- Two complex embeddings of the CM field which agree on the totally real
subfield are equal or complex conjugate. -/
theorem eq_or_eq_conjugate_of_comp_eq (φ ψ : K →+* ℂ)
    (h : ψ.comp (algebraMap E K) = φ.comp (algebraMap E K)) :
    ψ = φ ∨ ψ = ComplexEmbedding.conjugate φ := by
  let : Algebra E ℂ := (φ.comp (algebraMap E K)).toAlgebra
  have : FiniteDimensional E K :=
    Module.finite_of_finrank_eq_succ (IsQuadraticExtension.finrank_eq_two E K)
  have hreal : ∀ x : E, star (φ (algebraMap E K x)) = φ (algebraMap E K x) := fun x =>
    congrArg (fun f : E →+* ℂ => f x)
      (ComplexEmbedding.isReal_iff.mp
        (IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap E K))))
  let φ' : K →ₐ[E] ℂ := { φ with commutes' := fun _ => rfl }
  let ψ' : K →ₐ[E] ℂ :=
    { ψ with commutes' := fun x => congrArg (fun f : E →+* ℂ => f x) h }
  let χ' : K →ₐ[E] ℂ :=
    { ComplexEmbedding.conjugate φ with commutes' := fun x => hreal x }
  have hφχ : φ' ≠ χ' := by
    intro he
    apply IsTotallyComplex.complexEmbedding_not_isReal φ
    rw [ComplexEmbedding.isReal_iff]
    ext k
    exact (congrArg (fun f : K →ₐ[E] ℂ => f k) he).symm
  have hcard : Fintype.card (K →ₐ[E] ℂ) = 2 := by
    rw [AlgHom.card, IsQuadraticExtension.finrank_eq_two]
  by_contra hne
  push Not at hne
  have hψφ : ψ' ≠ φ' := fun he => hne.1 (RingHom.ext fun k => congrArg (fun f => f k) he)
  have hψχ : ψ' ≠ χ' := fun he => hne.2 (RingHom.ext fun k => congrArg (fun f => f k) he)
  have h3 : ({φ', χ', ψ'} : Finset (K →ₐ[E] ℂ)).card = 3 :=
    Finset.card_eq_three.mpr ⟨φ', χ', ψ', hφχ, hψφ.symm, hψχ.symm, rfl⟩
  have := Finset.card_le_univ ({φ', χ', ψ'} : Finset (K →ₐ[E] ℂ))
  omega

end Embeddings

variable [IsScalarTower E K A]

section CenterCompatible

variable {n : ℕ} {τ : E →+* ℝ} [NeZero n]

/-- A signature witness can be chosen complex linear for any prescribed complex
embedding above the real place, by composing with entrywise conjugation. -/
theorem HasSignature.exists_centerCompatible {σ : SecondKindInvolution E K A} {r : ℕ}
    (h : HasSignature σ τ n r) (φ : K →+* ℂ)
    (hφ : φ.comp (algebraMap E K) = Complex.ofRealHom.comp τ) :
    letI : Algebra E ℝ := τ.toAlgebra
    ∃ e : (ℝ ⊗[E] A) ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ,
      (∀ x, e (σ.involution.baseChange ℝ x) = signatureAdjoint n r (e x)) ∧
      ∀ k : K, e ((1 : ℝ) ⊗ₜ[E] algebraMap K A k) = Matrix.scalar (Fin n) (φ k) := by
  let : Algebra E ℝ := τ.toAlgebra
  obtain ⟨-, e, he⟩ := h
  have hc : (chartCenter e).comp (algebraMap E K) = φ.comp (algebraMap E K) := by
    rw [chartCenter_comp, hφ]
  rcases eq_or_eq_conjugate_of_comp_eq φ (chartCenter e) hc with hc' | hc'
  · refine ⟨e, he, fun k => ?_⟩
    rw [chart_center_eq_scalar, hc']
  · refine ⟨e.trans (matrixConj n), fun x => ?_, fun k => ?_⟩
    · rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, he, matrixConj_signatureAdjoint]
    · rw [AlgEquiv.trans_apply, chart_center_eq_scalar, matrixConj_scalar, hc',
        ComplexEmbedding.conjugate_coe_eq]
      simp

end CenterCompatible

/-- Actual algebra charts witnessing the Harris signatures, complex linear for a
specified CM-type section `Φ`. They are isomorphisms of the given scalar-extended
algebra, not independent group data. -/
structure HarrisSignatureCharts (σ : SecondKindInvolution E K A) (n : ℕ)
    (Φ : (E →+* ℝ) → (K →+* ℂ)) where
  rank_gt_one : 1 < n
  distinguished : E →+* ℝ
  equiv (τ : E →+* ℝ) :
    letI : Algebra E ℝ := τ.toAlgebra
    (ℝ ⊗[E] A) ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ
  compatible (τ : E →+* ℝ) :
    letI : Algebra E ℝ := τ.toAlgebra
    ∀ x, equiv τ (σ.involution.baseChange ℝ x) =
      signatureAdjoint n (if τ = distinguished then n - 1 else n) (equiv τ x)
  center (τ : E →+* ℝ) (k : K) :
    letI : Algebra E ℝ := τ.toAlgebra
    equiv τ ((1 : ℝ) ⊗ₜ[E] algebraMap K A k) = Matrix.scalar (Fin n) (Φ τ k)

namespace HarrisSignatureCharts

variable {σ : SecondKindInvolution E K A} {n : ℕ} {Φ : (E →+* ℝ) → (K →+* ℂ)}

/-- Choose actual charts, complex linear for the CM-type section, only after the
signature predicate supplies their existence. No existence of a prescribed
global algebra is assumed here. -/
def ofSignature (h : HasHarrisSignature σ n) (hΦ : IsCMSection E K Φ) :
    HarrisSignatureCharts σ n Φ := by
  classical
  haveI : NeZero n := ⟨by have := h.1; omega⟩
  let τ₀ := h.2.choose
  have hs : ∀ τ : E →+* ℝ,
      HasSignature σ τ n (if τ = τ₀ then n - 1 else n) := by
    intro τ
    by_cases he : τ = τ₀
    · subst τ
      simpa using h.2.choose_spec.1
    · simpa [he] using h.2.choose_spec.2 τ he
  have hc := fun τ => (hs τ).exists_centerCompatible (Φ τ) (hΦ τ)
  exact
    { rank_gt_one := h.1
      distinguished := τ₀
      equiv := fun τ => (hc τ).choose
      compatible := fun τ => (hc τ).choose_spec.1
      center := fun τ => (hc τ).choose_spec.2 }

variable (C : HarrisSignatureCharts σ n Φ)

/-- Evaluate the original algebra in the chart at one real embedding. -/
def component (τ : E →+* ℝ) :
    A →+* Matrix (Fin n) (Fin n) ℂ := by
  letI : Algebra E ℝ := τ.toAlgebra
  exact (C.equiv τ).toRingHom.comp
    (Algebra.TensorProduct.includeRight : A →ₐ[E] ℝ ⊗[E] A).toRingHom

omit [NumberField E] [IsScalarTower E K A] in
theorem component_involution (τ : E →+* ℝ) (a : A) :
    C.component τ (σ.involution a) =
      signatureAdjoint n (if τ = C.distinguished then n - 1 else n)
        (C.component τ a) := by
  let : Algebra E ℝ := τ.toAlgebra
  simpa [component] using C.compatible τ ((1 : ℝ) ⊗ₜ[E] a)

omit [NumberField E] [IsScalarTower E K A] in
/-- The CM center acts through the prescribed complex embedding in every chart. -/
theorem component_center (τ : E →+* ℝ) (k : K) :
    C.component τ (algebraMap K A k) = Matrix.scalar (Fin n) (Φ τ k) := by
  let : Algebra E ℝ := τ.toAlgebra
  exact C.center τ k

/-- Evaluate the actual algebra at all its real embeddings simultaneously. -/
def evaluation : A →+* ((E →+* ℝ) → Matrix (Fin n) (Fin n) ℂ) :=
  RingHom.pi C.component

omit [NumberField E] [IsScalarTower E K A] in
theorem evaluation_center (k : K) :
    C.evaluation (algebraMap K A k) = fun τ => Matrix.scalar (Fin n) (Φ τ k) := by
  funext τ
  exact C.component_center τ k

variable [Algebra ℚ A] [IsScalarTower ℚ E A]

/-- The rational group acts through the real group by its actual algebra charts.
Its multiplier is the same rational scalar in every archimedean factor. -/
def rationalMap :
    σ.rationalInvolution.similitudes →*
      (harrisArchimedeanInvolution n (E →+* ℝ) C.distinguished).similitudes := by
  classical
  apply σ.rationalInvolution.map
    (harrisArchimedeanInvolution n (E →+* ℝ) C.distinguished)
    C.evaluation (algebraMap ℚ ℝ)
  · intro a
    funext τ
    exact C.component_involution τ a
  · intro q
    exact (C.evaluation.map_rat_algebraMap q).trans
      (IsScalarTower.algebraMap_apply ℚ ℝ _ q)

omit [IsScalarTower E K A] in
@[simp] theorem rationalMap_multiplier (g : σ.rationalInvolution.similitudes) :
    (harrisArchimedeanInvolution n (E →+* ℝ) C.distinguished).multiplier
      (C.rationalMap g) =
      Units.map (algebraMap ℚ ℝ).toMonoidHom (σ.rationalInvolution.multiplier g) := rfl

/-- The actual corrected domain, retaining its chart-dependent rational action. -/
def Domain : Type u := by
  classical
  exact StandardArchimedeanDomain n (E →+* ℝ) C.distinguished

instance : TopologicalSpace C.Domain := by
  classical
  exact inferInstanceAs
    (TopologicalSpace (harrisDomainHom n (E →+* ℝ) C.distinguished).Domain)

instance : MulAction σ.rationalInvolution.similitudes C.Domain := by
  classical
  letI : MulAction
      (harrisArchimedeanInvolution n (E →+* ℝ) C.distinguished).similitudes C.Domain :=
    inferInstanceAs
      (MulAction (harrisArchimedeanInvolution n (E →+* ℝ) C.distinguished).similitudes
        (harrisDomainHom n (E →+* ℝ) C.distinguished).Domain)
  exact MulAction.compHom C.Domain C.rationalMap

/-- Simultaneous finite-adelic levels of the given rational unitary algebra,
using the chart-derived rational action on the corrected domain. -/
def tower [Module.Finite ℚ A] :
    CompactOpenLevel σ.rationalInvolution.FiniteAdelicPoints ⥤ TopCat.{max u w} :=
  LevelSpace.tower (X := C.Domain) (ι := σ.rationalInvolution.finiteAdelicDiagonal)

omit [IsScalarTower E K A] in
theorem tower_map_surjective [Module.Finite ℚ A]
    {U V : CompactOpenLevel σ.rationalInvolution.FiniteAdelicPoints} (f : U ⟶ V) :
    Function.Surjective (C.tower.map f) :=
  LevelSpace.translate_surjective f.element f.respects

end HarrisSignatureCharts

variable [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
variable {n : ℕ}

/-- The full central-simple input supplies rational finite dimensionality;
no separate finiteness hypothesis is needed for this Harris specialization.
The charts are complex linear for the supplied CM-type section. -/
def unitaryLevelTower (D : CentralSimpleUnitaryData E K A n)
    (h : HasHarrisSignature D.toSecondKindInvolution n)
    (Φ : (E →+* ℝ) → (K →+* ℂ)) (hΦ : IsCMSection E K Φ) :
    CompactOpenLevel D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints ⥤
      TopCat.{max u w} := by
  letI : FiniteDimensional K A := D.finite
  letI : FiniteDimensional ℚ A := FiniteDimensional.trans ℚ K A
  exact (HarrisSignatureCharts.ofSignature h hΦ).tower

section HarrisCMType

variable (E) {F : Type t} [Field F] [NumberField F] [IsCMField F]
  [IsQuadraticExtension ℚ F]

/-- Harris's CM-type section: above each real embedding of the totally real
field, the unique embedding of the CM field in the CM type of all embeddings
inducing the chosen embedding `τ₀` of the imaginary quadratic subfield. -/
def harrisCMSection (ι : F →+* K) (τ₀ : F →+* ℂ) : (E →+* ℝ) → (K →+* ℂ) :=
  letI : IsCMField K := IsCMField.ofCMExtension E K
  fun τ => (Global.CMType.inducedFromImaginaryQuadratic ι τ₀).embeddingAbove E τ

omit [IsScalarTower E K A] in
theorem isCMSection_harrisCMSection (ι : F →+* K) (τ₀ : F →+* ℂ) :
    IsCMSection E K (harrisCMSection E ι τ₀) := fun τ => by
  let : IsCMField K := IsCMField.ofCMExtension E K
  exact (Global.CMType.inducedFromImaginaryQuadratic ι τ₀).embeddingAbove_restrict E τ

omit [IsScalarTower E K A] in
/-- Every selected embedding induces the chosen embedding of the imaginary
quadratic subfield. -/
theorem harrisCMSection_comp (ι : F →+* K) (τ₀ : F →+* ℂ) (τ : E →+* ℝ) :
    (harrisCMSection E ι τ₀ τ).comp ι = τ₀ := by
  let : IsCMField K := IsCMField.ofCMExtension E K
  exact Global.CMType.induced_embeddingAbove_restrict E ι τ₀ τ

omit [IsScalarTower E K A] in
/-- Every selected embedding is a member of Harris's induced CM type. -/
theorem harrisCMSection_mem (ι : F →+* K) (τ₀ : F →+* ℂ) (τ : E →+* ℝ) :
    letI : IsCMField K := IsCMField.ofCMExtension E K
    harrisCMSection E ι τ₀ τ ∈ Global.CMType.inducedFromImaginaryQuadratic ι τ₀ := by
  let : IsCMField K := IsCMField.ofCMExtension E K
  exact Global.CMType.embeddingAbove_mem E _ τ

omit [IsScalarTower E K A] in
/-- The section involves no choice: it is the only embedding above `τ` that
induces `τ₀`. -/
theorem eq_harrisCMSection (ι : F →+* K) (τ₀ : F →+* ℂ) (τ : E →+* ℝ)
    {φ : K →+* ℂ} (hι : φ.comp ι = τ₀)
    (hτ : φ.comp (algebraMap E K) = Complex.ofRealHom.comp τ) :
    φ = harrisCMSection E ι τ₀ τ := by
  let : IsCMField K := IsCMField.ofCMExtension E K
  exact Global.CMType.eq_embeddingAbove E _ τ hι hτ

variable {E}

/-- The level tower of Harris 1999, Section 4: charts complex linear for the CM
type induced from the chosen embedding `τ₀` of the imaginary quadratic subfield
embedded by `ι`. -/
def harrisUnitaryLevelTower (D : CentralSimpleUnitaryData E K A n)
    (h : HasHarrisSignature D.toSecondKindInvolution n)
    (ι : F →+* K) (τ₀ : F →+* ℂ) :
    CompactOpenLevel D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints ⥤
      TopCat.{max u w} :=
  unitaryLevelTower D h (harrisCMSection E ι τ₀) (isCMSection_harrisCMSection E ι τ₀)

end HarrisCMType

end Langlands.Shimura
