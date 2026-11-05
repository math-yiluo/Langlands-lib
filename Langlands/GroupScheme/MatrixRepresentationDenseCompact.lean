import Langlands.GroupScheme.MatrixRepresentationPositiveForm
import Langlands.GroupScheme.MatrixRepresentationPolynomialImage
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Positive forms from Zariski-dense compact subgroups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open Matrix MeasureTheory
open scoped ComplexOrder

namespace Langlands.Group.DenseCompactForm

variable {𝕜 : Type u} [RCLike 𝕜] {n : Type} [Fintype n] [DecidableEq n]

section Averaging

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {K : Type v} [Group K]

/-- The standard Hermitian form pulled back along the inverse of `φ k`. -/
def pulledForm (φ : K →* GL n 𝕜) (k : K) : Matrix n n 𝕜 :=
  star (((φ k)⁻¹ : GL n 𝕜) : Matrix n n 𝕜) * (((φ k)⁻¹ : GL n 𝕜) : Matrix n n 𝕜)

/-- The Haar average of the pulled-back standard Hermitian forms. -/
def averagedForm [MeasurableSpace K] (μ : Measure K) (φ : K →* GL n 𝕜) : Matrix n n 𝕜 :=
  ∫ k, pulledForm φ k ∂μ

variable {φ : K →* GL n 𝕜}

theorem pulledForm_mul_left (h k : K) :
    pulledForm φ (h⁻¹ * k) =
      star ((φ h : GL n 𝕜) : Matrix n n 𝕜) * (pulledForm φ k * ((φ h : GL n 𝕜) : Matrix n n 𝕜)) := by
  simp only [pulledForm, map_mul, map_inv, _root_.mul_inv_rev, inv_inv, Units.val_mul, star_mul,
    Matrix.mul_assoc]

theorem dotProduct_pulledForm (x : n → 𝕜) (k : K) :
    star x ⬝ᵥ (pulledForm φ k *ᵥ x) =
      ((∑ i, ‖((((φ k)⁻¹ : GL n 𝕜) : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 : ℝ) : 𝕜) := by
  rw [pulledForm, star_eq_conjTranspose, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_conjTranspose, star_star]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
  push_cast
  rfl

variable [TopologicalSpace K]

theorem continuous_pulledForm (hφ : Continuous φ) : Continuous (pulledForm φ) := by
  have h : Continuous fun k => (((φ k)⁻¹ : GL n 𝕜) : Matrix n n 𝕜) :=
    Units.continuous_val.comp (continuous_inv.comp hφ)
  exact (h.matrix_conjTranspose).mul h

variable [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]

theorem integrable_pulledForm (hφ : Continuous φ) : Integrable (pulledForm φ) μ :=
  (continuous_pulledForm hφ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Left invariance of the Haar measure makes the averaged form invariant. -/
theorem star_mul_averagedForm_mul [IsTopologicalGroup K] [μ.IsMulLeftInvariant]
    (hφ : Continuous φ) (h : K) :
    star ((φ h : GL n 𝕜) : Matrix n n 𝕜) * averagedForm μ φ * ((φ h : GL n 𝕜) : Matrix n n 𝕜) =
      averagedForm μ φ := by
  let L : Matrix n n 𝕜 →L[𝕜] Matrix n n 𝕜 :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.mulLeft 𝕜 (star ((φ h : GL n 𝕜) : Matrix n n 𝕜))).comp
        (LinearMap.mulRight 𝕜 ((φ h : GL n 𝕜) : Matrix n n 𝕜)))
  have hL : ∀ M, L M = star ((φ h : GL n 𝕜) : Matrix n n 𝕜) *
      (M * ((φ h : GL n 𝕜) : Matrix n n 𝕜)) := fun M => rfl
  rw [Matrix.mul_assoc, ← hL, averagedForm,
    ← L.integral_comp_comm (integrable_pulledForm (μ := μ) hφ)]
  simp only [hL, ← pulledForm_mul_left]
  exact integral_mul_left_eq_self (pulledForm φ) h⁻¹

theorem isHermitian_averagedForm (hφ : Continuous φ) : (averagedForm μ φ).IsHermitian := by
  let L : Matrix n n 𝕜 →SL[starRingEnd 𝕜] Matrix n n 𝕜 :=
    ⟨(Matrix.conjTransposeLinearEquiv n n 𝕜 𝕜).toLinearMap, continuous_id.matrix_conjTranspose⟩
  have hL : ∀ M, L M = Mᴴ := fun M => rfl
  change (averagedForm μ φ)ᴴ = averagedForm μ φ
  rw [← hL, averagedForm, ← L.integral_comp_commSL
    (fun r x => by simp only [RCLike.real_smul_eq_coe_mul, map_mul, RCLike.conj_ofReal])
    (integrable_pulledForm (μ := μ) hφ)]
  simp only [hL, pulledForm, ← star_eq_conjTranspose, star_mul, star_star]

theorem posDef_averagedForm [μ.IsOpenPosMeasure] (hφ : Continuous φ) :
    (averagedForm μ φ).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (isHermitian_averagedForm μ hφ) fun x hx => ?_
  let ℓ : Matrix n n 𝕜 →L[𝕜] 𝕜 := LinearMap.toContinuousLinearMap
    { toFun := fun M => star x ⬝ᵥ (M *ᵥ x)
      map_add' := fun M N => by simp [add_mulVec, dotProduct_add]
      map_smul' := fun c M => by simp [smul_mulVec, dotProduct_smul] }
  have hℓ : ∀ M, ℓ M = star x ⬝ᵥ (M *ᵥ x) := fun M => rfl
  rw [← hℓ, averagedForm, ← ℓ.integral_comp_comm (integrable_pulledForm (μ := μ) hφ)]
  simp only [hℓ, dotProduct_pulledForm]
  rw [integral_ofReal, RCLike.ofReal_pos]
  have hc : Continuous fun k : K =>
      ∑ i, ‖((((φ k)⁻¹ : GL n 𝕜) : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 := by
    have h : Continuous fun k => (((φ k)⁻¹ : GL n 𝕜) : Matrix n n 𝕜) :=
      Units.continuous_val.comp (continuous_inv.comp hφ)
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp (h.matrix_mulVec continuous_const)).norm.pow 2
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun k => by positivity) (x := 1) ?_
  simp only [map_one, inv_one, Units.val_one, one_mulVec]
  intro h0
  apply hx
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp h0 i
    (Finset.mem_univ i)
  simpa using this

end Averaging

/-- Every compact matrix subgroup preserves some positive definite Hermitian form. -/
theorem exists_posDef_invariant (K₀ : Subgroup (GL n 𝕜))
    (hK : IsCompact (K₀ : Set (GL n 𝕜))) :
    ∃ J : GL n 𝕜, J.val.PosDef ∧ ∀ k ∈ K₀, star k * J * k = J := by
  let : MeasurableSpace K₀ := borel K₀
  have : BorelSpace K₀ := ⟨rfl⟩
  have : CompactSpace K₀ := isCompact_iff_compactSpace.mp hK
  have hφ : Continuous (K₀.subtype : K₀ →* GL n 𝕜) := continuous_subtype_val
  have hJ := posDef_averagedForm (Measure.haar : Measure K₀) hφ
  refine ⟨hJ.isUnit.unit, hJ, fun k hk => Units.ext ?_⟩
  simpa only [Units.val_mul, IsUnit.unit_spec, Units.coe_star, Subgroup.coe_subtype] using
    star_mul_averagedForm_mul (Measure.haar : Measure K₀) hφ ⟨k, hk⟩

section Transfer

open Langlands.GroupScheme.GeneralLinear
open Langlands.Group.AlgebraicMatrixPowers

/-- Polynomials giving the conjugated coordinates of the form adjoint
`J⁻¹ * star g * J` in terms of the coordinates of `g`. -/
def adjointCoordinate (J : GL n 𝕜) : Coordinate n → MvPolynomial (Coordinate n) 𝕜
  | .entry i j => ∑ b, ∑ a,
      MvPolynomial.C (starRingEnd 𝕜 ((J⁻¹ : GL n 𝕜) i a) * starRingEnd 𝕜 (J b j)) *
        MvPolynomial.X (Coordinate.entry b a)
  | .inverseEntry i j => ∑ b, ∑ a,
      MvPolynomial.C (starRingEnd 𝕜 ((J⁻¹ : GL n 𝕜) i a) * starRingEnd 𝕜 (J b j)) *
        MvPolynomial.X (Coordinate.inverseEntry b a)

theorem conj_formAdjoint_apply (J h : GL n 𝕜) (i j : n) :
    starRingEnd 𝕜 ((J⁻¹ * star h * J : GL n 𝕜) i j) =
      ∑ b, ∑ a, starRingEnd 𝕜 ((J⁻¹ : GL n 𝕜) i a) * starRingEnd 𝕜 (J b j) * h b a := by
  simp only [Units.val_mul, Units.coe_star, Matrix.mul_apply, Matrix.star_apply, map_sum,
    map_mul, RCLike.star_def, RCLike.conj_conj, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

theorem eval_adjointCoordinate (J g : GL n 𝕜) (c : Coordinate n) :
    MvPolynomial.eval (values g) (adjointCoordinate J c) =
      starRingEnd 𝕜 (values (J⁻¹ * star g * J) c) := by
  cases c with
  | entry i j =>
    simp only [adjointCoordinate, values, conj_formAdjoint_apply, map_sum, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
  | inverseEntry i j =>
    have h : (J⁻¹ * star g * J)⁻¹ = J⁻¹ * star g⁻¹ * J := by
      rw [star_inv]
      group
    simp only [adjointCoordinate, values, h, conj_formAdjoint_apply, map_sum, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- A polynomial whose value at `g` is the conjugate of the value of `p` at the
form adjoint `J⁻¹ * star g * J`. -/
def adjointPolynomial (J : GL n 𝕜) (p : MvPolynomial (Coordinate n) 𝕜) :
    MvPolynomial (Coordinate n) 𝕜 :=
  MvPolynomial.bind₁ (adjointCoordinate J) (MvPolynomial.map (starRingEnd 𝕜) p)

theorem eval_adjointPolynomial (J g : GL n 𝕜) (p : MvPolynomial (Coordinate n) 𝕜) :
    MvPolynomial.eval (values g) (adjointPolynomial J p) =
      starRingEnd 𝕜 (MvPolynomial.eval (values (J⁻¹ * star g * J)) p) := by
  change MvPolynomial.eval₂Hom (RingHom.id _) _
    (MvPolynomial.bind₁ (adjointCoordinate J) (MvPolynomial.map (starRingEnd 𝕜) p)) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval
    (fun c => MvPolynomial.eval (values g) (adjointCoordinate J c))
    (MvPolynomial.map (starRingEnd 𝕜) p) = _
  have he : (fun c => MvPolynomial.eval (values g) (adjointCoordinate J c)) =
      starRingEnd 𝕜 ∘ values (J⁻¹ * star g * J) :=
    funext (eval_adjointCoordinate J g)
  rw [he, MvPolynomial.eval_map]
  change _ = starRingEnd 𝕜 (MvPolynomial.eval₂ (RingHom.id 𝕜) _ p)
  rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]

/-- If a subgroup is Zariski dense in a polynomially defined matrix group and
preserves the form `J`, then the whole group is stable under the adjoint for `J`. -/
theorem formAdjoint_mem_of_dense (A K₀ : Subgroup (GL n 𝕜)) (hA : IsPolynomiallyDefined A)
    (hKA : K₀ ≤ A)
    (hdense : ∀ p : MvPolynomial (Coordinate n) 𝕜,
      (∀ k ∈ K₀, MvPolynomial.eval (values k) p = 0) →
        ∀ g ∈ A, MvPolynomial.eval (values g) p = 0)
    (J : GL n 𝕜) (hJ : ∀ k ∈ K₀, star k * J * k = J) :
    ∀ g ∈ A, J⁻¹ * star g * J ∈ A := by
  obtain ⟨S, hS⟩ := hA
  intro g hg
  refine (hS _).mpr fun p hp => ?_
  have hk : ∀ k ∈ K₀, MvPolynomial.eval (values k) (adjointPolynomial J p) = 0 := by
    intro k hk
    have hinv : J⁻¹ * star k * J = k⁻¹ :=
      calc J⁻¹ * star k * J = J⁻¹ * (star k * J * k) * k⁻¹ := by group
        _ = k⁻¹ := by rw [hJ k hk]; group
    rw [eval_adjointPolynomial, hinv, (hS _).mp (A.inv_mem (hKA hk)) p hp, map_zero]
  have h := hdense _ hk g hg
  rwa [eval_adjointPolynomial, map_eq_zero] at h

/-- A compact Zariski-dense subgroup of a polynomially defined matrix group
yields a positive definite form for whose adjoint the group is stable. -/
theorem exists_posDef_formAdjoint_of_dense (A K₀ : Subgroup (GL n 𝕜))
    (hA : IsPolynomiallyDefined A) (hKA : K₀ ≤ A)
    (hK : IsCompact (K₀ : Set (GL n 𝕜)))
    (hdense : ∀ p : MvPolynomial (Coordinate n) 𝕜,
      (∀ k ∈ K₀, MvPolynomial.eval (values k) p = 0) →
        ∀ g ∈ A, MvPolynomial.eval (values g) p = 0) :
    ∃ J : GL n 𝕜, J.val.PosDef ∧ (∀ k ∈ K₀, star k * J * k = J) ∧
      ∀ g ∈ A, J⁻¹ * star g * J ∈ A := by
  obtain ⟨J, hJ, hinv⟩ := exists_posDef_invariant K₀ hK
  exact ⟨J, hJ, hinv, formAdjoint_mem_of_dense A K₀ hA hKA hdense J hinv⟩

end Transfer

end Langlands.Group.DenseCompactForm

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.GroupScheme.GeneralLinear
open Langlands.Group.DenseCompactForm Langlands.Group.PositiveFormNormalization

variable {k : Type u} [RCLike k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

local instance matrixRepresentationDenseCompactInst1 : TopologicalSpace (G.affinePoints (CommAlgCat.of k k)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of k k)

/-- A compact subgroup of actual base-field points whose coefficient image is
Zariski dense in the whole coefficient image yields an actual closed
adjoint-stable representation in which that subgroup acts unitarily. -/
theorem exists_closed_starStable_of_denseCompact [IsAffine G.X.left]
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (K₀ : Subgroup (G.affinePoints (CommAlgCat.of k k)))
    (hK : IsCompact (K₀ : Set (G.affinePoints (CommAlgCat.of k k))))
    (hdense : ∀ p : MvPolynomial (Coordinate n) k,
      (∀ x ∈ K₀, MvPolynomial.eval (values (ρ.affineMatrix (CommAlgCat.of k k) x)) p = 0) →
        ∀ x, MvPolynomial.eval (values (ρ.affineMatrix (CommAlgCat.of k k) x)) p = 0) :
    ∃ σ : MatrixRepresentation G n, IsClosedSubgroup σ ∧
      Topology.IsClosedEmbedding (σ.affineMatrix (CommAlgCat.of k k)) ∧
      (∀ g ∈ (σ.affineMatrix (CommAlgCat.of k k)).range,
        star g ∈ (σ.affineMatrix (CommAlgCat.of k k)).range) ∧
      ∀ x ∈ K₀, (σ.affineMatrix (CommAlgCat.of k k) x).val ∈ Matrix.unitaryGroup n k := by
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have hφ := ρ.isClosedEmbedding_affineMatrix (CommAlgCat.of k k) hρ
  have hK₁ : IsCompact ((K₀.map (ρ.affineMatrix (CommAlgCat.of k k)) : Subgroup (GL n k)) :
      Set (GL n k)) := by
    rw [Subgroup.coe_map]
    exact hK.image hφ.continuous
  have hdense₁ : ∀ p : MvPolynomial (Coordinate n) k,
      (∀ g ∈ K₀.map (ρ.affineMatrix (CommAlgCat.of k k)), MvPolynomial.eval (values g) p = 0) →
        ∀ g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range,
          MvPolynomial.eval (values g) p = 0 := by
    rintro p hp _ ⟨x, rfl⟩
    exact hdense p (fun y hy => hp _ ⟨y, hy, rfl⟩) x
  obtain ⟨J, hJ, hinv, hform⟩ := exists_posDef_formAdjoint_of_dense
    (ρ.affineMatrix (CommAlgCat.of k k)).range (K₀.map (ρ.affineMatrix (CommAlgCat.of k k)))
    (ρ.affineMatrix_range_isPolynomiallyDefined k)
    (Subgroup.map_le_range _ K₀) hK₁ hdense₁
  have hσ := ρ.isClosedSubgroup_positiveFormConjugate J hJ hρ
  refine ⟨ρ.positiveFormConjugate J hJ, hσ,
    (ρ.positiveFormConjugate J hJ).isClosedEmbedding_affineMatrix (CommAlgCat.of k k) hσ,
    ρ.star_mem_positiveFormConjugate_range J hJ hform, fun x hx => ?_⟩
  have hk := hinv _ ⟨x, hx, rfl⟩
  rw [positiveFormConjugate_affineMatrix, normalizedHom_apply, Matrix.mem_unitaryGroup_iff',
    ← Units.coe_star, ← Units.val_mul, Units.val_eq_one]
  have hs := star_normalizingMatrix J hJ
  have hsq := normalizingMatrix_mul_self J hJ
  generalize normalizingMatrix J hJ = C at *
  generalize ρ.affineMatrix (CommAlgCat.of k k) x = g at *
  rw [star_mul, star_mul, star_inv, hs]
  calc C⁻¹ * (star g * C) * (C * g * C⁻¹) = C⁻¹ * (star g * (C * C) * g) * C⁻¹ := by group
    _ = 1 := by rw [hsq, hk, ← hsq]; group

end Langlands.GroupScheme.MatrixRepresentation
