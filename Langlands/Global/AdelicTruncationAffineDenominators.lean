import Langlands.Global.AdelicTruncationRegularization
import Langlands.Global.AdelicTruncatedEisensteinPairing
import Langlands.Global.AdelicEisensteinStandardizationReduction
import Langlands.Analysis.Meromorphic.RootHyperplanePoles

/-! # Genericity and local division for the affine coroot denominators -/

noncomputable section

open Set Filter Topology Metric CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace Langlands.Global.ImaginaryAxis

variable {n : ℕ} {I : Type*}

private def imaginarySliceLinearMap :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℂ) where
  toFun := imaginarySlice
  map_add' x y := by
    ext j
    simp [imaginarySlice, Complex.ofReal_add, mul_add]
  map_smul' r x := by
    ext j
    simp [imaginarySlice, Complex.real_smul, mul_left_comm]

private theorem dense_ne_zero_affine {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ℓ : X →ₗ[ℝ] ℂ) (b : ℂ) (hne : ∃ x, ℓ x + b ≠ 0) :
    Dense {x | ℓ x + b ≠ 0} := by
  rw [dense_iff_inter_open]
  intro V hV hVne
  obtain ⟨v, hv⟩ := hVne
  by_cases h₀ : ℓ v + b ≠ 0
  · exact ⟨v, hv, h₀⟩
  obtain ⟨w, hw⟩ := hne
  let f : ℝ → X := fun t => v + t • (w - v)
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hV' : IsOpen (f ⁻¹' V) := hV.preimage hf
  have hmem : (0 : ℝ) ∈ f ⁻¹' V := by simpa [f] using hv
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV' 0 hmem
  have hhalf : r / 2 ∈ ball (0 : ℝ) r := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  refine ⟨f (r / 2), hball hhalf, ?_⟩
  change ℓ (v + (r / 2) • (w - v)) + b ≠ 0
  have hv₀ : ℓ v + b = 0 := not_not.mp h₀
  rw [map_add, map_smul, map_sub, show ℓ w - ℓ v = (ℓ w + b) - (ℓ v + b) by abel,
    hv₀, sub_zero, add_comm (ℓ v), add_assoc, hv₀, add_zero]
  exact smul_ne_zero (by positivity) hw

/-- The complement of the union of the zero sets of the finite affine denominators. -/
def affineNonzeroRegion (ℓ : I → (Fin n → ℂ) →ₗ[ℂ] ℂ) (b : I → ℂ) :
    Set (Fin n → ℂ) :=
  {s | ∀ i, ℓ i s + b i ≠ 0}

/-- A nonvanishing witness on the imaginary slice for each factor gives open dense
nonvanishing regions on complex coordinates and on the imaginary slice. -/
theorem affineNonzeroRegion_open_dense [Finite I]
    (ℓ : I → (Fin n → ℂ) →ₗ[ℂ] ℂ) (b : I → ℂ)
    (hne : ∀ i, ∃ x : Fin n → ℝ, ℓ i (imaginarySlice x) + b i ≠ 0) :
    IsOpen (affineNonzeroRegion ℓ b) ∧ Dense (affineNonzeroRegion ℓ b) ∧
      IsOpen (imaginarySlice ⁻¹' affineNonzeroRegion ℓ b) ∧
      Dense (imaginarySlice ⁻¹' affineNonzeroRegion ℓ b) := by
  let V : I → Set (Fin n → ℂ) := fun i => {s | ℓ i s + b i ≠ 0}
  have hV : affineNonzeroRegion ℓ b = ⋂ i, V i := by
    ext s
    change (∀ i, s ∈ V i) ↔ s ∈ ⋂ i, V i
    rw [mem_iInter]
  have ho (i : I) : IsOpen (V i) :=
    isOpen_ne_fun ((ℓ i).continuous_of_finiteDimensional.add continuous_const) continuous_const
  have hvo : IsOpen (⋂ i, V i) := isOpen_iInter_of_finite ho
  rw [hV]
  refine ⟨hvo, dense_iInter_of_isOpen ho ?_, hvo.preimage continuous_imaginarySlice, ?_⟩
  · intro i
    obtain ⟨x, hx⟩ := hne i
    exact dense_ne_zero_affine ((ℓ i).restrictScalars ℝ) (b i) ⟨imaginarySlice x, hx⟩
  · rw [preimage_iInter]
    apply dense_iInter_of_isOpen (fun i => (ho i).preimage continuous_imaginarySlice)
    intro i
    exact dense_ne_zero_affine (((ℓ i).restrictScalars ℝ).comp imaginarySliceLinearMap) (b i)
      (hne i)

/-- A cleared expression with finite affine factors gives the centered local denominator
presentation on the imaginary axis. Repeated indices allow powers of the same factor. -/
theorem hasImaginaryHyperplanePresentation_of_affine_product [Fintype I]
    (ℓ : I → (Fin n → ℂ) →ₗ[ℂ] ℂ) (b : I → ℂ)
    (hreal : ∀ i (x : Fin n → ℝ), (ℓ i (fun j => (x j : ℂ))).im = 0)
    (hne : ∀ i, ∃ x : Fin n → ℝ, ℓ i (imaginarySlice x) + b i ≠ 0)
    {f h : (Fin n → ℂ) → ℂ} {D U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (him : Set.range (imaginarySlice (n := n)) ⊆ U) (hhol : DifferentiableOn ℂ h U)
    (hEq : EqOn h (fun s => (∏ i, (ℓ i s + b i)) * f s) (U ∩ D)) :
    HasImaginaryHyperplanePresentation f D := by
  classical
  rintro _ ⟨x₀, rfl⟩
  let s₀ := imaginarySlice x₀
  let d := fun (i : I) (s : Fin n → ℂ) => ℓ i s + b i
  let B := {i : I // d i s₀ = 0}
  let e := (Fintype.equivFin B).symm
  let V := {i : I // d i s₀ ≠ 0}
  let a := fun s => ∏ i : V, d i.val s
  have ha : Differentiable ℂ a :=
    Langlands.Analysis.Meromorphic.differentiable_finsetProd_apply
      Finset.univ (F := fun i : V => d i.val) fun i _ =>
      (ℓ i.val).toContinuousLinearMap.differentiable.add_const _
  have ha₀ : a s₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => i.property
  let W := U ∩ {s | a s ≠ 0}
  have hW : IsOpen W := hU.inter (isOpen_ne_fun ha.continuous continuous_const)
  have hs₀ : s₀ ∈ W := ⟨him (mem_range_self x₀), ha₀⟩
  have hz (i : B) (s : Fin n → ℂ) : ℓ i.val (s - s₀) = d i.val s := by
    have hb : b i.val = -ℓ i.val s₀ := eq_neg_of_add_eq_zero_right i.property
    rw [map_sub]
    simp only [d, hb, sub_eq_add_neg]
  have hprod (s : Fin n → ℂ) :
      (∏ i, d i s) = (∏ k, ℓ (e k).val (s - s₀)) * a s := by
    rw [Fintype.prod_equiv e _ (fun i : B => d i.val s) (fun k => hz (e k) s)]
    exact (Fintype.prod_subtype_mul_prod_subtype (fun i => d i s₀ = 0) (fun i => d i s)).symm
  refine ⟨Fintype.card B, fun k => ℓ (e k).val, W, fun s => h s / a s,
    fun k => hreal (e k).val, ?_, hW, hs₀, ?_, ?_⟩
  · intro k
    obtain ⟨x, hx⟩ := hne (e k).val
    refine ⟨x - x₀, fun hzero => hx ?_⟩
    have hd : imaginarySlice x - s₀ = Complex.I • (fun j => ((x - x₀) j : ℂ)) := by
      ext j
      simp [s₀, imaginarySlice, Complex.ofReal_sub, mul_sub]
    change d (e k).val (imaginarySlice x) = 0
    rw [← hz, hd, map_smul, hzero, smul_zero]
  · have hh : DifferentiableOn ℂ h W := hhol.mono inter_subset_left
    have hi : DifferentiableOn ℂ (fun s => (a s)⁻¹) W :=
      ha.differentiableOn.inv fun s (hs : s ∈ W) => hs.2
    rw [show (fun s => h s / a s) = h * (fun s => (a s)⁻¹) from
      funext fun s => div_eq_mul_inv _ _]
    exact hh.mul hi
  · intro s hs
    have hne' : a s ≠ 0 := hs.1.2
    change h s / a s = _
    rw [hEq ⟨hs.1.1, hs.2⟩]
    change ((∏ i, d i s) * f s) / a s = (∏ k, ℓ (e k).val (s - s₀)) * f s
    rw [hprod]
    rw [div_eq_iff hne']
    ring

end Langlands.Global.ImaginaryAxis

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Global.AdelicGroupPoints
  Langlands.Global.ImaginaryAxis
open scoped CategoryTheory.MonObj

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (P : StandardIndex F G fam.i fam.ν)
  (L : ∀ Q : StandardIndex F G fam.i fam.ν, fam.AffineExponentLabels P Q) {n : ℕ}
  (ec : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F (fam.P P))

/-- The indices of all affine coroot denominators, including the standard parabolic,
its label, and the relative simple coroot. -/
abbrev AffineCorootIndex :=
  Σ Q : StandardIndex F G fam.i fam.ν, Fin (L Q).size × fam.relativeSimpleRoots Q

instance : Fintype (AffineCorootIndex fam P L) := by
  classical
  let : Finite (StandardIndex F G fam.i fam.ν) :=
    (fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i fam.ν).finite_subsets.to_subtype
  let : Fintype (StandardIndex F G fam.i fam.ν) := Fintype.ofFinite _
  exact Sigma.instFintype

/-- The linear part of a coroot evaluation in the supplied spectral coordinates. -/
def affineCorootLinear (i : AffineCorootIndex fam P L) : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  (complexParameterPairingAt (fam.P i.1) (fam.relativeCoroot i.1 i.2.2)).comp
    (((L i.1).linear i.2.1).comp ec.toLinearMap)

/-- The constant part of the same coroot evaluation. -/
def affineCorootOffset (i : AffineCorootIndex fam P L) : ℂ :=
  fam.corootValue i.1 ((L i.1).offset i.2.1) i.2.2

omit [NumberField F] in
theorem affineCoroot_apply (i : AffineCorootIndex fam P L) (s : Fin n → ℂ) :
    affineCorootLinear fam P L ec i s + affineCorootOffset fam P L i =
      fam.corootValue i.1 ((L i.1).label i.2.1 (ec s)) i.2.2 :=
  ((L i.1).corootValue_label i.2.1 (ec s) i.2.2).symm

omit [NumberField F] in
/-- The published generic parameter region is the nonzero locus of these affine
denominators in the spectral chart. -/
theorem preimage_genericParameterRegion :
    ec ⁻¹' fam.genericParameterRegion P L =
      affineNonzeroRegion (affineCorootLinear fam P L ec) (affineCorootOffset fam P L) := by
  ext s
  constructor
  · rintro hs ⟨Q, k, α⟩
    rw [affineCoroot_apply]
    exact hs Q k α
  · intro hs Q k α
    have h := hs ⟨Q, k, α⟩
    rw [affineCoroot_apply] at h
    exact h

omit [NumberField F] in
/-- A nonvanishing imaginary witness for each label and coroot gives an open dense generic
region in both the imaginary slice and its complex chart. -/
theorem open_dense_genericParameterRegion
    (hne : ∀ Q (k : Fin (L Q).size) (α : fam.relativeSimpleRoots Q), ∃ x : Fin n → ℝ,
      fam.corootValue Q ((L Q).label k (ec (imaginarySlice x))) α ≠ 0) :
    let D := ec ⁻¹' fam.genericParameterRegion P L
    IsOpen D ∧ Dense D ∧ IsOpen (imaginarySlice ⁻¹' D) ∧ Dense (imaginarySlice ⁻¹' D) := by
  dsimp only
  rw [preimage_genericParameterRegion]
  apply affineNonzeroRegion_open_dense
  rintro ⟨Q, k, α⟩
  obtain ⟨x, hx⟩ := hne Q k α
  exact ⟨x, by rwa [affineCoroot_apply]⟩

end Langlands.Global.StandardParabolicFamily
