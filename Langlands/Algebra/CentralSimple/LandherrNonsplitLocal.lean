import Langlands.Algebra.CentralSimple.LandherrNonsplitChart

/-! # Hermitian charts and reduced-norm-one solutions at a nonsplit completion -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root Langlands.Shimura
  Langlands.Shimura.FiniteUnitary
open scoped TensorProduct

universe u

variable (F E : Type u) [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CharZero F]
  (B : Type u) [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
  (K : Type u) [Field K] [Algebra F K] [hK : Fact (¬ IsSquare (algebraMap F K (skewSq F E)))]

attribute [local instance] nonsplitAlgebra nonsplit_isScalarTower nonsplit_smulCommClass

/-- The relative reduced norm with arbitrary (not necessarily invertible) arguments. -/
def relNorm (R : Type u) [CommRing R] [Algebra F R] (z : R ⊗[F] B) : E ⊗[F] R :=
  reducedNorm E B (E ⊗[F] R) (UnitaryPoints.tensorEquiv F E B R z)

theorem nonsplitCenterEquiv_relNorm (z : K ⊗[F] B) :
    nonsplitCenterEquiv F E K (relNorm F E B K z) =
      reducedNorm E B (nonsplitField F E K) (nonsplitEquiv F E B K z) := by
  have h := reducedNorm_naturality E B (nonsplitCenterEquiv F E K).toAlgHom
    (UnitaryPoints.tensorEquiv F E B K z)
  rw [map_nonsplitCenterEquiv_tensorEquiv] at h
  exact h.symm

/-- The conjugation of `K(√d)` as a ring endomorphism. -/
abbrev nonsplitConjHom : nonsplitField F E K →+* nonsplitField F E K :=
  (nonsplitConj F E K).toAlgHom.toRingHom

omit hK in
theorem nonsplitConjHom_apply (x : nonsplitField F E K) : nonsplitConjHom F E K x = star x := rfl

omit hK in
theorem nonsplitConjHom_involutive (x : nonsplitField F E K) :
    nonsplitConjHom F E K (nonsplitConjHom F E K x) = x := by
  simp

/-- The conjugation of `K(√d)` as an algebra involution over `K`. -/
def nonsplitConjInvolution : AlgebraInvolution K (nonsplitField F E K) where
  linear := (nonsplitConj F E K).toLinearEquiv.toLinearMap
  map_one := map_one (nonsplitConj F E K)
  map_mul a b := by
    change nonsplitConj F E K (a * b) = nonsplitConj F E K b * nonsplitConj F E K a
    rw [map_mul, mul_comm]
  involutive a := by
    change nonsplitConj F E K (nonsplitConj F E K a) = a
    simp

omit hK in
theorem nonsplit_exists_conj_ne : ∃ a : nonsplitField F E K, nonsplitConjHom F E K a ≠ a := by
  by_contra h
  push Not at h
  exact nonsplitConj_ne_one F E K (AlgEquiv.ext fun a => h a)

omit hK in
theorem nonsplit_isQuadratic : Algebra.IsQuadraticExtension K (nonsplitField F E K) :=
  ⟨QuadraticAlgebra.finrank_eq_two _ _⟩

theorem nonsplit_isSeparable : Algebra.IsSeparable K (nonsplitField F E K) := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have := nonsplit_isQuadratic F E K
  have : FiniteDimensional K (nonsplitField F E K) :=
    Module.finite_of_finrank_eq_succ (QuadraticAlgebra.finrank_eq_two _ _)
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

local notation "Mat" => Matrix (Fin (reducedDegree E B)) (Fin (reducedDegree E B))
  (nonsplitField F E K)

variable (τ : FirstKindInvolution F B)
  (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e))

include hτ in
/-- Let `τ` act on `E` by quadratic conjugation and let `K` have the unitary splitting
property with `skewSq F E` nonsquare in `K`. There is a splitting chart of
`K(√d) ⊗_E B` in which the transported involution is adjoint to an invertible Hermitian
matrix. -/
theorem exists_nonsplit_chart (hS : UnitaryInvolutionSplitting K) :
    ∃ (e : nonsplitAlg F E B K ≃ₐ[nonsplitField F E K] Mat) (H : Matˣ),
      Landherr.ct (nonsplitConjHom F E K) (H : Mat) = H ∧
      ∀ z, e (nonsplitInvolution F E B K τ z) =
        (↑H⁻¹ : Mat) * Landherr.ct (nonsplitConjHom F E K) (e z) * (H : Mat) := by
  classical
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have := nonsplit_isQuadratic F E K
  have := nonsplit_isSeparable F E K
  have : IsSimpleRing (nonsplitAlg F E B K) := isSimpleRing_baseChange E B _
  have : Algebra.IsCentral (nonsplitField F E K) (nonsplitAlg F E B K) :=
    isCentral_baseChange E B _
  have hU := nonsplitInvolution_isUnitary F E B K τ hτ
  obtain ⟨m, ⟨e₀⟩⟩ := hS (nonsplitField F E K) (nonsplitConj F E K) (nonsplitConj_ne_one F E K)
    (nonsplitAlg F E B K) (nonsplitInvolution F E B K τ) hU
  have hm := matrix_size_eq_reducedDegree E B (nonsplitField F E K) m e₀
  subst hm
  set θ := nonsplitInvolution F E B K τ with hθ
  have hθ1 : θ 1 = 1 := by
    have := hU.2.2.2 1
    rwa [map_one, map_one] at this
  have hθsmul : ∀ (k : K) (z : nonsplitAlg F E B K), θ (k • z) = k • θ z := by
    intro k z
    simp [hθ, nonsplitInvolution]
  let ρ : AlgebraInvolution K Mat :=
    { linear :=
        { toFun := fun X => e₀ (θ (e₀.symm X))
          map_add' := fun X Y => by simp only [map_add, hU.1]
          map_smul' := fun k X => by
            simp only [RingHom.id_apply]
            rw [← algebraMap_smul (nonsplitField F E K) k X, map_smul, algebraMap_smul, hθsmul,
              ← algebraMap_smul (nonsplitField F E K) k (θ _), map_smul, algebraMap_smul] }
      map_one := by simp [hθ1]
      map_mul := fun X Y => by simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, hU.2.1]
      involutive := fun X => by simp only [LinearMap.coe_mk, AddHom.coe_mk,
        AlgEquiv.symm_apply_apply, hU.2.2.1, AlgEquiv.apply_symm_apply] }
  have hρ : ∀ a : nonsplitField F E K, ρ (algebraMap (nonsplitField F E K) Mat a) =
      algebraMap (nonsplitField F E K) Mat (nonsplitConjInvolution F E K a) := by
    intro a
    change e₀ (θ (e₀.symm _)) = _
    rw [AlgEquiv.commutes, hU.2.2.2, AlgEquiv.commutes]
    rfl
  have hc : ∃ a : nonsplitField F E K, nonsplitConjInvolution F E K a ≠ a :=
    nonsplit_exists_conj_ne F E K
  obtain ⟨H, hH, hadj⟩ := exists_hermitianGram_of_matrixInvolution
    (nonsplitConjInvolution F E K) (reducedDegree_pos E B) hc ρ hρ
  have hct : ∀ X : Mat, matrixTranspose (nonsplitConjInvolution F E K) _ X =
      Landherr.ct (nonsplitConjHom F E K) X := fun X => Matrix.ext fun i j => rfl
  refine ⟨e₀, H, by rw [← hct]; exact hH, fun z => ?_⟩
  have h := hadj (e₀ z)
  rw [AlgebraInvolution.adjoint_apply, hct] at h
  rw [← h]
  change e₀ (θ z) = e₀ (θ (e₀.symm (e₀ z)))
  rw [AlgEquiv.symm_apply_apply]

omit [Algebra F B] [IsScalarTower F E B] [FiniteDimensional E B] [Algebra.IsCentral E B]
  [IsSimpleRing B] in
theorem ct_mul_nonsplit (X Y : Mat) :
    Landherr.ct (nonsplitConjHom F E K) (X * Y) =
      Landherr.ct (nonsplitConjHom F E K) Y * Landherr.ct (nonsplitConjHom F E K) X := by
  simp only [Landherr.ct, Matrix.map_mul, Matrix.transpose_mul]

omit [Algebra F B] [IsScalarTower F E B] [FiniteDimensional E B] [Algebra.IsCentral E B]
  [IsSimpleRing B] in
theorem ct_one_nonsplit : Landherr.ct (nonsplitConjHom F E K) (1 : Mat) = 1 := by
  simp only [Landherr.ct, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

omit [Algebra F B] [IsScalarTower F E B] [FiniteDimensional E B] [Algebra.IsCentral E B]
  [IsSimpleRing B] in
theorem det_ct_nonsplit (X : Mat) :
    (Landherr.ct (nonsplitConjHom F E K) X).det = star X.det := by
  rw [Landherr.ct, Matrix.det_transpose, ← nonsplitConjHom_apply, RingHom.map_det]
  rfl

include hτ in
/-- Let `K` have the unitary splitting property with `skewSq F E` nonsquare in `K`.
If `τ` acts on `E` by quadratic conjugation, the relative reduced norm intertwines
`τ_K` with conjugation on the center. -/
theorem relNorm_baseChange_nonsplit (hS : UnitaryInvolutionSplitting K) (z : K ⊗[F] B) :
    relNorm F E B K (τ.baseChange K z) = centerConj F E K (relNorm F E B K z) := by
  obtain ⟨e, H, hH, he⟩ := exists_nonsplit_chart F E B K τ hτ hS
  apply (nonsplitCenterEquiv F E K).injective
  rw [nonsplitCenterEquiv_centerConj, nonsplitCenterEquiv_relNorm, nonsplitCenterEquiv_relNorm,
    ← nonsplitInvolution_equiv, reducedNorm_eq_chart_det E B e, reducedNorm_eq_chart_det E B e, he,
    Matrix.det_units_conj', det_ct_nonsplit]

include hτ in
/-- Let `τ` act on `E` by quadratic conjugation. Let `K` have the unitary splitting property
and let `skewSq F E` be nonsquare in `K`. If units `x, y` of `K ⊗_F B` satisfy
`y = x τ_K(x)` and `y` has relative reduced norm one, then `y = w τ_K(w)` for a unit `w`
of relative reduced norm one in the commutator subgroup. -/
theorem exists_commutator_solution (hS : UnitaryInvolutionSplitting K)
    (y x : (K ⊗[F] B)ˣ) (hyx : (y : K ⊗[F] B) = x * τ.baseChange K x)
    (hy : relNorm F E B K y = 1) :
    ∃ w : (K ⊗[F] B)ˣ, (y : K ⊗[F] B) = w * τ.baseChange K w ∧ relNorm F E B K w = 1 ∧
      w ∈ commutator (K ⊗[F] B)ˣ := by
  classical
  obtain ⟨e, H, hH, he⟩ := exists_nonsplit_chart F E B K τ hτ hS
  set c := nonsplitConjHom F E K with hc
  let ψ : K ⊗[F] B ≃+* Mat := (nonsplitEquiv F E B K).toRingEquiv.trans e.toRingEquiv
  have hψ : ∀ z, ψ z = e (nonsplitEquiv F E B K z) := fun z => rfl
  have key : ∀ z, ψ (τ.baseChange K z) = ((H⁻¹ : Matˣ) : Mat) * Landherr.ct c (ψ z) * (H : Mat) := by
    intro z
    rw [hψ, hψ, ← nonsplitInvolution_equiv, he]
  have hdet : ∀ z, nonsplitCenterEquiv F E K (relNorm F E B K z) = (ψ z).det := by
    intro z
    rw [nonsplitCenterEquiv_relNorm, reducedNorm_eq_chart_det E B e]
    rfl
  set X := ψ x with hXdef
  have hXY : ψ y = X * (((H⁻¹ : Matˣ) : Mat) * Landherr.ct c X * (H : Mat)) := by rw [hyx, map_mul, key]
  have hdetY : (ψ y).det = 1 := by rw [← hdet, hy, map_one]
  have hnorm : X.det * star X.det = 1 := by
    rw [hXY, Matrix.det_mul, Matrix.det_units_conj', det_ct_nonsplit] at hdetY
    exact hdetY
  have hX0 : X.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hnorm
    exact zero_ne_one hnorm
  set δ := (X.det)⁻¹ with hδdef
  have hδ : c δ * δ = 1 := by
    rw [hδdef, map_inv₀, ← mul_inv, nonsplitConjHom_apply, mul_comm, hnorm, inv_one]
  have hHinv : Landherr.ct c ((H⁻¹ : Matˣ) : Mat) = ((H⁻¹ : Matˣ) : Mat) := by
    have h1 : Landherr.ct c ((H⁻¹ : Matˣ) : Mat) * (H : Mat) = 1 := by
      calc Landherr.ct c ((H⁻¹ : Matˣ) : Mat) * (H : Mat)
          = Landherr.ct c ((H⁻¹ : Matˣ) : Mat) * Landherr.ct c (H : Mat) := by rw [hH]
        _ = 1 := by rw [← ct_mul_nonsplit, Units.mul_inv, ct_one_nonsplit]
    calc Landherr.ct c ((H⁻¹ : Matˣ) : Mat)
        = Landherr.ct c ((H⁻¹ : Matˣ) : Mat) * (H : Mat) * ((H⁻¹ : Matˣ) : Mat) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = ((H⁻¹ : Matˣ) : Mat) := by rw [h1, one_mul]
  have hHinv0 : ((H⁻¹ : Matˣ) : Mat) ≠ 0 := by
    intro h0
    have h01 : (H : Mat) * ((H⁻¹ : Matˣ) : Mat) = 1 := Units.mul_inv H
    rw [h0, mul_zero] at h01
    have : Nonempty (Fin (reducedDegree E B)) := ⟨⟨0, reducedDegree_pos E B⟩⟩
    exact zero_ne_one h01
  obtain ⟨g, hg, hgdet⟩ := exists_unitary_det c (nonsplitConjHom_involutive F E K)
    (nonsplit_exists_conj_ne F E K) ((H⁻¹ : Matˣ) : Mat) hHinv hHinv0 δ hδ
  set W := X * g with hWdef
  have hWdet : W.det = 1 := by
    rw [hWdef, Matrix.det_mul, hgdet, hδdef, mul_inv_cancel₀ hX0]
  have hW : W * (((H⁻¹ : Matˣ) : Mat) * Landherr.ct c W * (H : Mat)) = ψ y := by
    rw [hXY, hWdef, ct_mul_nonsplit]
    calc X * g * (((H⁻¹ : Matˣ) : Mat) * (Landherr.ct c g * Landherr.ct c X) * (H : Mat))
        = X * (g * ((H⁻¹ : Matˣ) : Mat) * Landherr.ct c g) * Landherr.ct c X * (H : Mat) := by
          noncomm_ring
      _ = X * (((H⁻¹ : Matˣ) : Mat) * Landherr.ct c X * (H : Mat)) := by rw [hg]; noncomm_ring
  have hWunit : IsUnit W := (Matrix.isUnit_iff_isUnit_det W).mpr (by rw [hWdet]; exact isUnit_one)
  set Wu := hWunit.unit with hWu
  let f : Matˣ ≃* (K ⊗[F] B)ˣ := Units.mapEquiv ψ.symm.toMulEquiv
  have hfW : ψ ((f Wu : (K ⊗[F] B)ˣ) : K ⊗[F] B) = W := by
    change ψ (ψ.symm W) = W
    exact ψ.apply_symm_apply W
  refine ⟨f Wu, ?_, ?_, ?_⟩
  · apply ψ.injective
    rw [map_mul, key, hfW, hW]
  · apply (nonsplitCenterEquiv F E K).injective
    rw [hdet, hfW, hWdet, map_one]
  · have h2 : (2 : nonsplitField F E K) ≠ 0 := by
      have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
      have : CharZero (nonsplitField F E K) :=
        charZero_of_injective_algebraMap (algebraMap K (nonsplitField F E K)).injective
      exact two_ne_zero
    have hc' : Wu ∈ commutator Matˣ := mem_commutator_of_det_eq_one h2 Wu hWdet
    have hm := Subgroup.mem_map_of_mem f.toMonoidHom hc'
    rwa [map_commutator_of_surjective (f := f.toMonoidHom) f.surjective] at hm

end Langlands.CentralSimple.Landherr
