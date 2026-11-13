import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.Global.AdelicRepresentationHeight
import Langlands.Global.PositiveRealTorusIntrinsic
import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Mathlib.NumberTheory.NumberField.ProductFormula

/-! # Product-formula lower bounds for diagonal adelic heights -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicSiegelFactors

section ProductFormula

variable (F : Type u) [Field F] [NumberField F]

theorem norm_infiniteProjection_diagonal (v : InfinitePlace F) (x : F) :
    ‖infiniteProjection F v (diagonal F x)‖ = v x := by
  rw [infiniteProjection_diagonal]
  rw [NumberField.InfinitePlace.Completion.algebraMap_apply]
  rw [← (WithAbs.equiv v.1).apply_symm_apply x]
  exact NumberField.InfinitePlace.Completion.norm_coe (v := v) _

theorem norm_finiteProjection_diagonal (v : FinitePlace F) (x : F) :
    ‖finiteProjection F v (diagonal F x)‖ =
      NumberField.FinitePlace.equivHeightOneSpectrum.symm v x := by
  rw [finiteProjection_diagonal, NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply]
  rfl

theorem hasFiniteMulSupport_norm_finiteProjection_diagonal {x : F} (hx : x ≠ 0) :
    (fun v : FinitePlace F => ‖finiteProjection F v (diagonal F x)‖).HasFiniteMulSupport := by
  simp only [norm_finiteProjection_diagonal]
  change (Function.mulSupport ((fun w : NumberField.FinitePlace F => w x) ∘
    NumberField.FinitePlace.equivHeightOneSpectrum.symm)).Finite
  rw [Function.mulSupport_comp_eq_preimage]
  exact (NumberField.FinitePlace.hasFiniteMulSupport hx).preimage (Equiv.injective _).injOn

/-- The product formula, with the local norms of the actual adele projections. -/
theorem prod_norm_diagonal_eq_one {x : F} (hx : x ≠ 0) :
    (∏ v : InfinitePlace F, ‖infiniteProjection F v (diagonal F x)‖ ^ v.mult) *
      ∏ᶠ v : FinitePlace F, ‖finiteProjection F v (diagonal F x)‖ = 1 := by
  simp only [norm_infiniteProjection_diagonal, norm_finiteProjection_diagonal]
  rw [finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm
    (f := fun w : NumberField.FinitePlace F => w x)]
  exact NumberField.prod_abs_eq_one hx

end ProductFormula

section EntryBound

open AdelicMatrixHeight MatrixInverseHeight GroupScheme.GeneralLinear.CocharacterDiagonal

variable (F : Type u) [Field F] [NumberField F] {N : ℕ}

/-- An entry equal to a nonzero rational number times a positive scalar idele `s` forces the
full height to be at least `(N * s) ^ [F : ℚ]`, by the product formula. -/
theorem pow_le_height_of_entry (hN : 0 < N) (g : AdelicGL F N) (i j : Fin N) {ρ : F}
    (hρ : ρ ≠ 0) (s : ℝ≥0ˣ)
    (h : (g : Matrix (Fin N) (Fin N) (Adeles F)) i j =
      diagonal F ρ * ((PositiveRealIdeles.full F s : Ideles F) : Adeles F)) :
    ((N : ℝ) * ((s : ℝ≥0) : ℝ)) ^ (∑ v : InfinitePlace F, v.mult) ≤
      AdelicMatrixHeight.height F N g := by
  have hs : 0 ≤ ((s : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hv0 (v : InfinitePlace F) : 0 ≤ v ρ :=
    (norm_nonneg _).trans_eq (norm_infiniteProjection_diagonal F v ρ)
  have hinf (v : InfinitePlace F) :
      v ρ * ((s : ℝ≥0) : ℝ) ≤ infiniteLocal F N g v := by
    have h1 := entry_le_localMaximum (infiniteProjection F v) g i j
    rw [h, map_mul, norm_mul, norm_infiniteProjection_diagonal] at h1
    have h2 : ‖infiniteProjection F v
        ((PositiveRealIdeles.full F s : Ideles F) : Adeles F)‖ = ((s : ℝ≥0) : ℝ) :=
      PositiveRealIdeles.norm_full_infinite_value F v s
    rw [h2] at h1
    exact h1
  have hfin (v : FinitePlace F) :
      ‖finiteProjection F v (diagonal F ρ)‖ ≤ finiteLocal F N g v := by
    have h1 := entry_le_localMaximum (finiteProjection F v) g i j
    rw [h, map_mul, norm_mul] at h1
    have h2 : ‖finiteProjection F v
        ((PositiveRealIdeles.full F s : Ideles F) : Adeles F)‖ = 1 := by
      change ‖(PositiveRealIdeles.full F s).val.2 v‖ = 1
      rw [PositiveRealIdeles.full_finite_value, norm_one]
    rwa [h2, mul_one] at h1
  calc ((N : ℝ) * ((s : ℝ≥0) : ℝ)) ^ (∑ v : InfinitePlace F, v.mult)
      = ((N : ℝ) * ((s : ℝ≥0) : ℝ)) ^ (∑ v : InfinitePlace F, v.mult) *
          ((∏ v : InfinitePlace F, ‖infiniteProjection F v (diagonal F ρ)‖ ^ v.mult) *
            ∏ᶠ v : FinitePlace F, ‖finiteProjection F v (diagonal F ρ)‖) := by
        rw [prod_norm_diagonal_eq_one F hρ, mul_one]
    _ = (∏ v : InfinitePlace F, ((N : ℝ) * (v ρ * ((s : ℝ≥0) : ℝ))) ^ v.mult) *
          ∏ᶠ v : FinitePlace F, ‖finiteProjection F v (diagonal F ρ)‖ := by
        simp only [norm_infiniteProjection_diagonal]
        rw [← mul_assoc, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [← mul_pow]
        ring_nf
    _ ≤ AdelicMatrixHeight.height F N g := by
        rw [AdelicMatrixHeight.height]
        apply mul_le_mul
        · apply Finset.prod_le_prod₀
          · intro v _
            exact pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hv0 v) hs)) _
          · intro v _
            exact pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hv0 v) hs))
              (mul_le_mul_of_nonneg_left (hinf v) (Nat.cast_nonneg _)) _
        · exact finprod_le_finprod₀ (hasFiniteMulSupport_norm_finiteProjection_diagonal F hρ)
            (fun v => norm_nonneg _) (hasFiniteMulSupport_finiteLocal F N hN g) (fun v => hfin v)
        · exact finprod_nonneg fun v => norm_nonneg _
        · exact Finset.prod_nonneg fun v _ =>
            pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (localMaximum_nonneg _ _)) _

omit [NumberField F] in
/-- In an invertible matrix over a field, the `j`-th row of the inverse and the `j`-th column
have a common index at which both entries are nonzero. -/
theorem exists_inv_entry_ne_zero_and_entry_ne_zero (R : Matrix.GeneralLinearGroup (Fin N) F)
    (j : Fin N) : ∃ k, (R⁻¹ : Matrix.GeneralLinearGroup (Fin N) F) j k ≠ 0 ∧ R k j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h1 : ((R⁻¹ * R : Matrix.GeneralLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F) j j =
      1 := by
    rw [inv_mul_cancel]
    simp
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_zero] at h1
  · exact zero_ne_one h1
  · intro k _
    by_cases hk : (R⁻¹ : Matrix.GeneralLinearGroup (Fin N) F) j k = 0
    · rw [hk, zero_mul]
    · rw [hcon k hk, mul_zero]

theorem inv_diagonalMatrix {A : Type*} [CommRing A] (t : Fin N → Aˣ) :
    (diagonalMatrix t)⁻¹ = diagonalMatrix t⁻¹ := by
  unfold diagonalMatrix
  rw [← map_inv, ← map_inv]

/-- A diagonal unit matrix has local maximum at most a common bound on its entries and their
inverses. -/
theorem localMaximum_diagonalMatrix_le {A K : Type*} [CommRing A] [NormedField K]
    (f : A →+* K) (t : Fin N → Aˣ) {C : ℝ} (hC : 0 ≤ C)
    (ht : ∀ j, ‖f (t j : A)‖ ≤ C) (hti : ∀ j, ‖f (((t j)⁻¹ : Aˣ) : A)‖ ≤ C) :
    MatrixInverseHeight.localMaximum f (diagonalMatrix t) ≤ C := by
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro a
    apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro b
    change ‖f ((diagonalMatrix t : Matrix (Fin N) (Fin N) A) a b)‖ ≤ C
    rw [coe_diagonalMatrix, Matrix.diagonal_apply]
    split_ifs with h
    · exact ht a
    · simpa using hC
  · apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro a
    apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro b
    change ‖f (((diagonalMatrix t)⁻¹ : Matrix.GeneralLinearGroup (Fin N) A) a b)‖ ≤ C
    rw [inv_diagonalMatrix, coe_diagonalMatrix, Matrix.diagonal_apply]
    split_ifs with h
    · exact hti a
    · simpa using hC

/-- Upper bound for the full height of a diagonal matrix of positive real scalar ideles. -/
theorem height_diagonalMatrix_full_le (hN : 0 < N) (r : Fin N → ℝ≥0ˣ) {M : ℝ}
    (hr : ∀ j, ((r j : ℝ≥0) : ℝ) ≤ M) (hri : ∀ j, (((r j)⁻¹ : ℝ≥0ˣ) : ℝ≥0) ≤ M) :
    AdelicMatrixHeight.height F N (diagonalMatrix (fun j => PositiveRealIdeles.full F (r j))) ≤
      ((N : ℝ) * M) ^ (∑ v : InfinitePlace F, v.mult) := by
  have hM : 0 ≤ M := (NNReal.coe_nonneg _).trans (hr ⟨0, hN⟩)
  have hfin : ∀ v : FinitePlace F,
      finiteLocal F N (diagonalMatrix (fun j => PositiveRealIdeles.full F (r j))) v = 1 := by
    intro v
    apply le_antisymm _ (one_le_finiteLocal F N hN _ v)
    apply localMaximum_diagonalMatrix_le _ _ zero_le_one
    · intro j
      change ‖(PositiveRealIdeles.full F (r j)).val.2 v‖ ≤ 1
      rw [PositiveRealIdeles.full_finite_value, norm_one]
    · intro j
      rw [← map_inv]
      change ‖(PositiveRealIdeles.full F (r j)⁻¹).val.2 v‖ ≤ 1
      rw [PositiveRealIdeles.full_finite_value, norm_one]
  have hinf : ∀ v : InfinitePlace F,
      infiniteLocal F N (diagonalMatrix (fun j => PositiveRealIdeles.full F (r j))) v ≤ M := by
    intro v
    apply localMaximum_diagonalMatrix_le _ _ hM
    · intro j
      change ‖(PositiveRealIdeles.full F (r j)).val.1 v‖ ≤ M
      rw [PositiveRealIdeles.norm_full_infinite_value]
      exact hr j
    · intro j
      rw [← map_inv]
      change ‖(PositiveRealIdeles.full F (r j)⁻¹).val.1 v‖ ≤ M
      rw [PositiveRealIdeles.norm_full_infinite_value]
      exact_mod_cast hri j
  rw [AdelicMatrixHeight.height]
  simp only [hfin, finprod_one, mul_one]
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀
  · intro v _
    exact pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (localMaximum_nonneg _ _)) _
  · intro v _
    exact pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (localMaximum_nonneg _ _))
      (mul_le_mul_of_nonneg_left (hinf v) (Nat.cast_nonneg _)) _

/-- **Diagonal inequality.** Multiplying a diagonal matrix of positive real scalar ideles on
the left by a rational invertible matrix does not decrease the full height. -/
theorem height_diagonalMatrix_full_le_height_rational_mul (hN : 0 < N)
    (R : Matrix.GeneralLinearGroup (Fin N) F) (r : Fin N → ℝ≥0ˣ) :
    AdelicMatrixHeight.height F N (diagonalMatrix (fun j => PositiveRealIdeles.full F (r j))) ≤
      AdelicMatrixHeight.height F N
        (Matrix.GeneralLinearGroup.map (diagonal F) R *
          diagonalMatrix (fun j => PositiveRealIdeles.full F (r j))) := by
  let φ : Fin N → ℝ := fun j => max ((r j : ℝ≥0) : ℝ) ((((r j)⁻¹ : ℝ≥0ˣ) : ℝ≥0) : ℝ)
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ φ ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hup := height_diagonalMatrix_full_le F hN r (M := φ j0)
    (fun j => (le_max_left _ _).trans (hj0 j (Finset.mem_univ _)))
    (fun j => (le_max_right _ _).trans (hj0 j (Finset.mem_univ _)))
  refine hup.trans ?_
  obtain ⟨k, hk1, hk2⟩ := exists_inv_entry_ne_zero_and_entry_ne_zero F R j0
  rcases le_total ((r j0 : ℝ≥0) : ℝ) ((((r j0)⁻¹ : ℝ≥0ˣ) : ℝ≥0) : ℝ) with hle | hle
  · rw [show φ j0 = ((((r j0)⁻¹ : ℝ≥0ˣ) : ℝ≥0) : ℝ) from max_eq_right hle]
    rw [← AdelicMatrixHeight.height_inv]
    apply pow_le_height_of_entry F hN _ j0 k hk1 (r j0)⁻¹
    rw [mul_inv_rev, inv_diagonalMatrix, Units.val_mul, coe_diagonalMatrix,
      Matrix.diagonal_mul, mul_comm, Pi.inv_apply, ← map_inv]
    rfl
  · rw [show φ j0 = ((r j0 : ℝ≥0) : ℝ) from max_eq_left hle]
    apply pow_le_height_of_entry F hN _ k j0 hk2 (r j0)
    rw [Units.val_mul, coe_diagonalMatrix, Matrix.mul_diagonal]
    rfl

end EntryBound

section MainInequality

open GroupScheme AdelicGroupPoints PositiveRealTorus RepresentationGrowth
  GroupScheme.GeneralLinear.CocharacterDiagonal

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The representation matrix at the image of a torus point is the matrix of the restricted
split-torus representation at the point's coordinates. -/
theorem adelicMatrix_map_eq_matrixAt {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (f : T.toGrp ⟶ G)
    (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    (y : AdelicGroupPoints F T.toGrp) :
    adelicMatrix F G rho (map F T.toGrp G f y) =
      matrixAt I (rho.restrict (e.inv ≫ f)) (coordinates F I T e (Adeles F) y) := by
  unfold matrixAt
  rw [show (splitTorus.algebraPointsEquiv I (Adeles F)).symm
      (coordinates F I T e (Adeles F) y) = y ≫ e.hom.hom.hom from
    (splitTorus.algebraPointsEquiv I (Adeles F)).symm_apply_apply (y ≫ e.hom.hom.hom)]
  rw [GroupScheme.MatrixRepresentation.affineMatrix_restrict]
  change rho.affineMatrix _ (y ≫ f.hom.hom) =
    rho.affineMatrix _ ((y ≫ e.hom.hom.hom) ≫ (e.inv ≫ f).hom.hom)
  have h : e.hom.hom.hom ≫ (e.inv ≫ f).hom.hom = f.hom.hom := by
    rw [Grp.comp_hom_hom, ← Grp.comp_hom_hom_assoc, e.hom_inv_id, Grp.id_hom_hom,
      Category.id_comp]
  rw [Category.assoc, h]

/-- The representation matrix of a principal rational point is the diagonal image of its
rational representation matrix. -/
theorem adelicMatrix_rational {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (q : RationalGroupPoints F G) :
    adelicMatrix F G rho (rational F G q) =
      Matrix.GeneralLinearGroup.map (diagonal F) (rho.affineMatrix (CommAlgCat.of F F) q) :=
  rho.affineMatrix_naturality (CommAlgCat.ofHom (Algebra.ofId F (Adeles F))) q

/-- **Part A of Mœglin–Waldspurger I.2.2 (vii).** For a split torus `T₀` and any homomorphism
`f : T₀ → G`, the full adelic height of the image of an intrinsic positive point is bounded by a
constant times the height of each of its rational left translates. -/
theorem exists_adelicHeight_map_le_rational_mul {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (hT₀ : IsSplitTorus T₀.toGrp)
    (f : T₀.toGrp ⟶ G) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀)
      (q : RationalGroupPoints F G),
      adelicHeight F G rho (AdelicGroupPoints.map F T₀.toGrp G f a) ≤
        c * adelicHeight F G rho
          (AdelicGroupPoints.rational F G q * AdelicGroupPoints.map F T₀.toGrp G f a) := by
  classical
  obtain ⟨I, _, ⟨e⟩⟩ := hT₀
  have : Fintype I := Fintype.ofFinite I
  obtain ⟨B, w, hBw⟩ := exists_diagonalizingMatrix I (rho.restrict (e.inv ≫ f))
  set BA : AdelicGL F N := Matrix.GeneralLinearGroup.map (algebraMap F (Adeles F)) B with hBA
  have h0 (M : AdelicGL F N) : 0 ≤ AdelicMatrixHeight.height F N M :=
    zero_le_one.trans (AdelicMatrixHeight.one_le_height F N hN M)
  refine ⟨(AdelicMatrixHeight.height F N BA * AdelicMatrixHeight.height F N BA⁻¹) ^ 2,
    pow_nonneg (mul_nonneg (h0 _) (h0 _)) 2, fun a q => ?_⟩
  have hmem : a.val ∈ PositiveRealTorus.subgroup F I T₀ e := by
    rw [subgroup_eq_intrinsicSubgroup]
    exact a.property
  obtain ⟨x, hx⟩ := (mem_subgroup_iff F I T₀ e _).mp hmem
  let r : Fin N → ℝ≥0ˣ := fun j => ∏ k, x k ^ w j k
  have hexp (j : Fin N) :
      splitTorus.exponentValue I (fun k => PositiveRealIdeles.full F (x k))
        (Multiplicative.ofAdd (w j)) = PositiveRealIdeles.full F (r j) := by
    change (∏ k, PositiveRealIdeles.full F (x k) ^ w j k) = _
    rw [map_prod]
    simp only [map_zpow]
  have hdiag := hBw (Adeles F) (fun k => PositiveRealIdeles.full F (x k))
  rw [show (fun j => splitTorus.exponentValue I (fun k => PositiveRealIdeles.full F (x k))
      (Multiplicative.ofAdd (w j))) = fun j => PositiveRealIdeles.full F (r j) from
    funext hexp] at hdiag
  have hmat : adelicMatrix F G rho (map F T₀.toGrp G f a) =
      BA * diagonalMatrix (fun j => PositiveRealIdeles.full F (r j)) * BA⁻¹ := by
    rw [← hdiag, adelicMatrix_map_eq_matrixAt F G rho T₀ f I e, ← hx, coordinates_full, hBA]
    group
  set D : AdelicGL F N := diagonalMatrix (fun j => PositiveRealIdeles.full F (r j)) with hD
  set Q := rho.affineMatrix (CommAlgCat.of F F) q with hQ
  set QA : AdelicGL F N := Matrix.GeneralLinearGroup.map (algebraMap F (Adeles F)) Q with hQA
  have hkey : AdelicMatrixHeight.height F N D ≤
      AdelicMatrixHeight.height F N (BA⁻¹ * (QA * (BA * D * BA⁻¹)) * BA) := by
    have h := height_diagonalMatrix_full_le_height_rational_mul F hN (B⁻¹ * Q * B) r
    rw [map_mul, map_mul, map_inv] at h
    refine h.trans_eq (congrArg _ ?_)
    change BA⁻¹ * QA * BA * D = _
    group
  rw [adelicHeight, adelicHeight, map_mul, hmat, adelicMatrix_rational, ← hQ]
  change AdelicMatrixHeight.height F N (BA * D * BA⁻¹) ≤ _ *
    AdelicMatrixHeight.height F N (QA * (BA * D * BA⁻¹))
  set X := QA * (BA * D * BA⁻¹) with hX
  calc AdelicMatrixHeight.height F N (BA * D * BA⁻¹)
      ≤ AdelicMatrixHeight.height F N BA * AdelicMatrixHeight.height F N D *
          AdelicMatrixHeight.height F N BA⁻¹ := by
        refine (AdelicMatrixHeight.height_mul_le F N hN _ _).trans ?_
        exact mul_le_mul_of_nonneg_right (AdelicMatrixHeight.height_mul_le F N hN _ _) (h0 _)
    _ ≤ AdelicMatrixHeight.height F N BA *
          (AdelicMatrixHeight.height F N BA⁻¹ * AdelicMatrixHeight.height F N X *
            AdelicMatrixHeight.height F N BA) * AdelicMatrixHeight.height F N BA⁻¹ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (h0 _)) (h0 _)
        refine hkey.trans ((AdelicMatrixHeight.height_mul_le F N hN _ _).trans ?_)
        exact mul_le_mul_of_nonneg_right (AdelicMatrixHeight.height_mul_le F N hN _ _) (h0 _)
    _ = (AdelicMatrixHeight.height F N BA * AdelicMatrixHeight.height F N BA⁻¹) ^ 2 *
          AdelicMatrixHeight.height F N X := by ring

end MainInequality

end Langlands.Global.AdelicSiegelFactors
