import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnipotentIntersectionProduct

/-! # Heights of Levi components of dynamic parabolic points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix Filter Topology
open Langlands.GroupScheme.GeneralLinear
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

/-- **Entries of a limit, diagonal form.** Let `ρ₁` be a representation with
`χ ≫ ρ₁ = diag(t ^ e i)`, `t ^ n → 0`, and suppose the matrix of `p` is block triangular for
`e`. If `χ(t) ^ n p χ(t)⁻ⁿ → m`, then every entry of the matrix of `m` has absolute value at
most that of the corresponding entry of the matrix of `p`. -/
theorem abs_rationalMatrix_apply_le_of_tendsto_conj
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) {N : ℕ}
    (ρ₁ : MatrixRepresentation G (Fin N)) {e : Fin N → ℤ}
    (hχ : χ ≫ ρ₁ = diagonalCocharacter (Fin N) (CommRingCat.of F) e)
    (t : Fˣ) (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0)) (p m : rationalPoints G)
    (hp : ρ₁.rationalMatrix p ∈ blockParabolicSubgroup F e)
    (hm : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      Tendsto (fun n : ℕ => (gmRationalPoint t ≫ χ.hom.hom) ^ n * p *
        ((gmRationalPoint t ≫ χ.hom.hom) ^ n)⁻¹) atTop (𝓝 m))
    (i j : Fin N) :
    LocalField.residueNormalizedAbsoluteValue F
        ((ρ₁.rationalMatrix m : Matrix (Fin N) (Fin N) F) i j) ≤
      LocalField.residueNormalizedAbsoluteValue F
        ((ρ₁.rationalMatrix p : Matrix (Fin N) (Fin N) F) i j) := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  have ht1 := residueNormalizedAbsoluteValue_le_one_of_tendsto_pow F ht
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have hD : ρ₁.rationalMatrix (gmRationalPoint t ≫ χ.hom.hom) = diagonalUnits F e t :=
    rationalMatrix_gmRationalPoint_comp hχ t
  have hentry : ∀ n : ℕ,
      (ρ₁.rationalMatrix ((gmRationalPoint t ≫ χ.hom.hom) ^ n * p *
        ((gmRationalPoint t ≫ χ.hom.hom) ^ n)⁻¹) : Matrix (Fin N) (Fin N) F) i j =
        (((t ^ n)⁻¹ : Fˣ) : F) ^ (e j - e i) *
          (ρ₁.rationalMatrix p : Matrix (Fin N) (Fin N) F) i j := by
    intro n
    rw [← HarishChandraSchwartz.diagonalUnits_conj_apply e ((t ^ n)⁻¹)]
    rw [map_mul, map_mul, map_inv, map_pow, hD, map_inv, map_pow, inv_inv]
  have hlim := ((Plancherel.continuous_residueNormalizedAbsoluteValue F).tendsto _).comp
    (((ρ₁.continuous_rationalMatrix_entry i j).tendsto m).comp hm)
  rcases lt_or_ge (e i) (e j) with hlt | hge
  · -- Entries below the block diagonal vanish along the whole sequence.
    have hp0 : (ρ₁.rationalMatrix p : Matrix (Fin N) (Fin N) F) i j = 0 :=
      (mem_blockParabolicSubgroup F e).mp hp i j hlt
    have hzero : ∀ n : ℕ, LocalField.residueNormalizedAbsoluteValue F
        ((ρ₁.rationalMatrix ((gmRationalPoint t ≫ χ.hom.hom) ^ n * p *
          ((gmRationalPoint t ≫ χ.hom.hom) ^ n)⁻¹) : Matrix (Fin N) (Fin N) F) i j) =
          LocalField.residueNormalizedAbsoluteValue F
            ((ρ₁.rationalMatrix p : Matrix (Fin N) (Fin N) F) i j) := by
      intro n
      rw [hentry n, hp0, mul_zero]
    exact le_of_tendsto' hlim fun n => (hzero n).le
  · -- On and above the block diagonal the factor has absolute value at most `1`.
    refine le_of_tendsto' hlim fun n => ?_
    change ‖(ρ₁.rationalMatrix ((gmRationalPoint t ≫ χ.hom.hom) ^ n * p *
        ((gmRationalPoint t ≫ χ.hom.hom) ^ n)⁻¹) : Matrix (Fin N) (Fin N) F) i j‖ ≤
      ‖(ρ₁.rationalMatrix p : Matrix (Fin N) (Fin N) F) i j‖
    rw [hentry n, norm_mul, norm_zpow]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    have hx : 1 ≤ ‖(((t ^ n)⁻¹ : Fˣ) : F)‖ := by
      rw [Units.val_inv_eq_inv_val, norm_inv, Units.val_pow_eq_pow_val, norm_pow]
      exact (one_le_inv₀ (pow_pos (norm_pos_iff.mpr t.ne_zero) n)).mpr
        (pow_le_one₀ (norm_nonneg _) ht1)
    exact zpow_le_one_of_nonpos₀ hx (by omega)

variable [LocallyOfFiniteType G.X.hom]

/-- **Heights of Levi components.** Let `χ` be a cocharacter of `G` and `ρ₀` a closed
representation. There is `C` such that whenever `p ∈ P(χ)(F)` factors as `p = m u` with
`m ∈ Z(χ)(F)` and `u ∈ U(χ)(F)`, the height of `m` is at most `C` times the height of `p`. -/
theorem exists_rationalMatrixNorm_levi_le
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N)) (hρ₀ : IsClosedSubgroup ρ₀) :
    ∃ C : ℝ, ∀ p m : rationalPoints G, p ∈ (Dynamic.parabolic χ).rationalPoints →
      m ∈ (Dynamic.centralizer χ).rationalPoints →
      m⁻¹ * p ∈ (Dynamic.unipotent χ).rationalPoints →
      rationalMatrixNorm F ρ₀ m ≤ C * rationalMatrixNorm F ρ₀ p := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have : IsUltrametricDist F :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (LocalField.residueNormalizedAbsoluteValue_add_le_max F)
  obtain ⟨t, ht⟩ := BruhatTits.DynamicUnipotentContainment.exists_unit_tendsto_pow_zero (F := F)
  obtain ⟨g₀, e, hg₀⟩ := exists_innerIso_comp_eq_diagonalCocharacter F (χ ≫ ρ₀)
  have hcl : IsClosedSubgroup
      (ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom) :=
    hρ₀.comp_iso _
  have hχ₁ : χ ≫ ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom =
      diagonalCocharacter (Fin N) (CommRingCat.of F) e := by
    rw [← Category.assoc, hg₀]
  set M := HarishChandraSchwartz.glNorm
    (rationalMatrix (𝟙 (groupScheme (Fin N) (CommRingCat.of F))) g₀) with hM
  have hM0 : 0 ≤ M := HarishChandraSchwartz.glNorm_nonneg _
  have hconj : ∀ x : rationalPoints G,
      rationalMatrix (ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom) x =
        rationalMatrix (𝟙 (groupScheme (Fin N) (CommRingCat.of F))) g₀ *
          ρ₀.rationalMatrix x *
          (rationalMatrix (𝟙 (groupScheme (Fin N) (CommRingCat.of F))) g₀)⁻¹ :=
    fun x => rationalMatrix_comp_innerIso ρ₀ g₀ x
  have hle₁ : ∀ x : rationalPoints G,
      rationalMatrixNorm F (ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom) x ≤
        M ^ 2 * rationalMatrixNorm F ρ₀ x := by
    intro x
    change HarishChandraSchwartz.glNorm (rationalMatrix
        (ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom) x) ≤
      M ^ 2 * HarishChandraSchwartz.glNorm (ρ₀.rationalMatrix x)
    rw [hconj]
    refine (HarishChandraSchwartz.glNorm_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (HarishChandraSchwartz.glNorm_mul_le _ _)
      (HarishChandraSchwartz.glNorm_nonneg _)).trans_eq ?_
    rw [HarishChandraSchwartz.glNorm_inv]
    ring
  have hle₀ : ∀ x : rationalPoints G, rationalMatrixNorm F ρ₀ x ≤
      M ^ 2 * rationalMatrixNorm F
        (ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom) x := by
    intro x
    change HarishChandraSchwartz.glNorm (ρ₀.rationalMatrix x) ≤
      M ^ 2 * HarishChandraSchwartz.glNorm (rationalMatrix
        (ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom) x)
    have hx : ρ₀.rationalMatrix x =
        (rationalMatrix (𝟙 (groupScheme (Fin N) (CommRingCat.of F))) g₀)⁻¹ *
          rationalMatrix (ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom) x *
          rationalMatrix (𝟙 (groupScheme (Fin N) (CommRingCat.of F))) g₀ := by
      rw [hconj]
      group
    rw [hx]
    refine (HarishChandraSchwartz.glNorm_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (HarishChandraSchwartz.glNorm_mul_le _ _)
      (HarishChandraSchwartz.glNorm_nonneg _)).trans_eq ?_
    rw [HarishChandraSchwartz.glNorm_inv]
    ring
  generalize ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom = ρ₁
    at hcl hχ₁ hle₁ hle₀
  have : IsClosedImmersion ρ₁.hom.hom.left := hcl
  refine ⟨M ^ 2 * M ^ 2, fun p m hp hm hu => ?_⟩
  set a := gmRationalPoint t ≫ χ.hom.hom with ha
  have hcomm : ∀ n : ℕ, Commute m (a ^ n) := by
    intro n
    have h := BruhatTits.DynamicUnipotentContainment.commute_cocharPoint χ hm t
    rw [cocharPoint_eq_gmRationalPoint_comp] at h
    exact h.pow_right n
  have hulim : Tendsto (fun n : ℕ => a ^ n * (m⁻¹ * p) * (a ^ n)⁻¹) atTop (𝓝 1) := by
    have h := BruhatTits.DynamicUnipotentContainment.tendsto_cocharPoint_pow_conj χ t ht
      ⟨m⁻¹ * p, hu⟩
    have h' := h.comp (tendsto_id.prodMk (tendsto_const_nhds (x := (⟨m⁻¹ * p, hu⟩ :
      BruhatTits.DynamicUnipotentContainment.unipotentPoints χ))))
    simpa only [Function.comp_def, id, cocharPoint_eq_gmRationalPoint_comp] using h'
  have hplim : Tendsto (fun n : ℕ => a ^ n * p * (a ^ n)⁻¹) atTop (𝓝 m) := by
    have hk : ∀ n : ℕ, a ^ n * p * (a ^ n)⁻¹ = m * (a ^ n * (m⁻¹ * p) * (a ^ n)⁻¹) := by
      intro n
      have hc := (hcomm n).eq
      calc a ^ n * p * (a ^ n)⁻¹ = (a ^ n * m) * (m⁻¹ * p) * (a ^ n)⁻¹ := by group
        _ = (m * a ^ n) * (m⁻¹ * p) * (a ^ n)⁻¹ := by rw [hc]
        _ = m * (a ^ n * (m⁻¹ * p) * (a ^ n)⁻¹) := by group
    simp_rw [hk]
    simpa using hulim.const_mul m
  have hpinvlim : Tendsto (fun n : ℕ => a ^ n * p⁻¹ * (a ^ n)⁻¹) atTop (𝓝 m⁻¹) := by
    have h := hplim.inv
    convert h using 1
    funext n
    group
  have hpar : ∀ x ∈ (Dynamic.parabolic χ).rationalPoints,
      rationalMatrix ρ₁ x ∈ blockParabolicSubgroup F e := by
    intro x hx
    rw [rationalMatrix_mem_blockParabolicSubgroup_iff]
    exact (Dynamic.mem_parabolic_iff_of_diagonal hχ₁ x).1 hx
  have h1 := abs_rationalMatrix_apply_le_of_tendsto_conj F χ ρ₁ hχ₁ t ht p m (hpar p hp) hplim
  have h2 := abs_rationalMatrix_apply_le_of_tendsto_conj F χ ρ₁ hχ₁ t ht p⁻¹ m⁻¹
    (hpar p⁻¹ (inv_mem hp)) hpinvlim
  have hlevi : rationalMatrixNorm F ρ₁ m ≤ rationalMatrixNorm F ρ₁ p := by
    change HarishChandraSchwartz.glNorm (rationalMatrix ρ₁ m) ≤
      HarishChandraSchwartz.glNorm (rationalMatrix ρ₁ p)
    refine HarishChandraSchwartz.glNorm_le (fun i j => ?_) (fun i j => ?_)
    · have hb : ‖(rationalMatrix ρ₁ p : Matrix (Fin N) (Fin N) F) i j‖ ≤
          HarishChandraSchwartz.glNorm (rationalMatrix ρ₁ p) :=
        HarishChandraSchwartz.norm_le_glNorm (rationalMatrix ρ₁ p) i j
      exact (h1 i j).trans hb
    · have hb : ‖(((rationalMatrix ρ₁ p)⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) i j‖ ≤
          HarishChandraSchwartz.glNorm (rationalMatrix ρ₁ p) :=
        HarishChandraSchwartz.norm_inv_le_glNorm (rationalMatrix ρ₁ p) i j
      have h2' := h2 i j
      rw [map_inv, map_inv] at h2'
      exact h2'.trans hb
  calc rationalMatrixNorm F ρ₀ m ≤ M ^ 2 * rationalMatrixNorm F ρ₁ m := hle₀ m
    _ ≤ M ^ 2 * rationalMatrixNorm F ρ₁ p :=
        mul_le_mul_of_nonneg_left hlevi (pow_nonneg hM0 2)
    _ ≤ M ^ 2 * (M ^ 2 * rationalMatrixNorm F ρ₀ p) :=
        mul_le_mul_of_nonneg_left (hle₁ p) (pow_nonneg hM0 2)
    _ = M ^ 2 * M ^ 2 * rationalMatrixNorm F ρ₀ p := by ring

end LocalField

end Langlands.GroupScheme.MatrixRepresentation
