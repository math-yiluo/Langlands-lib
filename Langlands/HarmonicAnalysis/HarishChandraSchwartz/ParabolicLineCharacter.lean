import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicLineHeight

/-! # The character of a dynamic parabolic on its Chevalley line, and Iwasawa bounds -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open Langlands.GroupScheme.GeneralLinear
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.HarishChandraSchwartz

variable {A : Type*} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

/-- A block unipotent matrix for `-e` fixes the `m`-block coordinates of a vector supported on
the weight block `{e = m}`. -/
theorem mulVec_apply_eq_of_mem_blockUnipotentSubgroup {e : n → ℤ} {g : GL n A}
    (hg : g ∈ blockUnipotentSubgroup A (-e)) {m : ℤ} {w : n → A}
    (hw : ∀ k, e k ≠ m → w k = 0) {i : n} (hi : e i = m) :
    ((g : Matrix n n A) *ᵥ w) i = w i := by
  rw [mem_blockUnipotentSubgroup] at hg
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [hg i i le_rfl, Matrix.one_apply_eq, one_mul]
  · intro l _ hli
    by_cases hl : e l = m
    · rw [hg i l (by simp [hi, hl]), Matrix.one_apply_ne (Ne.symm hli), zero_mul]
    · rw [hw l hl, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

end Langlands.HarishChandraSchwartz

namespace Langlands.GroupScheme.MatrixRepresentation

section Character

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n] {ρ : MatrixRepresentation G n} {j : n}
  {S : Subgroup (rationalPoints G)}

/-- The `j`-th coordinate of `M e j` is the diagonal entry `M j j`. -/
theorem mulVec_single_one_apply_self (M : Matrix n n k) :
    (M *ᵥ Pi.single j 1) j = M j j := by
  rw [Matrix.mulVec_single_one]
  rfl

/-- On the stabilizer, `ρ(x) e j` is the diagonal entry `ρ(x) j j` times `e j`. -/
theorem IsRationalLineStabilizer.mulVec_single_eq (h : IsRationalLineStabilizer ρ j S)
    {x : rationalPoints G} (hx : x ∈ S) :
    (ρ.rationalMatrix x : Matrix n n k) *ᵥ Pi.single j 1 =
      (ρ.rationalMatrix x : Matrix n n k) j j • Pi.single j 1 := by
  obtain ⟨u, hu⟩ := h.exists_unit_of_mem hx
  have hj : (ρ.rationalMatrix x : Matrix n n k) j j = u := by
    rw [← mulVec_single_one_apply_self (j := j) (ρ.rationalMatrix x : Matrix n n k), hu,
      Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  rw [hu, hj]

/-- On the stabilizer, the diagonal entry `ρ(x) j j` is nonzero. -/
theorem IsRationalLineStabilizer.apply_self_ne_zero (h : IsRationalLineStabilizer ρ j S)
    {x : rationalPoints G} (hx : x ∈ S) : (ρ.rationalMatrix x : Matrix n n k) j j ≠ 0 := by
  obtain ⟨u, hu⟩ := h.exists_unit_of_mem hx
  have hj : (ρ.rationalMatrix x : Matrix n n k) j j = u := by
    rw [← mulVec_single_one_apply_self (j := j) (ρ.rationalMatrix x : Matrix n n k), hu,
      Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  rw [hj]
  exact u.ne_zero

/-- **The line character.** If `S` is the stabilizer of the line `k e j`, then `x ↦ ρ(x) j j`
is a homomorphism `S →* kˣ`: the scalar by which `x` acts on the line. -/
def IsRationalLineStabilizer.character (h : IsRationalLineStabilizer ρ j S) : S →* kˣ where
  toFun x := Units.mk0 _ (h.apply_self_ne_zero x.2)
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp only [Units.val_mk0, Subgroup.coe_mul, map_mul, Units.val_mul]
    calc ((ρ.rationalMatrix x : Matrix n n k) * (ρ.rationalMatrix y : Matrix n n k)) j j
        = ((ρ.rationalMatrix x : Matrix n n k) *ᵥ
            ((ρ.rationalMatrix y : Matrix n n k) *ᵥ Pi.single j 1)) j := by
          rw [Matrix.mulVec_mulVec, mulVec_single_one_apply_self]
      _ = (ρ.rationalMatrix y : Matrix n n k) j j * (ρ.rationalMatrix x : Matrix n n k) j j := by
          rw [h.mulVec_single_eq y.2, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
            mulVec_single_one_apply_self]
      _ = _ := mul_comm _ _

@[simp] theorem IsRationalLineStabilizer.coe_character (h : IsRationalLineStabilizer ρ j S)
    (x : S) : (h.character x : k) = (ρ.rationalMatrix x : Matrix n n k) j j :=
  rfl

/-- `ρ(x) e j = χ(x) e j` for the line character `χ`. -/
theorem IsRationalLineStabilizer.mulVec_single_eq_character_smul
    (h : IsRationalLineStabilizer ρ j S) (x : S) :
    (ρ.rationalMatrix x : Matrix n n k) *ᵥ Pi.single j 1 =
      (h.character x : k) • Pi.single j 1 :=
  h.mulVec_single_eq x.2

/-- `ρ((p g)⁻¹) e j = χ(p)⁻¹ ρ(g⁻¹) e j` for `p ∈ S`. -/
theorem IsRationalLineStabilizer.mulVec_mul_inv (h : IsRationalLineStabilizer ρ j S)
    (p : S) (g : rationalPoints G) :
    (ρ.rationalMatrix ((p : rationalPoints G) * g)⁻¹ : Matrix n n k) *ᵥ Pi.single j 1 =
      (((h.character p)⁻¹ : kˣ) : k) •
        ((ρ.rationalMatrix g⁻¹ : Matrix n n k) *ᵥ Pi.single j 1) := by
  have hp := h.mulVec_single_eq_character_smul p⁻¹
  rw [map_inv h.character] at hp
  rw [_root_.mul_inv_rev, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  change (ρ.rationalMatrix g⁻¹ : Matrix n n k) *ᵥ
      ((ρ.rationalMatrix ((p⁻¹ : S) : rationalPoints G) : Matrix n n k) *ᵥ Pi.single j 1) = _
  rw [hp, Matrix.mulVec_smul]

end Character

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}

/-- **Opposite unipotent points do not shrink weight vectors.** Let `v` be an eigenvector of
every `ρ(χ(t))`. Then `‖v‖ ≤ C ‖ρ(x) v‖` for all `x ∈ Ū(F) = U(χ⁻¹)(F)`. -/
theorem exists_rationalVectorNorm_le_mul_of_weightVector
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n) {v : n → F}
    (hv : IsCocharacterEigenvector χ ρ v) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).rationalPoints,
      rationalVectorNorm F v ≤
        C * rationalVectorNorm F ((ρ.rationalMatrix x : Matrix n n F) *ᵥ v) := by
  obtain ⟨g, e, hg⟩ := exists_innerIso_comp_eq_diagonalCocharacter F (χ ≫ ρ)
  have hχ : χ ≫ ρ ≫ ((groupScheme n (CommRingCat.of F)).innerIso g).hom =
      diagonalCocharacter n (CommRingCat.of F) e := by
    rw [← Category.assoc, hg]
  let t : Fˣ := Units.mk0 (LocalField.uniformizer F) (LocalField.uniformizer_ne_zero F)
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have : IsUltrametricDist F :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (LocalField.residueNormalizedAbsoluteValue_add_le_max F)
  have hq1 : (1 : ℝ) < (LocalField.residueCardinality F : ℝ) := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  have ht : ‖(t : F)‖ ≠ 1 := by
    have htn : ‖(t : F)‖ = (LocalField.residueCardinality F : ℝ)⁻¹ :=
      LocalField.residueNormalizedAbsoluteValue_of_ord_one F (LocalField.ord_uniformizer F)
    rw [htn]
    exact (inv_lt_one_of_one_lt₀ hq1).ne
  obtain ⟨c, hc⟩ := hv t
  have hdiag : (diagonalUnits F e t : Matrix n n F) *ᵥ
      ((rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F) *ᵥ v) =
      c • ((rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F) *ᵥ v) := by
    rw [← rationalMatrix_gmRationalPoint_comp hχ t, rationalMatrix_comp_innerIso_mulVec, hc,
      Matrix.mulVec_smul]
  obtain ⟨m, hwm⟩ := HarishChandraSchwartz.exists_weight_block_of_mulVec_eq_smul ht hdiag
  obtain ⟨K, hK, hKb⟩ := HarishChandraSchwartz.exists_norm_mulVec_le
    (rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F)
  obtain ⟨K', hK', hK'b⟩ := HarishChandraSchwartz.exists_norm_mulVec_le
    (((rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g)⁻¹ : GL n F) : Matrix n n F)
  have hpos : 0 < max 1 K' * max 1 K :=
    mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (zero_lt_one.trans_le (le_max_left _ _))
  refine ⟨max 1 K' * max 1 K, hpos, fun x hx => ?_⟩
  have hρU : rationalMatrix (ρ ≫ ((groupScheme n (CommRingCat.of F)).innerIso g).hom) x ∈
      blockUnipotentSubgroup F (-e) := by
    rw [rationalMatrix_mem_blockUnipotentSubgroup_iff]
    have h := Dynamic.unipotent_le_comap _
      (ρ ≫ ((groupScheme n (CommRingCat.of F)).innerIso g).hom) _ hx
    rw [SubgroupFunctor.mem_comap, Dynamic.oppositeCocharacter, Category.assoc, hχ,
      inv_comp_diagonalCocharacter, unipotent_diagonalCocharacter] at h
    exact h
  have hw : ‖(rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F) *ᵥ v‖ ≤
      ‖(rationalMatrix (ρ ≫ ((groupScheme n (CommRingCat.of F)).innerIso g).hom) x :
          Matrix n n F) *ᵥ
        ((rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F) *ᵥ v)‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    by_cases hi : e i = m
    · rw [← HarishChandraSchwartz.mulVec_apply_eq_of_mem_blockUnipotentSubgroup hρU hwm hi]
      exact norm_le_pi_norm _ i
    · rw [hwm i hi, norm_zero]
      exact norm_nonneg _
  rw [rationalMatrix_comp_innerIso_mulVec] at hw
  have hv' : v = (((rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g)⁻¹ : GL n F) :
      Matrix n n F) *ᵥ
        ((rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  change ‖v‖ ≤ max 1 K' * max 1 K * ‖(ρ.rationalMatrix x : Matrix n n F) *ᵥ v‖
  calc ‖v‖ = ‖(((rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g)⁻¹ : GL n F) :
          Matrix n n F) *ᵥ
        ((rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F) *ᵥ v)‖ := by
        rw [← hv']
    _ ≤ K' * ‖(rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F) *ᵥ v‖ :=
        hK'b _
    _ ≤ K' * ‖(rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F) *ᵥ
          ((ρ.rationalMatrix x : Matrix n n F) *ᵥ v)‖ := mul_le_mul_of_nonneg_left hw hK'
    _ ≤ K' * (K * ‖(ρ.rationalMatrix x : Matrix n n F) *ᵥ v‖) :=
        mul_le_mul_of_nonneg_left (hKb _) hK'
    _ ≤ max 1 K' * max 1 K * ‖(ρ.rationalMatrix x : Matrix n n F) *ᵥ v‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (le_max_right _ _) (le_max_right _ _) hK
            (zero_lt_one.trans_le (le_max_left _ _)).le) (norm_nonneg _)

/-- On a compact set `K` of rational points, `‖ρ(k⁻¹) v‖` is bounded. -/
theorem exists_rationalVectorNorm_mulVec_inv_le [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (v : n → F) {K : Set (rationalPoints G)}
    (hK : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k ∈ K,
      rationalVectorNorm F ((ρ.rationalMatrix k⁻¹ : Matrix n n F) *ᵥ v) ≤ B := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have hinv : Continuous fun g : rationalPoints G => g⁻¹ := continuous_rationalPoint_inv F G
  have hi : ∀ i, Continuous fun g : rationalPoints G =>
      LocalField.residueNormalizedAbsoluteValue F
        (((ρ.rationalMatrix g⁻¹ : Matrix n n F) *ᵥ v) i) := by
    intro i
    refine (Plancherel.continuous_residueNormalizedAbsoluteValue F).comp ?_
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun l _ =>
      ((ρ.continuous_rationalMatrix_entry i l).comp hinv).mul continuous_const
  have hc : Continuous fun g : rationalPoints G =>
      rationalVectorNorm F ((ρ.rationalMatrix g⁻¹ : Matrix n n F) *ᵥ v) :=
    HarishChandraSchwartz.continuous_norm_pi_comp hi
  obtain ⟨B, hB⟩ := (hK.image hc).isBounded.subset_closedBall 0
  refine ⟨max B 0, le_max_right _ _, fun k hk => ?_⟩
  have h1 := hB (Set.mem_image_of_mem _ hk)
  rw [Metric.mem_closedBall, Real.dist_0_eq_abs] at h1
  exact (le_abs_self _).trans (h1.trans (le_max_left _ _))

/-- **Iwasawa bounds for the parabolic line.** Let `χ` be a cocharacter of an affine group `G`
of finite type over a non-archimedean local field `F`, `ρ₀` a closed representation and `K` a
compact set of rational points. There are a representation `ρ` and a basis vector `e j` whose
line has stabilizer `P(χ)(F)`, with line character `χ_P`, such that for every `x ∈ Ū(F)` and
every factorization `x = p k` with `p ∈ P(χ)(F)` and `k ∈ K`:
* `|χ_P(p)| ≤ C₁`, and
* the `ρ₀`-height of `x` is at most `C₂ * max 1 |χ_P(p)|⁻¹ ^ D`. -/
theorem exists_parabolic_line_character_bounds [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] [IsAffine G.X.left] (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N))
    (hρ₀ : IsClosedSubgroup ρ₀) {K : Set (rationalPoints G)}
    (hK : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact K) :
    ∃ (n : ℕ) (j : Fin (n + 1)) (ρ : MatrixRepresentation G (Fin (n + 1)))
      (h : IsRationalLineStabilizer ρ j (Dynamic.parabolic χ).rationalPoints),
      (∃ C : ℝ, ∀ x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).rationalPoints,
        ∀ (p : (Dynamic.parabolic χ).rationalPoints), ∀ k ∈ K, x = (p : rationalPoints G) * k →
          LocalField.residueNormalizedAbsoluteValue F (h.character p : F) ≤ C) ∧
      ∃ C : ℝ, ∃ D : ℕ, 0 < C ∧
        ∀ x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).rationalPoints,
          ∀ (p : (Dynamic.parabolic χ).rationalPoints), ∀ k ∈ K,
            x = (p : rationalPoints G) * k →
              rationalMatrixNorm F ρ₀ x ≤ C * max 1
                (LocalField.residueNormalizedAbsoluteValue F (h.character p : F))⁻¹ ^ D := by
  obtain ⟨n, j, ρ, h, C, D, hC, hb⟩ := exists_parabolic_line_rationalMatrixNorm_le F χ ρ₀ hρ₀
  have hv : IsCocharacterEigenvector χ ρ (Pi.single j 1) := fun t => by
    obtain ⟨u, hu⟩ := h.exists_unit_of_mem (gmRationalPoint_comp_mem_parabolic χ t)
    exact ⟨u, hu⟩
  obtain ⟨C', hC', hlow⟩ := exists_rationalVectorNorm_le_mul_of_weightVector F χ ρ hv
  obtain ⟨B, hB, hBK⟩ := exists_rationalVectorNorm_mulVec_inv_le F ρ (Pi.single j 1) hK
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have hnorm : ∀ (p : (Dynamic.parabolic χ).rationalPoints) (k : rationalPoints G),
      rationalVectorNorm F
          ((ρ.rationalMatrix ((p : rationalPoints G) * k)⁻¹ : Matrix (Fin (n + 1))
            (Fin (n + 1)) F) *ᵥ Pi.single j 1) =
        (LocalField.residueNormalizedAbsoluteValue F (h.character p : F))⁻¹ *
          rationalVectorNorm F ((ρ.rationalMatrix k⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ
            Pi.single j 1) := by
    intro p k
    change ‖_‖ = _ * ‖_‖
    rw [h.mulVec_mul_inv p k, norm_smul, Units.val_inv_eq_inv_val, norm_inv]
    rfl
  have hsingle : rationalVectorNorm F (Pi.single j (1 : F) : Fin (n + 1) → F) = 1 := by
    change ‖(Pi.single j (1 : F) : Fin (n + 1) → F)‖ = 1
    rw [Pi.norm_single, norm_one]
  have habs_pos : ∀ p : (Dynamic.parabolic χ).rationalPoints,
      0 < LocalField.residueNormalizedAbsoluteValue F (h.character p : F) := fun p =>
    (LocalField.residueNormalizedAbsoluteValue F).pos (h.character p).ne_zero
  refine ⟨n, j, ρ, h, ⟨C' * B, fun x hx p k hk hxpk => ?_⟩,
    ⟨C * max 1 B ^ D, D, mul_pos hC (pow_pos (zero_lt_one.trans_le (le_max_left _ _)) D),
      fun x hx p k hk hxpk => ?_⟩⟩
  · subst hxpk
    have h1 := hlow _ (Subgroup.inv_mem _ hx)
    rw [hsingle, hnorm p k] at h1
    have hpos := habs_pos p
    have h2 := hBK k hk
    have h3 : 1 ≤ C' * B * (LocalField.residueNormalizedAbsoluteValue F (h.character p : F))⁻¹ := by
      calc (1 : ℝ) ≤ C' * ((LocalField.residueNormalizedAbsoluteValue F (h.character p : F))⁻¹ *
            rationalVectorNorm F ((ρ.rationalMatrix k⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ
              Pi.single j 1)) := h1
        _ ≤ C' * ((LocalField.residueNormalizedAbsoluteValue F (h.character p : F))⁻¹ * B) := by
            gcongr
        _ = _ := by ring
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul] at h3
    exact h3
  · subst hxpk
    have h1 := hb _ (Subgroup.inv_mem _ hx)
    rw [rationalMatrixNorm_inv, hnorm p k] at h1
    refine h1.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    rw [← mul_pow]
    refine pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) ?_ D
    have hinvpos := (inv_pos.2 (habs_pos p)).le
    have h2 := hBK k hk
    refine max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)) ?_
    calc (LocalField.residueNormalizedAbsoluteValue F (h.character p : F))⁻¹ *
          rationalVectorNorm F ((ρ.rationalMatrix k⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ
            Pi.single j 1)
        ≤ max 1 (LocalField.residueNormalizedAbsoluteValue F (h.character p : F))⁻¹ * max 1 B :=
          mul_le_mul (le_max_right _ _) (h2.trans (le_max_right _ _))
            (by change 0 ≤ ‖_‖; exact norm_nonneg _) (zero_le_one.trans (le_max_left _ _))
      _ = max 1 B * max 1 (LocalField.residueNormalizedAbsoluteValue F (h.character p : F))⁻¹ :=
          mul_comm _ _

end LocalField

end Langlands.GroupScheme.MatrixRepresentation
