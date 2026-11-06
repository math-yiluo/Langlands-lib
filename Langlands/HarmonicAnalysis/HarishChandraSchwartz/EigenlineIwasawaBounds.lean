import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicLineCharacter
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnipotentIntersectionProduct
import Langlands.GroupScheme.Dynamic.PositiveWeightParabolicDistinction

/-! # Iwasawa bounds for eigenlines of a dynamic parabolic and of its Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix Filter Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section Eigenline

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n] {ρ : MatrixRepresentation G n} {v : n → k}
  {S : Subgroup (rationalPoints G)} {c : rationalPoints G → k}

variable (ρ v S c) in
/-- **Common eigenvectors.** `v` is an eigenvector of `ρ(x)` with eigenvalue `c x` for every
`x ∈ S`. -/
def IsEigenvectorOn : Prop :=
  ∀ x ∈ S, (ρ.rationalMatrix x : Matrix n n k) *ᵥ v = c x • v

/-- Eigenvalues on a common nonzero eigenvector of a subgroup are multiplicative. -/
theorem eigenvalue_mul (hv : v ≠ 0)
    (hc : IsEigenvectorOn ρ v S c)
    {x y : rationalPoints G} (hx : x ∈ S) (hy : y ∈ S) : c (x * y) = c x * c y := by
  apply smul_left_injective k hv
  change c (x * y) • v = (c x * c y) • v
  rw [← hc _ (S.mul_mem hx hy), map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hc y hy,
    Matrix.mulVec_smul, hc x hx, smul_smul, mul_comm]

/-- The eigenvalue of the identity is `1`. -/
theorem eigenvalue_one (hv : v ≠ 0)
    (hc : IsEigenvectorOn ρ v S c) : c 1 = 1 := by
  apply smul_left_injective k hv
  change c 1 • v = (1 : k) • v
  rw [← hc 1 S.one_mem, map_one, Units.val_one, Matrix.one_mulVec, one_smul]

/-- The eigenvalue of an inverse is the inverse eigenvalue. -/
theorem eigenvalue_mul_inv (hv : v ≠ 0)
    (hc : IsEigenvectorOn ρ v S c)
    {x : rationalPoints G} (hx : x ∈ S) : c x * c x⁻¹ = 1 := by
  rw [← eigenvalue_mul hv hc hx (S.inv_mem hx), mul_inv_cancel, eigenvalue_one hv hc]

end Eigenline

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- **Unipotent points act trivially on an eigenline of the parabolic.** If a subgroup `S`
containing `P(χ)(F)` acts on a nonzero vector `v` by scalars `c`, then `c x = 1` for every
`x ∈ U(χ)(F)`. -/
theorem eigenvalue_eq_one_of_mem_unipotent [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (ρ : MatrixRepresentation G n)
    {v : n → F} (hv : v ≠ 0) {S : Subgroup (rationalPoints G)}
    (hPS : (Dynamic.parabolic χ).rationalPoints ≤ S) {c : rationalPoints G → F}
    (hc : IsEigenvectorOn ρ v S c)
    {x : rationalPoints G} (hx : x ∈ (Dynamic.unipotent χ).rationalPoints) : c x = 1 := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  obtain ⟨t, ht⟩ := BruhatTits.DynamicUnipotentContainment.exists_unit_tendsto_pow_zero (F := F)
  set a : rationalPoints G := gmRationalPoint t ≫ χ.hom.hom with ha_def
  have ha : a ∈ S := hPS (gmRationalPoint_comp_mem_parabolic χ t)
  have hxS : x ∈ S := hPS (Dynamic.unipotent_le_parabolic χ _ hx)
  have hlim := (mem_unipotent_iff_tendsto_conj F χ t ht x).1 hx
  have hcn : ∀ m : ℕ, c (a ^ m * x * (a ^ m)⁻¹) = c x := by
    intro m
    have ham : a ^ m ∈ S := S.pow_mem ha m
    rw [eigenvalue_mul hv hc (S.mul_mem ham hxS) (S.inv_mem ham), eigenvalue_mul hv hc ham hxS,
      mul_comm (c (a ^ m)) (c x), mul_assoc, eigenvalue_mul_inv hv hc ham, mul_one]
  have hcont : Continuous fun g : rationalPoints G =>
      (ρ.rationalMatrix g : Matrix n n F) *ᵥ v := by
    refine continuous_pi fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun l _ =>
      (continuous_rationalMatrix_entry ρ i l).mul continuous_const
  have h1 : Tendsto (fun m : ℕ => (ρ.rationalMatrix (a ^ m * x * (a ^ m)⁻¹) :
      Matrix n n F) *ᵥ v) atTop (𝓝 ((ρ.rationalMatrix 1 : Matrix n n F) *ᵥ v)) :=
    (hcont.tendsto 1).comp hlim
  have h2 : (fun m : ℕ => (ρ.rationalMatrix (a ^ m * x * (a ^ m)⁻¹) :
      Matrix n n F) *ᵥ v) = fun _ => c x • v := by
    funext m
    rw [hc _ (S.mul_mem (S.mul_mem (S.pow_mem ha m) hxS) (S.inv_mem (S.pow_mem ha m))), hcn m]
  rw [h2, map_one, Units.val_one, Matrix.one_mulVec] at h1
  have h3 : c x • v = v := tendsto_nhds_unique tendsto_const_nhds h1
  apply smul_left_injective F hv
  change c x • v = (1 : F) • v
  rw [h3, one_smul]

/-- **Upper Iwasawa bound for an eigenline of the parabolic.** Let `P(χ)(F)` act on a nonzero
vector `v` by scalars `c`. For a compact set `K` there is `C` with `|c p| ≤ C` whenever
`x = p κ` with `x ∈ Ū(F)`, `p ∈ P(χ)(F)` and `κ ∈ K`. -/
theorem exists_abs_eigenvalue_le [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (ρ : MatrixRepresentation G n)
    {v : n → F} (hv : v ≠ 0) {c : rationalPoints G → F}
    (hc : IsEigenvectorOn ρ v (Dynamic.parabolic χ).rationalPoints c)
    {K : Set (rationalPoints G)}
    (hK : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact K) :
    ∃ C : ℝ, ∀ x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).rationalPoints,
      ∀ p ∈ (Dynamic.parabolic χ).rationalPoints, ∀ κ ∈ K, x = p * κ →
        LocalField.residueNormalizedAbsoluteValue F (c p) ≤ C := by
  have hev : IsCocharacterEigenvector χ ρ v := fun t =>
    ⟨_, hc _ (gmRationalPoint_comp_mem_parabolic χ t)⟩
  obtain ⟨C', hC', hlow⟩ := exists_rationalVectorNorm_le_mul_of_weightVector F χ ρ hev
  obtain ⟨B, hB, hBK⟩ := exists_rationalVectorNorm_mulVec_inv_le F ρ v hK
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  refine ⟨C' * B / ‖v‖, fun x hx p hp κ hκ hxpκ => ?_⟩
  subst hxpκ
  have hinv := eigenvalue_mul_inv hv hc hp
  have hcp : c p ≠ 0 := left_ne_zero_of_mul_eq_one hinv
  have hvec : (ρ.rationalMatrix (p * κ)⁻¹ : Matrix n n F) *ᵥ v =
      c p⁻¹ • ((ρ.rationalMatrix κ⁻¹ : Matrix n n F) *ᵥ v) := by
    rw [_root_.mul_inv_rev, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      hc _ ((Dynamic.parabolic χ).rationalPoints.inv_mem hp), Matrix.mulVec_smul]
  have h1 := hlow _ ((Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).rationalPoints.inv_mem hx)
  change ‖v‖ ≤ C' * ‖(ρ.rationalMatrix (p * κ)⁻¹ : Matrix n n F) *ᵥ v‖ at h1
  rw [hvec, norm_smul] at h1
  have h2 : ‖(ρ.rationalMatrix κ⁻¹ : Matrix n n F) *ᵥ v‖ ≤ B := hBK κ hκ
  have hcinv : ‖c p⁻¹‖ = ‖c p‖⁻¹ := by
    rw [eq_inv_of_mul_eq_one_right hinv, norm_inv]
  rw [hcinv] at h1
  have hpos : 0 < ‖c p‖ := norm_pos_iff.2 hcp
  change ‖c p‖ ≤ C' * B / ‖v‖
  rw [le_div_iff₀ hvpos]
  calc ‖c p‖ * ‖v‖ ≤ ‖c p‖ * (C' * (‖c p‖⁻¹ * B)) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hpos.le)) hC'.le)
    _ = C' * B := by field_simp

/-- **Lower Iwasawa bound for an eigenline of the Levi.** Let `Z(χ)(F)` act on a nonzero vector
`v` by scalars `c`. For a compact set `K` there is `C > 0` with `C ≤ |c m|` whenever
`x = m u κ` with `m ∈ Z(χ)(F)`, `u ∈ U(χ)(F)`, `κ ∈ K` and `x` fixes `v`. -/
theorem exists_le_abs_eigenvalue [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (ρ : MatrixRepresentation G n)
    {v : n → F} (hv : v ≠ 0) {c : rationalPoints G → F}
    (hc : IsEigenvectorOn ρ v (Dynamic.centralizer χ).rationalPoints c)
    {K : Set (rationalPoints G)}
    (hK : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x m u κ : rationalPoints G,
      m ∈ (Dynamic.centralizer χ).rationalPoints → u ∈ (Dynamic.unipotent χ).rationalPoints →
        κ ∈ K → x = m * u * κ → (ρ.rationalMatrix x : Matrix n n F) *ᵥ v = v →
          C ≤ LocalField.residueNormalizedAbsoluteValue F (c m) := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  have hev : IsCocharacterEigenvector (Dynamic.oppositeCocharacter χ) ρ v := by
    intro t
    have hr := Dynamic.range_comp_le_centralizer_comp χ
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) (-1))) (𝟙 _)
    rw [Category.id_comp] at hr
    exact ⟨_, hc _ (hr _ (SubgroupFunctor.mem_range.mpr ⟨gmRationalPoint t, rfl⟩))⟩
  obtain ⟨C', hC', hlow⟩ :=
    exists_rationalVectorNorm_le_mul_of_weightVector F (Dynamic.oppositeCocharacter χ) ρ hev
  rw [Dynamic.oppositeCocharacter_oppositeCocharacter] at hlow
  have hKi : IsCompact ((fun g : rationalPoints G => g⁻¹) '' K) :=
    hK.image (continuous_rationalPoint_inv F G)
  obtain ⟨B, hB, hBK⟩ := exists_rationalVectorNorm_mulVec_inv_le F ρ v hKi
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  refine ⟨‖v‖ / (C' * max B 1), div_pos hvpos (mul_pos hC' (lt_max_of_lt_right one_pos)),
    fun x m u κ hm hu hκ hx hxv => ?_⟩
  have hinv := eigenvalue_mul_inv hv hc hm
  have hcm : c m ≠ 0 := left_ne_zero_of_mul_eq_one hinv
  -- `ρ(κ) v = c(m⁻¹) ρ(u⁻¹) v`
  have hvec : (ρ.rationalMatrix κ : Matrix n n F) *ᵥ v =
      c m⁻¹ • ((ρ.rationalMatrix u⁻¹ : Matrix n n F) *ᵥ v) := by
    have hκ' : κ = u⁻¹ * m⁻¹ * x := by
      rw [hx]
      group
    rw [hκ', map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hxv, hc _ ((Dynamic.centralizer χ).rationalPoints.inv_mem hm),
      Matrix.mulVec_smul]
  have h1 := hlow _ ((Dynamic.unipotent χ).rationalPoints.inv_mem hu)
  change ‖v‖ ≤ C' * ‖(ρ.rationalMatrix u⁻¹ : Matrix n n F) *ᵥ v‖ at h1
  have h2 : ‖(ρ.rationalMatrix κ : Matrix n n F) *ᵥ v‖ ≤ B := by
    have := hBK κ⁻¹ ⟨κ, hκ, rfl⟩
    rwa [inv_inv] at this
  rw [hvec, norm_smul, eq_inv_of_mul_eq_one_right hinv, norm_inv] at h2
  have hpos : 0 < ‖c m‖ := norm_pos_iff.2 hcm
  have h3 : ‖(ρ.rationalMatrix u⁻¹ : Matrix n n F) *ᵥ v‖ ≤ ‖c m‖ * max B 1 := by
    rw [inv_mul_le_iff₀ hpos] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hpos.le)
  change ‖v‖ / (C' * max B 1) ≤ ‖c m‖
  rw [div_le_iff₀ (mul_pos hC' (lt_max_of_lt_right one_pos))]
  calc ‖v‖ ≤ C' * (‖c m‖ * max B 1) := h1.trans (mul_le_mul_of_nonneg_left h3 hC'.le)
    _ = ‖c m‖ * (C' * max B 1) := by ring

end LocalField

end Langlands.GroupScheme.MatrixRepresentation
