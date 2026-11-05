import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OppositeUnipotentDisplacement
import Langlands.BruhatTits.Unipotent.CocharacterContraction
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Dynamic.OppositeBaseChange
import Langlands.GroupScheme.Rational.PointDecomposition
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OpenCellPoints
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OpenCellIntersectionProduct

/-! # Contraction criterion and products of dynamic unipotent rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix Filter Topology
open Langlands.GroupScheme.GeneralLinear
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section Bridge

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}

/-- The intrinsic cocharacter point `χ(t)` is the composite of the rational point `t` of `𝔾_m`
with `χ`. -/
theorem cocharPoint_eq_gmRationalPoint_comp (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (t : Fˣ) :
    BruhatTits.DynamicUnipotentContainment.cocharPoint χ t = gmRationalPoint t ≫ χ.hom.hom := by
  rw [BruhatTits.DynamicUnipotentContainment.cocharPoint_eq]
  congr 1

end Bridge

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

/-- If the field powers `t ^ n` converge to `0`, then `|t| ≤ 1`. -/
theorem residueNormalizedAbsoluteValue_le_one_of_tendsto_pow {t : F}
    (ht : Tendsto (fun n : ℕ => t ^ n) atTop (𝓝 0)) :
    LocalField.residueNormalizedAbsoluteValue F t ≤ 1 := by
  by_contra h'
  have h := not_le.mp h'
  have hlim : Tendsto (fun n : ℕ => LocalField.residueNormalizedAbsoluteValue F (t ^ n)) atTop
      (𝓝 (LocalField.residueNormalizedAbsoluteValue F 0)) :=
    ((Plancherel.continuous_residueNormalizedAbsoluteValue F).tendsto 0).comp ht
  rw [map_zero] at hlim
  have hge : ∀ n : ℕ, 1 ≤ LocalField.residueNormalizedAbsoluteValue F (t ^ n) := by
    intro n
    rw [map_pow]
    exact one_le_pow₀ h.le
  have := ge_of_tendsto' hlim hge
  linarith

/-- **Contraction criterion, diagonal form.** Let `ξ` be a cocharacter of `G` and `ρ₁` a
representation with `ξ ≫ ρ₁ = diag(t ^ e i)`. If the powers `t ^ n` converge to `0` and
`ξ(t) ^ n y ξ(t)⁻ⁿ → 1`, then the matrix of `y` is block unipotent for `e`. -/
theorem rationalMatrix_mem_blockUnipotentSubgroup_of_tendsto
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) {N : ℕ}
    (ρ₁ : MatrixRepresentation G (Fin N)) {e : Fin N → ℤ}
    (hξ : ξ ≫ ρ₁ = diagonalCocharacter (Fin N) (CommRingCat.of F) e)
    (t : Fˣ) (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0)) (y : rationalPoints G)
    (hy : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      Tendsto (fun n : ℕ => (gmRationalPoint t ≫ ξ.hom.hom) ^ n * y *
        ((gmRationalPoint t ≫ ξ.hom.hom) ^ n)⁻¹) atTop (𝓝 1)) :
    ρ₁.rationalMatrix y ∈ blockUnipotentSubgroup F e := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  have ht1 := residueNormalizedAbsoluteValue_le_one_of_tendsto_pow F ht
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have hD : ρ₁.rationalMatrix (gmRationalPoint t ≫ ξ.hom.hom) = diagonalUnits F e t :=
    rationalMatrix_gmRationalPoint_comp hξ t
  -- Entries of the conjugates.
  have hentry : ∀ (n : ℕ) (i j : Fin N),
      (ρ₁.rationalMatrix ((gmRationalPoint t ≫ ξ.hom.hom) ^ n * y *
        ((gmRationalPoint t ≫ ξ.hom.hom) ^ n)⁻¹) : Matrix (Fin N) (Fin N) F) i j =
        (((t ^ n)⁻¹ : Fˣ) : F) ^ (e j - e i) *
          (ρ₁.rationalMatrix y : Matrix (Fin N) (Fin N) F) i j := by
    intro n i j
    rw [← HarishChandraSchwartz.diagonalUnits_conj_apply e ((t ^ n)⁻¹)]
    rw [map_mul, map_mul, map_inv, map_pow, hD, map_inv, map_pow, inv_inv]
  have hlim : ∀ i j : Fin N, Tendsto (fun n : ℕ =>
      (((t ^ n)⁻¹ : Fˣ) : F) ^ (e j - e i) * (ρ₁.rationalMatrix y : Matrix (Fin N) (Fin N) F) i j)
      atTop (𝓝 ((1 : Matrix (Fin N) (Fin N) F) i j)) := by
    intro i j
    have h := ((ρ₁.continuous_rationalMatrix_entry i j).tendsto 1).comp hy
    rw [map_one, Units.val_one] at h
    convert h using 1
    funext n
    exact (hentry n i j).symm
  intro i j hij
  rcases hij.lt_or_eq with hlt | heq
  · -- Different weights: the entry is multiplied by a factor of absolute value at least `1`.
    have hne : i ≠ j := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
    have hl := hlim i j
    rw [Matrix.one_apply_ne hne] at hl ⊢
    have habs := ((Plancherel.continuous_residueNormalizedAbsoluteValue F).tendsto 0).comp hl
    rw [map_zero] at habs
    have hge : ∀ n : ℕ, LocalField.residueNormalizedAbsoluteValue F
        ((ρ₁.rationalMatrix y : Matrix (Fin N) (Fin N) F) i j) ≤
        LocalField.residueNormalizedAbsoluteValue F
          ((((t ^ n)⁻¹ : Fˣ) : F) ^ (e j - e i) *
            (ρ₁.rationalMatrix y : Matrix (Fin N) (Fin N) F) i j) := by
      intro n
      change ‖(ρ₁.rationalMatrix y : Matrix (Fin N) (Fin N) F) i j‖ ≤
        ‖(((t ^ n)⁻¹ : Fˣ) : F) ^ (e j - e i) *
          (ρ₁.rationalMatrix y : Matrix (Fin N) (Fin N) F) i j‖
      rw [norm_mul, norm_zpow]
      refine le_mul_of_one_le_left (norm_nonneg _) (one_le_zpow₀ ?_ (by omega))
      rw [Units.val_inv_eq_inv_val, norm_inv, Units.val_pow_eq_pow_val, norm_pow]
      exact one_le_inv₀ (pow_pos (norm_pos_iff.mpr t.ne_zero) n) |>.mpr
        (pow_le_one₀ (norm_nonneg _) ht1)
    have hle := ge_of_tendsto' habs hge
    have h0 : LocalField.residueNormalizedAbsoluteValue F
        ((ρ₁.rationalMatrix y : Matrix (Fin N) (Fin N) F) i j) = 0 :=
      le_antisymm hle (AbsoluteValue.nonneg _ _)
    exact (AbsoluteValue.eq_zero _).mp h0
  · -- Equal weights: the entry is constant.
    have h := hlim i j
    simp only [heq, sub_self, zpow_zero, one_mul] at h
    exact tendsto_nhds_unique tendsto_const_nhds h

/-- **Contraction criterion.** Let `ξ` be a cocharacter of `G` and `ρ₀` a closed
representation. If `t ^ n → 0` and `ξ(t) ^ n y ξ(t)⁻ⁿ → 1`, then `y ∈ U(ξ)(F)`. -/
theorem mem_unipotent_of_tendsto_conj
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) {N : ℕ}
    (ρ₀ : MatrixRepresentation G (Fin N)) (hρ₀ : IsClosedSubgroup ρ₀)
    (t : Fˣ) (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0)) (y : rationalPoints G)
    (hy : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      Tendsto (fun n : ℕ => (gmRationalPoint t ≫ ξ.hom.hom) ^ n * y *
        ((gmRationalPoint t ≫ ξ.hom.hom) ^ n)⁻¹) atTop (𝓝 1)) :
    y ∈ (Dynamic.unipotent ξ).rationalPoints := by
  obtain ⟨g₀, e, hg₀⟩ := exists_innerIso_comp_eq_diagonalCocharacter F (ξ ≫ ρ₀)
  have hcl : IsClosedSubgroup
      (ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom) :=
    hρ₀.comp_iso _
  have hξ₁ : ξ ≫ ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom =
      diagonalCocharacter (Fin N) (CommRingCat.of F) e := by
    rw [← Category.assoc, hg₀]
  generalize ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom = ρ₁
    at hcl hξ₁
  have : IsClosedImmersion ρ₁.hom.hom.left := hcl
  have hχ₁ : (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ ξ) ≫ ρ₁ =
      diagonalCocharacter (Fin N) (CommRingCat.of F) (-e) := by
    rw [Category.assoc, hξ₁, inv_comp_diagonalCocharacter]
  have hblock := rationalMatrix_mem_blockUnipotentSubgroup_of_tendsto F ξ ρ₁ hξ₁ t ht y hy
  rw [← neg_neg e, rationalMatrix_mem_blockUnipotentSubgroup_iff] at hblock
  have hmem := (Dynamic.mem_unipotent_iff_of_diagonal hχ₁ y).2 hblock
  rwa [Dynamic.powerHom_neg_one_comp_powerHom_neg_one] at hmem

variable [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]

/-- **Contraction characterizes `U(ξ)(F)`.** For an affine group of finite type over a
non-archimedean local field, a cocharacter `ξ` and `t ∈ Fˣ` with `t ^ n → 0`, a rational point
`y` lies in `U(ξ)(F)` if and only if `ξ(t) ^ n y ξ(t)⁻ⁿ → 1`. -/
theorem mem_unipotent_iff_tendsto_conj
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (t : Fˣ) (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0)) (y : rationalPoints G) :
    y ∈ (Dynamic.unipotent ξ).rationalPoints ↔
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      Tendsto (fun n : ℕ => (gmRationalPoint t ≫ ξ.hom.hom) ^ n * y *
        ((gmRationalPoint t ≫ ξ.hom.hom) ^ n)⁻¹) atTop (𝓝 1) := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  constructor
  · intro hyU
    have h := BruhatTits.DynamicUnipotentContainment.tendsto_cocharPoint_pow_conj ξ t ht ⟨y, hyU⟩
    have h' := h.comp (tendsto_id.prodMk (tendsto_const_nhds (x := (⟨y, hyU⟩ :
      BruhatTits.DynamicUnipotentContainment.unipotentPoints ξ))))
    simpa only [Function.comp_def, id, cocharPoint_eq_gmRationalPoint_comp] using h'
  · intro hy
    obtain ⟨N, ρ₀, hρ₀⟩ := affineLinearEmbeddingStatement F G ‹_› ‹_›
    exact mem_unipotent_of_tendsto_conj F ξ ρ₀ hρ₀ t ht y hy

local instance unipotentIntersectionProductTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- A rational point commuting with `ξ(t)` normalizes `U(ξ)(F)`. -/
theorem mem_normalizer_unipotent_of_commute
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (t : Fˣ) (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0)) {c : rationalPoints G}
    (hc : Commute c (gmRationalPoint t ≫ ξ.hom.hom)) :
    c ∈ Subgroup.normalizer ((Dynamic.unipotent ξ).rationalPoints : Set (rationalPoints G)) := by
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [mem_unipotent_iff_tendsto_conj F ξ t ht, mem_unipotent_iff_tendsto_conj F ξ t ht]
  set a := gmRationalPoint t ≫ ξ.hom.hom
  have key : ∀ n : ℕ, a ^ n * (c * h * c⁻¹) * (a ^ n)⁻¹ = c * (a ^ n * h * (a ^ n)⁻¹) * c⁻¹ := by
    intro n
    have hcn : a ^ n * c = c * a ^ n := (hc.pow_right n).eq.symm
    calc a ^ n * (c * h * c⁻¹) * (a ^ n)⁻¹
        = (a ^ n * c) * h * (a ^ n * c)⁻¹ := by group
      _ = (c * a ^ n) * h * (c * a ^ n)⁻¹ := by rw [hcn]
      _ = c * (a ^ n * h * (a ^ n)⁻¹) * c⁻¹ := by group
  simp_rw [key]
  have hcont : ∀ g : rationalPoints G, Continuous fun x : rationalPoints G => g * x * g⁻¹ :=
    fun g => (continuous_const.mul continuous_id).mul continuous_const
  constructor
  · intro hlim
    simpa [Function.comp_def] using ((hcont c).tendsto 1).comp hlim
  · intro hlim
    have h2 := ((hcont c⁻¹).tendsto 1).comp hlim
    simpa [Function.comp_def, mul_assoc] using h2

variable [Smooth G.X.hom]

/-- **The open-cell contraction data of two commuting cocharacters.** Let `χ`, `ξ` be
cocharacters of a smooth affine group `G` of finite type over a non-archimedean local field,
`t ∈ Fˣ` with `t ^ n → 0`, and suppose `ξ(t)` lies in `Z(χ)(F)` and `Z(χ)(F) ∩ U(ξ)(F) = 1`.
Then the open cell `P(χ)(F) × U(χ⁻¹)(F) → G(F)`, the Levi decomposition of `P(χ)(F)` and
conjugation by `ξ(t)` and `χ(t)` satisfy `IsOpenCellContraction`, with target `U(ξ)(F)`. -/
theorem isOpenCellContraction_dynamic
    (χ ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (t : Fˣ) (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    (hξ : gmRationalPoint t ≫ ξ.hom.hom ∈ (Dynamic.centralizer χ).rationalPoints)
    (hZU : ∀ m ∈ (Dynamic.centralizer χ).rationalPoints,
      m ∈ (Dynamic.unipotent ξ).rationalPoints → m = 1) :
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    HarishChandraSchwartz.IsOpenCellContraction
      (Dynamic.parabolic χ).rationalPoints
      (Dynamic.unipotent (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).rationalPoints
      (Dynamic.unipotent χ).rationalPoints
      (Dynamic.unipotent ξ).rationalPoints
      (Dynamic.centralizer χ).rationalPoints
      (gmRationalPoint t ≫ ξ.hom.hom) (gmRationalPoint t ≫ χ.hom.hom) := by
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have : IsOpenUnits F := inferInstance
  have hcomm : Commute (gmRationalPoint t ≫ ξ.hom.hom) (gmRationalPoint t ≫ χ.hom.hom) := by
    have h := BruhatTits.DynamicUnipotentContainment.commute_cocharPoint χ hξ t
    rwa [cocharPoint_eq_gmRationalPoint_comp] at h
  have hξ' : gmRationalPoint t ≫ ξ.hom.hom ∈
      (Dynamic.centralizer (Dynamic.inverseCocharacter χ)).rationalPoints := by
    rw [Dynamic.centralizer_inverseCocharacter]
    exact hξ
  exact
    { isOpenEmbedding := HarishChandraSchwartz.isOpenEmbedding_openCellMap_rationalPoint F G χ
      unipotent_le := RationalPoint.unipotent_le_parabolic χ
      mem_normalizer_parabolic :=
        Subgroup.le_normalizer (RationalPoint.levi_le_parabolic χ hξ)
      mem_normalizer_opposite :=
        RationalPoint.levi_le_normalizer_unipotent (Dynamic.inverseCocharacter χ) hξ'
      tendsto_conj := fun x hx => (mem_unipotent_iff_tendsto_conj F ξ t ht x).1 hx
      mem_of_tendsto_conj := fun x hx => (mem_unipotent_iff_tendsto_conj F ξ t ht x).2 hx
      exists_levi_mul := fun p hp => by
        obtain ⟨⟨m, u⟩, ⟨hm, hu, hpmu⟩, -⟩ := RationalPoint.existsUnique_levi_mul_unipotent χ hp
        exact ⟨m, hm, u, hu, hpmu⟩
      tendsto_levi_conj := fun u hu => (mem_unipotent_iff_tendsto_conj F χ t ht u).1 hu
      commute_levi := fun m hm => by
        have h := BruhatTits.DynamicUnipotentContainment.commute_cocharPoint χ hm t
        rw [cocharPoint_eq_gmRationalPoint_comp] at h
        exact h.symm
      isClosed := BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints ξ
      mem_normalizer_target := mem_normalizer_unipotent_of_commute F ξ t ht hcomm.symm
      eq_one_of_mem_levi := hZU }

/-- **Product decomposition of a dynamic unipotent group.** Under the hypotheses of
`isOpenCellContraction_dynamic`, multiplication
`(U(χ) ∩ U(ξ))(F) × (U(χ⁻¹) ∩ U(ξ))(F) → U(ξ)(F)`, `(h, k) ↦ h k`, is a homeomorphism; the two
factors are read as subgroups of `U(ξ)(F)`. -/
def unipotentIntersectionProduct
    (χ ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (t : Fˣ) (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    (hξ : gmRationalPoint t ≫ ξ.hom.hom ∈ (Dynamic.centralizer χ).rationalPoints)
    (hZU : ∀ m ∈ (Dynamic.centralizer χ).rationalPoints,
      m ∈ (Dynamic.unipotent ξ).rationalPoints → m = 1) :
    ((Dynamic.unipotent χ).rationalPoints.subgroupOf (Dynamic.unipotent ξ).rationalPoints) ×
      ((Dynamic.unipotent (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).rationalPoints.subgroupOf
          (Dynamic.unipotent ξ).rationalPoints) ≃ₜ
      (Dynamic.unipotent ξ).rationalPoints :=
  letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  (isOpenCellContraction_dynamic F χ ξ t ht hξ hZU).productHomeomorph

theorem unipotentIntersectionProduct_apply
    (χ ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (t : Fˣ) (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    (hξ : gmRationalPoint t ≫ ξ.hom.hom ∈ (Dynamic.centralizer χ).rationalPoints)
    (hZU : ∀ m ∈ (Dynamic.centralizer χ).rationalPoints,
      m ∈ (Dynamic.unipotent ξ).rationalPoints → m = 1)
    (p : ((Dynamic.unipotent χ).rationalPoints.subgroupOf (Dynamic.unipotent ξ).rationalPoints) ×
      ((Dynamic.unipotent (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).rationalPoints.subgroupOf
          (Dynamic.unipotent ξ).rationalPoints)) :
    unipotentIntersectionProduct F χ ξ t ht hξ hZU p = (p.1 : _) * (p.2 : _) := rfl

end LocalField

end Langlands.GroupScheme.MatrixRepresentation
