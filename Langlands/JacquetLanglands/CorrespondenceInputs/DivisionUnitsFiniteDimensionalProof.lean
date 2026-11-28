import Langlands.JacquetLanglands.CorrespondenceInputs.DivisionUnitsFiniteDimensional
import Langlands.Representation.Schur.CountableDimensionProof
import Langlands.Representation.OrbitSpan
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Instances.Matrix

/-!
# Irreducible smooth representations of `Dˣ` are finite-dimensional

The theorem `irreducibleDivisionUnitsFiniteDimensional` proves
`IrreducibleDivisionUnitsFiniteDimensionalStatement`. Let `ϖ ∈ F` have a valuation generating
the value group. In the coordinates of a basis of `D`, the vectors whose coordinates have
valuation at most `1`, one of them exactly `1`, form a compact set `C ⊆ D \ {0}`, and every
nonzero `x ∈ D` has a multiple `ϖ ^ m • x` in `C`. Inversion is continuous on `D \ {0}`, so the
units in `C` form a compact subset of `Dˣ`. Hence, for every open subgroup `U` of `Dˣ`,
`Dˣ = Z S U` with `Z` the countable set of central elements `ϖ ^ m` (inverted) and `S` finite.
For an irreducible representation with a nonzero vector `w` fixed by `U`, the orbit of `w` is
then countable, Schur's lemma in countable dimension makes every element of `Z` act by a
scalar, and the finitely many vectors `s • w` (`s ∈ S`) span the representation.
-/

noncomputable section

namespace Langlands.JacquetLanglands

open _root_.Topology ValuativeRel WithZeroTopology Matrix

universe u uW

section Algebraic

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- An irreducible complex representation is finite-dimensional when a nonzero vector `w` is
fixed by a subgroup `U` and `G = Z S U` with `Z` a countable set of central elements and `S`
finite. -/
theorem finiteDimensional_of_central_finite_cover {ρ : Representation ℂ G W}
    (hirr : ρ.IsIrreducible) {w : W} (hw : w ≠ 0) (U : Subgroup G)
    (hU : ∀ u ∈ U, ρ u w = w) (Z : Set G) (hZc : Z.Countable) (hZ : Z ⊆ Subgroup.center G)
    (S : Finset G) (hcov : ∀ g : G, ∃ z ∈ Z, ∃ s ∈ S, ∃ u ∈ U, g = z * s * u) :
    FiniteDimensional ℂ W := by
  classical
  have horbit : ∀ g : G, ∃ z ∈ Z, ∃ s ∈ S, ρ g w = ρ z (ρ s w) := by
    intro g
    obtain ⟨z, hz, s, hs, u, hu, rfl⟩ := hcov g
    refine ⟨z, hz, s, hs, ?_⟩
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hU u hu]
  have hcount : (Set.range fun g : G => ρ g w).Countable := by
    have hsub : (Set.range fun g : G => ρ g w) ⊆
        (fun p : G × G => ρ p.1 (ρ p.2 w)) '' (Z ×ˢ (S : Set G)) := by
      rintro _ ⟨g, rfl⟩
      obtain ⟨z, hz, s, hs, h⟩ := horbit g
      exact ⟨(z, s), ⟨hz, hs⟩, h.symm⟩
    exact ((hZc.prod S.countable_toSet).image _).mono hsub
  have hspan := span_range_orbit_eq_top hirr hw
  have hrank : Module.rank ℂ W ≤ Cardinal.aleph0 := by
    calc
      Module.rank ℂ W = Module.rank ℂ (⊤ : Submodule ℂ W) := (rank_top ℂ W).symm
      _ = Module.rank ℂ (Submodule.span ℂ (Set.range fun g => ρ g w)) := by rw [hspan]
      _ ≤ Cardinal.mk (Set.range fun g => ρ g w) := rank_span_le _
      _ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr hcount.to_subtype
  have hscalar : ∀ z ∈ Z, ∃ c : ℂ, ∀ y : W, ρ z y = c • y := by
    intro z hz
    let T : ρ.IntertwiningMap ρ :=
      { toLinearMap := ρ z
        isIntertwining' := fun g => by
          change ρ z * ρ g = ρ g * ρ z
          rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hZ hz) g] }
    obtain ⟨c, hc, -⟩ := countableDimensionalSchur ρ hrank hirr T
    exact ⟨c, fun y => congrArg (fun f : ρ.IntertwiningMap ρ => f y) hc⟩
  have hle : Submodule.span ℂ (Set.range fun g : G => ρ g w) ≤
      Submodule.span ℂ ((fun s => ρ s w) '' (S : Set G)) := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    obtain ⟨z, hz, s, hs, h⟩ := horbit g
    obtain ⟨c, hc⟩ := hscalar z hz
    change ρ g w ∈ _
    rw [h, hc]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨s, hs, rfl⟩)
  rw [hspan] at hle
  have htop : Submodule.span ℂ ((fun s => ρ s w) '' (S : Set G)) = ⊤ := top_le_iff.mp hle
  exact Module.finite_def.mpr (htop ▸ Submodule.fg_span (S.finite_toSet.image _))

end Algebraic

section Field

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- A nonzero element `ϖ` of `F` whose valuation generates the value group: every nonzero
`a` has the valuation of an integer power of `ϖ`. -/
theorem exists_valuation_zpow_eq :
    ∃ ϖ : F, ϖ ≠ 0 ∧ ∀ a : F, a ≠ 0 → ∃ m : ℤ, valuation F (ϖ ^ m) = valuation F a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ValueGroupWithZero F)ˣ)
  obtain ⟨ϖ, hϖ⟩ := valuation_surjective (g : ValueGroupWithZero F)
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact g.ne_zero hϖ.symm
  refine ⟨ϖ, hϖ0, fun a ha => ?_⟩
  have hva : valuation F a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 _ hva))
  refine ⟨m, ?_⟩
  rw [map_zpow₀, hϖ]
  have := congrArg Units.val hm
  rwa [Units.val_zpow_eq_zpow_val, Units.val_mk0] at this

end Field

section Division

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
  [TopologicalSpace D] [IsModuleTopology F D]

include F in
/-- Inversion is continuous on the nonzero elements of `D` for the module topology: in the
coordinates of a basis, `x⁻¹` is the inverse of the matrix of left multiplication by `x`
applied to the coordinates of `1`, and matrix inversion is continuous where the determinant
does not vanish. -/
theorem continuousInv₀_division : ContinuousInv₀ D := by
  have := isTopologicalRing F D
  have := t2Space F D
  refine ⟨fun x hx => ?_⟩
  let b := Module.finBasis F D
  let M : D →ₐ[F] Matrix (Fin (Module.finrank F D)) (Fin (Module.finrank F D)) F :=
    Algebra.leftMulMatrix b
  have hM : Continuous M := IsModuleTopology.continuous_of_linearMap M.toLinearMap
  let e := coordinateHomeomorph F D b
  let c : Fin (Module.finrank F D) → F := e (1 : D)
  let φ : D → D := fun y => e.symm ((M y)⁻¹ *ᵥ c)
  have hMinv : ∀ y : D, y ≠ 0 → M y⁻¹ = (M y)⁻¹ := by
    intro y hy
    refine (Matrix.inv_eq_right_inv ?_).symm
    rw [← map_mul, mul_inv_cancel₀ hy, map_one]
  have hφ : ∀ y : D, y ≠ 0 → φ y = y⁻¹ := by
    intro y hy
    apply e.injective
    simp only [φ, Homeomorph.apply_symm_apply, c]
    rw [← hMinv y hy]
    change (M y⁻¹) *ᵥ (b.equivFun 1) = b.equivFun y⁻¹
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
      Algebra.leftMulMatrix_mulVec_repr, mul_one]
  have hdet : (M x).det ≠ 0 := by
    intro h0
    have h1 : M x * M x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx, map_one]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  have hcont : ContinuousAt φ x := by
    have hd : Continuous fun y => (M y).det := hM.matrix_det
    have hdinv : ContinuousAt (fun y : D => ((M y).det)⁻¹) x := hd.continuousAt.inv₀ hdet
    have hadj : ContinuousAt (fun y : D => (M y).adjugate) x := hM.matrix_adjugate.continuousAt
    have hinv : ContinuousAt (fun y => (M y)⁻¹) x := by
      have heq : (fun y => (M y)⁻¹) = fun y => ((M y).det)⁻¹ • (M y).adjugate := by
        funext y
        rw [Matrix.inv_def, Ring.inverse_eq_inv']
      rw [heq]
      exact hdinv.smul hadj
    have hmv : Continuous fun A : Matrix (Fin (Module.finrank F D)) (Fin (Module.finrank F D)) F =>
        A *ᵥ c := continuous_id.matrix_mulVec continuous_const
    exact e.symm.continuous.continuousAt.comp (hmv.continuousAt.comp hinv)
  refine hcont.congr ?_
  filter_upwards [isOpen_ne.mem_nhds hx] with y hy
  exact hφ y hy

/-- A compact set `C ⊆ D` not containing `0` and an element `ϖ ≠ 0` of `F` such that every
nonzero `x` has a multiple `ϖ ^ m • x` in `C`. In the coordinates of a basis, `C` is the set of
vectors whose coordinates have valuation at most `1`, one of them exactly `1`. -/
theorem exists_isCompact_zpow_smul_mem :
    ∃ (ϖ : F) (C : Set D), ϖ ≠ 0 ∧ IsCompact C ∧ (0 : D) ∉ C ∧
      ∀ x : D, x ≠ 0 → ∃ m : ℤ, (ϖ ^ m) • x ∈ C := by
  obtain ⟨ϖ, hϖ, hgen⟩ := exists_valuation_zpow_eq F
  let n := Module.finrank F D
  let b := Module.finBasis F D
  let e := coordinateHomeomorph F D b
  let T : Set (Fin n → F) :=
    (Set.univ.pi fun _ => {a : F | valuation F a ≤ 1}) ∩
      ⋃ i, (fun y : Fin n → F => y i) ⁻¹' {a : F | valuation F a = 1}
  have hT : IsCompact T := by
    refine (isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall F 1).inter_right
      (isClosed_iUnion_of_finite fun i => ?_)
    exact (isClosed_singleton.preimage IsValuativeTopology.continuous_valuation).preimage
      (continuous_apply i)
  have he : ∀ (a : F) (x : D), e (a • x) = a • e x := fun a x => b.equivFun.map_smul a x
  have he0 : e 0 = 0 := b.equivFun.map_zero
  refine ⟨ϖ, e ⁻¹' T, hϖ, e.isCompact_preimage.mpr hT, ?_, fun x hx => ?_⟩
  · rintro ⟨-, hmem⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, he0, Pi.zero_apply, map_zero] at hi
    exact zero_ne_one hi
  · set y := e x with hy
    have hy0 : y ≠ 0 := by
      intro h
      apply hx
      apply e.injective
      rw [← hy, h, he0]
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hy0
    have : Nonempty (Fin n) := ⟨i₀⟩
    obtain ⟨j, hj⟩ := Finite.exists_max fun i => valuation F (y i)
    have hyj : y j ≠ 0 := by
      intro h
      apply hi₀
      have := hj i₀
      rw [h, map_zero] at this
      exact (Valuation.zero_iff _).mp (le_antisymm this zero_le)
    obtain ⟨m, hm⟩ := hgen (y j) hyj
    refine ⟨-m, ?_⟩
    have hunit : valuation F (ϖ ^ (-m)) * valuation F (y j) = 1 := by
      rw [← hm, ← map_mul, zpow_neg, inv_mul_cancel₀ (zpow_ne_zero m hϖ), map_one]
    change e ((ϖ ^ (-m)) • x) ∈ T
    rw [he, ← hy]
    refine ⟨fun i _ => ?_, Set.mem_iUnion.mpr ⟨j, ?_⟩⟩
    · simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, map_mul]
      rw [← hunit]
      exact mul_le_mul_right (hj i) _
    · simp only [Set.mem_preimage, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, map_mul]
      exact hunit

include F in
/-- For an open subgroup `U` of `Dˣ`, a countable set `Z` of central elements and a finite set
`S` with `Dˣ = Z S U`. The elements of `Z` are the inverses of the images of the powers
`ϖ ^ m` of `exists_isCompact_zpow_smul_mem`, and `S` comes from a finite cover of the compact
set of units in `C` by left translates of `U`. -/
theorem exists_central_finite_cover (U : OpenSubgroup Dˣ) :
    ∃ Z : Set Dˣ, Z.Countable ∧ Z ⊆ Subgroup.center Dˣ ∧ ∃ S : Finset Dˣ,
      ∀ g : Dˣ, ∃ z ∈ Z, ∃ s ∈ S, ∃ u ∈ (U : Subgroup Dˣ), g = z * s * u := by
  classical
  have := units_isTopologicalGroup F D
  have := continuousInv₀_division F D
  obtain ⟨ϖ, C, hϖ, hC, hC0, hnorm⟩ := exists_isCompact_zpow_smul_mem F D
  have hζ0 : ∀ m : ℤ, algebraMap F D (ϖ ^ m) ≠ 0 := fun m =>
    (map_ne_zero (algebraMap F D)).mpr (zpow_ne_zero m hϖ)
  let ζ : ℤ → Dˣ := fun m => Units.mk0 (algebraMap F D (ϖ ^ m)) (hζ0 m)
  have hζc : ∀ m, ζ m ∈ Subgroup.center Dˣ := fun m =>
    Subgroup.mem_center_iff.mpr fun g => Units.ext (Algebra.commutes (ϖ ^ m) (g : D)).symm
  have hCU : IsCompact ((Units.val : Dˣ → D) ⁻¹' C) := by
    refine Units.isEmbedding_val₀.isInducing.isCompact_preimage' hC fun x hx => ?_
    have hx0 : x ≠ 0 := fun h => hC0 (h ▸ hx)
    exact ⟨Units.mk0 x hx0, rfl⟩
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hCU
    (V := (U : Set Dˣ)) ⟨1, by rw [U.isOpen.interior_eq]; exact U.one_mem⟩
  refine ⟨Set.range fun m => (ζ m)⁻¹, Set.countable_range _, ?_, t.image (·⁻¹), fun g => ?_⟩
  · rintro _ ⟨m, rfl⟩
    exact Subgroup.inv_mem _ (hζc m)
  · obtain ⟨m, hm⟩ := hnorm (g : D) g.ne_zero
    have hmem : ζ m * g ∈ (Units.val : Dˣ → D) ⁻¹' C := by
      change algebraMap F D (ϖ ^ m) * (g : D) ∈ C
      rwa [← Algebra.smul_def]
    obtain ⟨s, hs, hsU⟩ := Set.mem_iUnion₂.mp (ht hmem)
    refine ⟨(ζ m)⁻¹, ⟨m, rfl⟩, s⁻¹, Finset.mem_image_of_mem _ hs, s * (ζ m * g), hsU, ?_⟩
    group

end Division

/-- Every irreducible smooth complex representation of the units of a finite-dimensional
central division algebra over a nonarchimedean local field is finite-dimensional. -/
theorem irreducibleDivisionUnitsFiniteDimensional :
    IrreducibleDivisionUnitsFiniteDimensionalStatement.{u, uW} := by
  intro F _ _ _ _ D _ _ _ _ _ _ W _ _ ρ hs hirr
  let := hirr
  let : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ Dˣ) ρ.asModule
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨K, hK⟩ := hs w
  obtain ⟨Z, hZc, hZ, S, hcov⟩ := exists_central_finite_cover F D K
  exact finiteDimensional_of_central_finite_cover hirr hw K.toSubgroup
    (fun u hu => (Representation.mem_invariants _ w).mp hK ⟨u, hu⟩) Z hZc hZ S hcov

end Langlands.JacquetLanglands
