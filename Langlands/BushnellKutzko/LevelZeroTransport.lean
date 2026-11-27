import Langlands.BushnellKutzko.LevelZeroAdaptedBasis
import Langlands.BushnellKutzko.LevelZeroStandard
import Langlands.BushnellKutzko.SimpleTypes

/-! # The unit groups of a principal order in an adapted basis -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uF uV uI

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem toLinAlgEquiv_eq_toLin {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (β : Module.Basis ι F V) (M : Matrix ι ι F) :
    Matrix.toLinAlgEquiv β M = Matrix.toLin β β M :=
  β.ext fun i => by rw [Matrix.toLinAlgEquiv_self, Matrix.toLin_self]

variable (L : LatticeChain 𝒪[F] F V) {e f : ℕ}
  (b : ∀ i : Fin e, Module.Basis (Fin f) 𝓀[F] (L.Layer ((i : ℕ) : ℤ)))
  {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (he : L.period = e)

/-- Invertible matrices act on `V` through the adapted basis. -/
def stdToAut : GL (Fin f × Fin e) F ≃* (Module.End F V)ˣ :=
  Units.mapEquiv (Matrix.toLinAlgEquiv (adaptedBasis L b hϖ he)).toMulEquiv

theorem coe_stdToAut (x : GL (Fin f × Fin e) F) :
    ((stdToAut L b hϖ he x : (Module.End F V)ˣ) : Module.End F V) =
      Matrix.toLin (adaptedBasis L b hϖ he) (adaptedBasis L b hϖ he)
        (x : Matrix (Fin f × Fin e) (Fin f × Fin e) F) :=
  toLinAlgEquiv_eq_toLin _ _

theorem toLin_mem_order_iff (M : Matrix (Fin f × Fin e) (Fin f × Fin e) F) :
    Matrix.toLin (adaptedBasis L b hϖ he) (adaptedBasis L b hϖ he) M ∈ L.order ↔ InOrd M := by
  rw [LatticeChain.mem_order_iff_mem_endFiltration,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, toLin_mem_endFiltration_iff L b hϖ he (Nat.zero_le 1)]
  constructor
  · intro h p q
    exact ⟨(h p q).1, fun hpq => (h p q).2 (by have := Fin.lt_def.mp hpq; omega)⟩
  · intro h p q
    exact ⟨(h p q).1, fun hpq => (h p q).2 (Fin.lt_def.mpr (by omega))⟩

theorem toLin_mem_endFiltration_one_iff (M : Matrix (Fin f × Fin e) (Fin f × Fin e) F) :
    Matrix.toLin (adaptedBasis L b hϖ he) (adaptedBasis L b hϖ he) M ∈ L.endFiltration 1 ↔
      InRad M := by
  rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, toLin_mem_endFiltration_iff L b hϖ he le_rfl]
  constructor
  · intro h p q
    exact ⟨(h p q).1, fun hpq => (h p q).2 (by have := Fin.le_def.mp hpq; omega)⟩
  · intro h p q
    exact ⟨(h p q).1, fun hpq => (h p q).2 (Fin.le_def.mpr (by omega))⟩

theorem stdToAut_mem_unitFiltration_zero_iff (x : GL (Fin f × Fin e) F) :
    stdToAut L b hϖ he x ∈ L.unitFiltration 0 ↔ x ∈ J0 F e f := by
  have hinv : ((stdToAut L b hϖ he x)⁻¹ : (Module.End F V)ˣ) = stdToAut L b hϖ he x⁻¹ :=
    (map_inv _ _).symm
  constructor
  · rintro ⟨h1, h2, -⟩
    rw [coe_stdToAut, toLin_mem_order_iff] at h1
    rw [hinv, coe_stdToAut, toLin_mem_order_iff] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have h1' : ((stdToAut L b hϖ he x : (Module.End F V)ˣ) : Module.End F V) ∈ L.order := by
      rw [coe_stdToAut, toLin_mem_order_iff]; exact h1
    refine ⟨h1', by rw [hinv, coe_stdToAut, toLin_mem_order_iff]; exact h2, ?_⟩
    have hone : (1 : Module.End F V) ∈ L.endFiltration ((0 : ℕ) : ℤ) :=
      (L.mem_order_iff_mem_endFiltration).mp (one_mem _)
    exact sub_mem ((L.mem_order_iff_mem_endFiltration).mp h1') hone

theorem stdToAut_mem_unitFiltration_one_iff (x : GL (Fin f × Fin e) F) :
    stdToAut L b hϖ he x ∈ L.unitFiltration 1 ↔ x ∈ J1 F e f := by
  have hinv : ((stdToAut L b hϖ he x)⁻¹ : (Module.End F V)ˣ) = stdToAut L b hϖ he x⁻¹ :=
    (map_inv _ _).symm
  have hsub : ((stdToAut L b hϖ he x : (Module.End F V)ˣ) : Module.End F V) - 1 =
      Matrix.toLin (adaptedBasis L b hϖ he) (adaptedBasis L b hϖ he)
        ((x : Matrix (Fin f × Fin e) (Fin f × Fin e) F) - 1) := by
    rw [coe_stdToAut, map_sub, Matrix.toLin_one]
    rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [coe_stdToAut, toLin_mem_order_iff] at h1
    rw [hinv, coe_stdToAut, toLin_mem_order_iff] at h2
    rw [hsub, show ((1 : ℕ) : ℤ) = 1 from rfl, toLin_mem_endFiltration_one_iff] at h3
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨by rw [coe_stdToAut, toLin_mem_order_iff]; exact h1,
      by rw [hinv, coe_stdToAut, toLin_mem_order_iff]; exact h2, ?_⟩
    rw [hsub, show ((1 : ℕ) : ℤ) = 1 from rfl, toLin_mem_endFiltration_one_iff]
    exact h3

/-- A sum of integral multiples of vectors of `L_i` reduces termwise on the layer
`L_i / L_{i+1}`. -/
theorem intervalMk_sum_smul {I : Type uI} [Fintype I] {i : ℤ} (r : I → 𝒪[F]) (v : I → V)
    (hv : ∀ a, v a ∈ L.lattice i) :
    L.intervalMk i (i + 1) (∑ a, (r a : F) • v a)
        (Submodule.sum_mem _ fun a _ => integral_smul_mem L (r a).2 (hv a)) =
      ∑ a, IsLocalRing.residue 𝒪[F] (r a) • L.intervalMk i (i + 1) (v a) (hv a) := by
  let q := (L.intervalSubmodule i (i + 1)).mkQ
  have h (a : I) (y : L.Layer i) : IsLocalRing.residue 𝒪[F] (r a) • y = r a • y :=
    algebraMap_smul 𝓀[F] (r a) y
  simp only [h]
  change q ⟨_, _⟩ = ∑ a, r a • q ⟨v a, hv a⟩
  rw [show (⟨∑ a, (r a : F) • v a, _⟩ : L.lattice i) = ∑ a, r a • (⟨v a, hv a⟩ : L.lattice i)
    from ?_]
  · simp only [map_sum, map_smul]
  · apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
    exact Finset.sum_congr rfl fun a _ => (integer_smul_eq _ _).symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem sum_block_split {M : Type uI} [AddCommMonoid M] (g : Fin f × Fin e → M) (i : Fin e) :
    ∑ p, g p = ∑ c, g (c, i) + ∑ p ∈ Finset.univ.filter (fun p : Fin f × Fin e => p.2 ≠ i), g p := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Fin f × Fin e => p.2 = i)]
  congr 1
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq']

/-- The reduction on the `i`-th layer of an element of `U(𝔄)`, written in the layer bases
`b i`, is the residue of the `i`-th diagonal block of its matrix in the adapted basis. -/
theorem layerReduction_entry {U : Subgroup (Module.End F V)ˣ}
    (hU : ∀ u ∈ U, ∀ (i : ℤ) (v : V), v ∈ L.lattice i →
      (u : Module.End F V) v ∈ L.lattice i)
    {φ : U →* (Fin e → GeneralLinear f 𝓀[F])} (hφ : IsLayerReduction L U hU b φ)
    (x : GL (Fin f × Fin e) F) (hx : x ∈ J0 F e f) (hxU : stdToAut L b hϖ he x ∈ U)
    (i : Fin e) (a a' : Fin f) :
    ((φ ⟨_, hxU⟩ i : GeneralLinear f 𝓀[F]) : Matrix (Fin f) (Fin f) 𝓀[F]) a a' =
      IsLocalRing.residue 𝒪[F]
        ⟨(x : Matrix (Fin f × Fin e) (Fin f × Fin e) F) (a, i) (a', i), (hx.1 _ _).1⟩ := by
  classical
  set β := adaptedBasis L b hϖ he with hβ
  set X := (x : Matrix (Fin f × Fin e) (Fin f × Fin e) F) with hX
  have hv : β (a', i) ∈ L.lattice ((i : ℕ) : ℤ) := by
    rw [adaptedBasis_apply]; exact liftVec_mem L b (a', i)
  have key := hφ ⟨_, hxU⟩ i (β (a', i)) hv
  -- the right-hand side
  have hR : L.intervalMk _ _ (β (a', i)) hv = b i a' := by
    have hgen : ∀ (w : V) (hw : w ∈ L.lattice ((i : ℕ) : ℤ)), w = liftVec L b (a', i) →
        L.intervalMk _ _ w hw = b i a' := by
      rintro w hw rfl
      exact intervalMk_liftVec L b (a', i)
    exact hgen _ _ (adaptedBasis_apply L b hϖ he _)
  have hsingle : (b i).equivFun (b i a') = Pi.single a' 1 := by
    ext c
    rw [Module.Basis.equivFun_self]
    by_cases h : a' = c
    · subst h; simp
    · rw [ite_eq_right h, Pi.single_apply, ite_eq_right (Ne.symm h)]
  rw [hR, hsingle, Matrix.mulVec_single_one] at key
  -- the left-hand side
  let r : Fin f → 𝒪[F] := fun c => ⟨X (c, i) (a', i), (hx.1 _ _).1⟩
  have hlv : ∀ c, liftVec L b (c, i) ∈ L.lattice ((i : ℕ) : ℤ) := fun c => liftVec_mem L b (c, i)
  have hcol : (((⟨_, hxU⟩ : U) : (Module.End F V)ˣ) : Module.End F V) (β (a', i)) =
      ∑ p, X p (a', i) • liftVec L b p := by
    change ((stdToAut L b hϖ he x : (Module.End F V)ˣ) : Module.End F V) (β (a', i)) = _
    rw [coe_stdToAut, Matrix.toLin_self]
    simp only [adaptedBasis_apply, X]
  have hL : L.intervalMk ((i : ℕ) : ℤ) (((i : ℕ) : ℤ) + 1)
      ((((⟨_, hxU⟩ : U) : (Module.End F V)ˣ) : Module.End F V) (β (a', i)))
      (hU _ (⟨_, hxU⟩ : U).2 _ _ hv) = ∑ c, IsLocalRing.residue 𝒪[F] (r c) • b i c := by
    have hS : ∑ c, ((r c : 𝒪[F]) : F) • liftVec L b (c, i) ∈ L.lattice ((i : ℕ) : ℤ) :=
      Submodule.sum_mem _ fun c _ => integral_smul_mem L (r c).2 (hlv c)
    have h1 : L.intervalMk ((i : ℕ) : ℤ) (((i : ℕ) : ℤ) + 1)
        ((((⟨_, hxU⟩ : U) : (Module.End F V)ˣ) : Module.End F V) (β (a', i)))
        (hU _ (⟨_, hxU⟩ : U).2 _ _ hv) = L.intervalMk ((i : ℕ) : ℤ) (((i : ℕ) : ℤ) + 1) _ hS := by
      rw [LatticeChain.intervalMk_eq_iff, hcol, sum_block_split _ i]
      have hrest : ∑ p ∈ Finset.univ.filter (fun p : Fin f × Fin e => p.2 ≠ i),
          X p (a', i) • liftVec L b p ∈ L.lattice (((i : ℕ) : ℤ) + 1) := by
        refine Submodule.sum_mem _ fun p hp => ?_
        rw [Finset.mem_filter] at hp
        rcases lt_or_gt_of_ne (fun h : (p.2 : ℕ) = i => hp.2 (Fin.ext h)) with hlt | hgt
        · have h := maximal_smul_mem L hϖ he ((hx.1 p (a', i)).2 (Fin.lt_def.mpr hlt))
            (liftVec_mem L b p)
          exact L.antitone (by have := i.isLt; omega) h
        · exact L.antitone (by omega)
            (integral_smul_mem L (hx.1 p (a', i)).1 (liftVec_mem L b p))
      convert hrest using 1
      simp only [r]
      abel
    rw [h1, intervalMk_sum_smul L r (fun c => liftVec L b (c, i)) hlv]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [intervalMk_liftVec L b (c, i)]
  rw [hL] at key
  have hE : (b i).equivFun (∑ c, IsLocalRing.residue 𝒪[F] (r c) • b i c) =
      fun c => IsLocalRing.residue 𝒪[F] (r c) := by
    rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  rw [hE] at key
  have := congrFun key a
  simp only [Matrix.col_apply] at this
  exact this.symm

end Langlands.BushnellKutzko.LevelZero
