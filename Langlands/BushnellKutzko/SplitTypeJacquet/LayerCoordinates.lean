import Langlands.BushnellKutzko.SplitTypeJacquet.LayerBasis
import Langlands.BushnellKutzko.SplitTypeJacquet.IntegralOrder
import Langlands.BushnellKutzko.LevelZeroSplitType

/-! # The unit groups of a lattice chain in coordinates adapted to its layers

Reindex the adapted basis of `LayerBasis` along an equivalence `ν : ι ≃ Σ i, Fin (d i)`. If a
block function `blk` on `ι` reverses the order of the layers, the order `𝔄(L)` and its radical
become `InOrd blk` and `InRad blk`, the unit groups `U(𝔄)` and `U^1(𝔄)` become `J0 F blk` and
`J1 F blk`, and the reduction of `U(𝔄)` on each layer is read off from the residues of the
corresponding diagonal block. -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.SplitTypeJacquet

universe uF uV uI

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (L : LatticeChain 𝒪[F] F V) {d : Fin L.period → ℕ}
  (b : ∀ i : Fin L.period, Module.Basis (Fin (d i)) 𝓀[F] (L.Layer ((i : ℕ) : ℤ)))
  {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
  {ι : Type uI} [Fintype ι] [DecidableEq ι] (ν : ι ≃ Σ i : Fin L.period, Fin (d i))

omit [Fintype ι] [DecidableEq ι] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] in
theorem toLinAlgEquiv_eq_toLin' (β : Module.Basis ι F V) [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι F) : Matrix.toLinAlgEquiv β M = Matrix.toLin β β M :=
  β.ext fun i => by rw [Matrix.toLinAlgEquiv_self, Matrix.toLin_self]

/-- The adapted basis reindexed along `ν`. -/
def coordBasis : Module.Basis ι F V := (adaptedBasis L b hϖ).reindex ν.symm

omit [Fintype ι] [DecidableEq ι] in
theorem coordBasis_apply (c : ι) : coordBasis L b hϖ ν c = liftVec L b (ν c) := by
  rw [coordBasis, Module.Basis.reindex_apply, Equiv.symm_symm, adaptedBasis_apply]

/-- The criterion of `toLin_mem_endFiltration_iff` in the reindexed coordinates. -/
theorem toLin_coordBasis_mem_endFiltration_iff {s : ℕ} (hs : s ≤ 1) (M : Matrix ι ι F) :
    Matrix.toLin (coordBasis L b hϖ ν) (coordBasis L b hϖ ν) M ∈ L.endFiltration (s : ℤ) ↔
      ∀ c c', valuation F (M c c') ≤ 1 ∧
        (((ν c).1 : ℕ) < ((ν c').1 : ℕ) + s → valuation F (M c c') < 1) := by
  have hM : Matrix.toLin (coordBasis L b hϖ ν) (coordBasis L b hϖ ν) M =
      Matrix.toLin (adaptedBasis L b hϖ) (adaptedBasis L b hϖ) (M.submatrix ν.symm ν.symm) := by
    apply (coordBasis L b hϖ ν).ext
    intro c
    rw [Matrix.toLin_self, coordBasis_apply, ← adaptedBasis_apply L b hϖ, Matrix.toLin_self]
    rw [← Equiv.sum_comp ν]
    refine Finset.sum_congr rfl fun c' _ => ?_
    simp [coordBasis_apply, adaptedBasis_apply]
  rw [hM, toLin_mem_endFiltration_iff L b hϖ hs]
  constructor
  · intro h c c'
    have := h (ν c) (ν c')
    simpa using this
  · intro h p q
    have := h (ν.symm p) (ν.symm q)
    simpa using this

variable {blk : ι → ℕ}

theorem toLin_coordBasis_mem_order_iff
    (hblk : ∀ c c', ((ν c).1 : ℕ) < ((ν c').1 : ℕ) ↔ blk c' < blk c) (M : Matrix ι ι F) :
    Matrix.toLin (coordBasis L b hϖ ν) (coordBasis L b hϖ ν) M ∈ L.order ↔ InOrd blk M := by
  rw [LatticeChain.mem_order_iff_mem_endFiltration,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl,
    toLin_coordBasis_mem_endFiltration_iff L b hϖ ν (Nat.zero_le 1)]
  constructor
  · intro h c c'
    exact ⟨(h c c').1, fun hcc => (h c c').2 (by rw [add_zero]; exact (hblk c c').mpr hcc)⟩
  · intro h c c'
    exact ⟨(h c c').1, fun hcc => (h c c').2 ((hblk c c').mp (by simpa using hcc))⟩

theorem toLin_coordBasis_mem_endFiltration_one_iff
    (hblk : ∀ c c', ((ν c).1 : ℕ) < ((ν c').1 : ℕ) ↔ blk c' < blk c) (M : Matrix ι ι F) :
    Matrix.toLin (coordBasis L b hϖ ν) (coordBasis L b hϖ ν) M ∈ L.endFiltration 1 ↔
      InRad blk M := by
  rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl,
    toLin_coordBasis_mem_endFiltration_iff L b hϖ ν le_rfl]
  have hle : ∀ c c', ((ν c).1 : ℕ) < ((ν c').1 : ℕ) + 1 ↔ blk c' ≤ blk c := by
    intro c c'
    rw [Nat.lt_succ_iff, ← not_lt, ← not_lt, hblk c' c]
  constructor
  · intro h c c'
    exact ⟨(h c c').1, fun hcc => (h c c').2 ((hle c c').mpr hcc)⟩
  · intro h c c'
    exact ⟨(h c c').1, fun hcc => (h c c').2 ((hle c c').mp hcc)⟩

/-- Invertible matrices act on `V` through the reindexed adapted basis. -/
def stdToAut : GL ι F ≃* (Module.End F V)ˣ :=
  Units.mapEquiv (Matrix.toLinAlgEquiv (coordBasis L b hϖ ν)).toMulEquiv

theorem coe_stdToAut (x : GL ι F) :
    ((stdToAut L b hϖ ν x : (Module.End F V)ˣ) : Module.End F V) =
      Matrix.toLin (coordBasis L b hϖ ν) (coordBasis L b hϖ ν) (x : Matrix ι ι F) :=
  toLinAlgEquiv_eq_toLin' _ _

theorem stdToAut_mem_unitFiltration_zero_iff
    (hblk : ∀ c c', ((ν c).1 : ℕ) < ((ν c').1 : ℕ) ↔ blk c' < blk c) (x : GL ι F) :
    stdToAut L b hϖ ν x ∈ L.unitFiltration 0 ↔ x ∈ J0 F blk := by
  have hinv : ((stdToAut L b hϖ ν x)⁻¹ : (Module.End F V)ˣ) = stdToAut L b hϖ ν x⁻¹ :=
    (map_inv _ _).symm
  rw [LatticeChain.mem_unitFiltration_zero, hinv, coe_stdToAut, coe_stdToAut,
    toLin_coordBasis_mem_order_iff L b hϖ ν hblk, toLin_coordBasis_mem_order_iff L b hϖ ν hblk]
  rfl

theorem stdToAut_mem_unitFiltration_one_iff
    (hblk : ∀ c c', ((ν c).1 : ℕ) < ((ν c').1 : ℕ) ↔ blk c' < blk c) (x : GL ι F) :
    stdToAut L b hϖ ν x ∈ L.unitFiltration 1 ↔ x ∈ J1 F blk := by
  have hinv : ((stdToAut L b hϖ ν x)⁻¹ : (Module.End F V)ˣ) = stdToAut L b hϖ ν x⁻¹ :=
    (map_inv _ _).symm
  have hsub : ((stdToAut L b hϖ ν x : (Module.End F V)ˣ) : Module.End F V) - 1 =
      Matrix.toLin (coordBasis L b hϖ ν) (coordBasis L b hϖ ν) ((x : Matrix ι ι F) - 1) := by
    rw [coe_stdToAut, map_sub, Matrix.toLin_one]
    rfl
  rw [LatticeChain.mem_unitFiltration, hinv, hsub, coe_stdToAut, coe_stdToAut,
    show ((1 : ℕ) : ℤ) = 1 from rfl, toLin_coordBasis_mem_order_iff L b hϖ ν hblk,
    toLin_coordBasis_mem_order_iff L b hϖ ν hblk,
    toLin_coordBasis_mem_endFiltration_one_iff L b hϖ ν hblk]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩

/-- A sum of integral multiples of vectors of `L_i` reduces termwise on the layer
`L_i / L_{i+1}`. -/
theorem intervalMk_sum_smul {I : Type*} [Fintype I] {i : ℤ} (r : I → 𝒪[F]) (v : I → V)
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

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem sum_layer_split {M : Type*} [AddCommMonoid M] (g : (Σ i : Fin L.period, Fin (d i)) → M)
    (i : Fin L.period) :
    ∑ p, g p = ∑ r, g ⟨i, r⟩ +
      ∑ p ∈ Finset.univ.filter (fun p : Σ i : Fin L.period, Fin (d i) => p.1 ≠ i), g p := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun p : Σ i : Fin L.period, Fin (d i) => p.1 = i)]
  congr 1
  rw [Finset.sum_filter, Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

/-- **Layer reduction in coordinates.** The reduction on the `i`-th layer of an element of
`U(𝔄)`, written in the layer basis `b i`, is the residue of the corresponding diagonal block
of its matrix in the reindexed adapted basis. -/
theorem layerReduction_stdToAut_apply
    (hblk : ∀ c c', ((ν c).1 : ℕ) < ((ν c').1 : ℕ) ↔ blk c' < blk c)
    (x : GL ι F) (hx : x ∈ J0 F blk) (i : Fin L.period) (r s : Fin (d i)) :
    ((L.layerReduction b ⟨stdToAut L b hϖ ν x,
        (stdToAut_mem_unitFiltration_zero_iff L b hϖ ν hblk x).mpr hx⟩ i :
      GeneralLinear (d i) 𝓀[F]) : Matrix (Fin (d i)) (Fin (d i)) 𝓀[F]) r s =
      IsLocalRing.residue 𝒪[F]
        ⟨(x : Matrix ι ι F) (ν.symm ⟨i, r⟩) (ν.symm ⟨i, s⟩),
          (Valuation.mem_integer_iff _ _).mpr (hx.1 _ _).1⟩ := by
  classical
  set β := coordBasis L b hϖ ν with hβ
  set X := (x : Matrix ι ι F) with hX
  set c := ν.symm ⟨i, s⟩ with hc
  have hv : liftVec L b ⟨i, s⟩ ∈ L.lattice ((i : ℕ) : ℤ) := liftVec_mem L b ⟨i, s⟩
  have hU := (stdToAut_mem_unitFiltration_zero_iff L b hϖ ν hblk x).mpr hx
  have key := L.layerReduction_spec b ⟨stdToAut L b hϖ ν x, hU⟩ i (liftVec L b ⟨i, s⟩) hv
  rw [intervalMk_liftVec L b ⟨i, s⟩, Matrix.GeneralLinearGroup.toLin'_apply,
    Module.Basis.repr_self] at key
  -- the image of the basis vector
  have hβc : β c = liftVec L b ⟨i, s⟩ := by
    rw [coordBasis_apply, hc, Equiv.apply_symm_apply]
  have hcol : ((stdToAut L b hϖ ν x : (Module.End F V)ˣ) : Module.End F V)
      (liftVec L b ⟨i, s⟩) = ∑ p, X (ν.symm p) c • liftVec L b p := by
    rw [← hβc, coe_stdToAut, Matrix.toLin_self, ← Equiv.sum_comp ν.symm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [coordBasis_apply, Equiv.apply_symm_apply]
  let ρr : Fin (d i) → 𝒪[F] := fun r' => ⟨X (ν.symm ⟨i, r'⟩) c,
    (Valuation.mem_integer_iff _ _).mpr (hx.1 _ _).1⟩
  have hlv : ∀ r', liftVec L b ⟨i, r'⟩ ∈ L.lattice ((i : ℕ) : ℤ) := fun r' =>
    liftVec_mem L b ⟨i, r'⟩
  have hL : L.intervalMk ((i : ℕ) : ℤ) (((i : ℕ) : ℤ) + 1)
      (((stdToAut L b hϖ ν x : (Module.End F V)ˣ) : Module.End F V) (liftVec L b ⟨i, s⟩))
      (L.mem_order.mp hU.1 _ _ hv) = ∑ r', IsLocalRing.residue 𝒪[F] (ρr r') • b i r' := by
    have hS : ∑ r', ((ρr r' : 𝒪[F]) : F) • liftVec L b ⟨i, r'⟩ ∈ L.lattice ((i : ℕ) : ℤ) :=
      Submodule.sum_mem _ fun r' _ => integral_smul_mem L (ρr r').2 (hlv r')
    have h1 : L.intervalMk ((i : ℕ) : ℤ) (((i : ℕ) : ℤ) + 1)
        (((stdToAut L b hϖ ν x : (Module.End F V)ˣ) : Module.End F V) (liftVec L b ⟨i, s⟩))
        (L.mem_order.mp hU.1 _ _ hv) = L.intervalMk ((i : ℕ) : ℤ) (((i : ℕ) : ℤ) + 1) _ hS := by
      rw [LatticeChain.intervalMk_eq_iff, hcol, sum_layer_split L _ i]
      have hrest : ∑ p ∈ Finset.univ.filter
          (fun p : Σ i : Fin L.period, Fin (d i) => p.1 ≠ i),
          X (ν.symm p) c • liftVec L b p ∈ L.lattice (((i : ℕ) : ℤ) + 1) := by
        refine Submodule.sum_mem _ fun p hp => ?_
        rw [Finset.mem_filter] at hp
        rcases lt_or_gt_of_ne (fun h : (p.1 : ℕ) = i => hp.2 (Fin.ext h)) with hlt | hgt
        · have hb' : blk c < blk (ν.symm p) := by
            rw [← hblk]
            simp only [Equiv.apply_symm_apply, hc]
            exact hlt
          have h := maximal_smul_mem L hϖ ((hx.1 _ _).2 hb') (liftVec_mem L b p)
          exact L.antitone (by have := i.isLt; omega) h
        · exact L.antitone (by omega)
            (integral_smul_mem L (hx.1 _ _).1 (liftVec_mem L b p))
      convert hrest using 1
      simp only [ρr]
      abel
    rw [h1, intervalMk_sum_smul L ρr (fun r' => liftVec L b ⟨i, r'⟩) hlv]
    refine Finset.sum_congr rfl fun r' _ => ?_
    rw [intervalMk_liftVec L b ⟨i, r'⟩]
  rw [hL, Fintype.linearCombination_apply] at key
  have hE := congrArg (b i).repr key
  have := congrArg (fun f => f r) hE
  simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, Finsupp.single_apply] at this
  simpa [Matrix.mulVec, dotProduct, Finsupp.single_apply, eq_comm] using this

end Langlands.BushnellKutzko.SplitTypeJacquet
