import Langlands.BushnellKutzko.MinimalSimpleStratumResidue

/-! # Layer sizes of principal lattice chains

For a lattice chain `(L_i)` over a nonarchimedean local field `F` with period `e`, the quotient
`L_0 / L_e = L_0 / 𝔭_F L_0` has `q^N` elements, where `q` is the order of the residue field and
`N = dim_F V`. For a principal chain all the successive quotients `L_i / L_{i+1}` have the same
order, so each has `q^{N/e}` elements. If a field `E` normalizes the chain, the quotient
`L_0 / L_1` is a vector space over the residue field of `E`, and the residue degree of `E` divides
`N / e`.
-/

open ValuativeRel IsLocalRing

noncomputable section

namespace Langlands.BushnellKutzko.LatticeChain

universe uO uK uV uF

section General
variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  (𝓛 : LatticeChain O K V)

theorem natCard_interval_eq_relIndex (i j : ℤ) :
    Nat.card (𝓛.Interval i j) =
      (𝓛.lattice j).toAddSubgroup.relIndex (𝓛.lattice i).toAddSubgroup := rfl

theorem relIndex_mul_relIndex_lattice {i j k : ℤ} (hij : i ≤ j) (hjk : j ≤ k) :
    (𝓛.lattice k).toAddSubgroup.relIndex (𝓛.lattice j).toAddSubgroup *
      (𝓛.lattice j).toAddSubgroup.relIndex (𝓛.lattice i).toAddSubgroup =
    (𝓛.lattice k).toAddSubgroup.relIndex (𝓛.lattice i).toAddSubgroup :=
  AddSubgroup.relIndex_mul_relIndex _ _ _ (𝓛.antitone hjk) (𝓛.antitone hij)

theorem relIndex_lattice_natCast_of_isPrincipal (hP : 𝓛.IsPrincipal) (k : ℕ) :
    (𝓛.lattice (k : ℤ)).toAddSubgroup.relIndex (𝓛.lattice 0).toAddSubgroup =
      ((𝓛.lattice 1).toAddSubgroup.relIndex (𝓛.lattice 0).toAddSubgroup) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← 𝓛.relIndex_mul_relIndex_lattice (j := (k : ℤ)) (by omega) (by omega), ih, pow_succ,
      mul_comm]
    congr 1
    have := hP k 0
    simpa using this

end General

section Local

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

/-- The quotient of `L_0` by `L_e = 𝔭_F L_0` has `q^N` elements. -/
theorem natCard_interval_period [FiniteDimensional F V] :
    Nat.card (𝓛.Interval 0 𝓛.period) =
      Nat.card (ResidueField 𝒪[F]) ^ Module.finrank F V := by
  let L := 𝓛.lattice 0
  have : L.IsLattice F := 𝓛.isLattice 0
  let b₀ := Module.Free.chooseBasis 𝒪[F] L
  let b := b₀.extendOfIsLattice F
  have hrank : Module.finrank 𝒪[F] L = Module.finrank F V := by
    rw [Module.finrank_eq_card_basis b₀, Module.finrank_eq_card_basis b]
  have hsub : 𝓛.intervalSubmodule 0 𝓛.period =
      (maximalIdeal 𝒪[F]) • (⊤ : Submodule 𝒪[F] L) := by
    have h0 := 𝓛.lattice_add_period 0
    rw [zero_add, ringJacobson_eq_maximalIdeal] at h0
    have hmap : (maximalIdeal 𝒪[F]) • L = ((maximalIdeal 𝒪[F]) • (⊤ : Submodule 𝒪[F] L)).map
        L.subtype := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
    change (𝓛.lattice 𝓛.period).comap L.subtype = _
    rw [h0, hmap, Submodule.comap_map_eq_of_injective L.injective_subtype]
  let e := TensorProduct.quotTensorEquivQuotSMul L (maximalIdeal 𝒪[F])
  have hcard : Nat.card (𝓛.Interval 0 𝓛.period) =
      Nat.card (TensorProduct 𝒪[F] (ResidueField 𝒪[F]) L) := by
    change Nat.card (L ⧸ 𝓛.intervalSubmodule 0 𝓛.period) = _
    rw [hsub]
    exact (Nat.card_congr e.toEquiv).symm
  rw [hcard, Module.natCard_eq_pow_finrank (K := ResidueField 𝒪[F]), Module.finrank_baseChange,
    hrank]

local notation "𝒪ₑ[" F "," E "]" => subfieldIntegers F E

/-- For a principal chain normalized by a field `E`, the residue degree of `E` divides the common
dimension `N / e` of the successive quotients. -/
theorem finrank_residueField_dvd_of_isPrincipal [FiniteDimensional F V] (hP : 𝓛.IsPrincipal)
    (E : Type*) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
    (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)
    [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsLocalHom (algebraMap 𝒪[F] 𝒪ₑ[F,E])]
    [Module.Finite 𝒪[F] 𝒪ₑ[F,E]] :
    Module.finrank (ResidueField 𝒪[F]) (ResidueField 𝒪ₑ[F,E]) ∣
      Module.finrank F V / 𝓛.period := by
  set q := Nat.card (ResidueField 𝒪[F]) with hqdef
  have hq : 1 < q := Finite.one_lt_card
  have h1 : ((𝓛.lattice 1).toAddSubgroup.relIndex (𝓛.lattice 0).toAddSubgroup) ^ 𝓛.period =
      q ^ Module.finrank F V := by
    rw [← 𝓛.relIndex_lattice_natCast_of_isPrincipal hP, ← natCard_interval_eq_relIndex,
      natCard_interval_period]
  have hc : Nat.card (𝓛.Layer 0) =
      (𝓛.lattice 1).toAddSubgroup.relIndex (𝓛.lattice 0).toAddSubgroup :=
    𝓛.natCard_interval_eq_relIndex 0 (0 + 1)
  let := 𝓛.subfieldLayerResidueModule E hE 0
  have := 𝓛.subfieldLayer_isScalarTower_residue E hE 0
  have : Module.Finite 𝒪[F] (𝓛.lattice 0) := Module.Finite.iff_fg.mpr (𝓛.fg_lattice 0)
  have : Module.Finite (ResidueField 𝒪[F]) (𝓛.Layer 0) :=
    Module.Finite.of_restrictScalars_finite 𝒪[F] _ _
  have : Finite (𝓛.Layer 0) := Module.finite_of_finite (ResidueField 𝒪[F])
  have h2 : Nat.card (𝓛.Layer 0) = Nat.card (ResidueField 𝒪ₑ[F,E]) ^
      Module.finrank (ResidueField 𝒪ₑ[F,E]) (𝓛.Layer 0) := Module.natCard_eq_pow_finrank
  have h3 : Nat.card (ResidueField 𝒪ₑ[F,E]) =
      q ^ Module.finrank (ResidueField 𝒪[F]) (ResidueField 𝒪ₑ[F,E]) :=
    Module.natCard_eq_pow_finrank
  rw [← hc, h2, h3, ← pow_mul, ← pow_mul] at h1
  have h4 := Nat.pow_right_injective hq h1
  refine ⟨Module.finrank (ResidueField 𝒪ₑ[F,E]) (𝓛.Layer 0), ?_⟩
  rw [← h4, ← mul_assoc, Nat.mul_div_cancel _ 𝓛.period_pos]

end Local

end Langlands.BushnellKutzko.LatticeChain
