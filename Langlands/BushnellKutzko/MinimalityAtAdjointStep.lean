import Langlands.BushnellKutzko.SubfieldLayerMinimality

/-! # Minimality and containment of the first adjoint lattice above the shift -/

noncomputable section

open ValuativeRel IsLocalRing IsDiscreteValuationRing

namespace Langlands.BushnellKutzko.LatticeChain

universe uF uV uE

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V) (E : Type uE) [Field E] [Algebra F E]
  [Module E V] [IsScalarTower F E V]
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)

local notation "𝒪ₑ[" F "," E "]" => subfieldIntegers F E
local notation "kₑ[" F "," E "]" => ResidueField (subfieldIntegers F E)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem commute_subfield_of_commute_generator (b : E) (z : Module.End F V)
    (hgen : Algebra.adjoin F ({b} : Set E) = ⊤) (hb : Commute (subfieldEmbedding F E V b) z)
    (a : E) : Commute (subfieldEmbedding F E V a) z := by
  let C := (Subalgebra.centralizer F ({z} : Set (Module.End F V))).comap (subfieldEmbedding F E V)
  have hcl : Algebra.adjoin F ({b} : Set E) ≤ C := by
    apply Algebra.adjoin_le
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact (Subalgebra.mem_centralizer_iff F).mpr (by
      intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact hb.eq.symm)
  have ha : a ∈ C := hcl (hgen.symm ▸ (show a ∈ (⊤ : Subalgebra F E) from by simp))
  exact ((Subalgebra.mem_centralizer_iff F).mp ha z (Set.mem_singleton _)).symm

variable [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsFractionRing 𝒪ₑ[F,E] E]

/-- Containment one step above the shift is equivalent to graded generation
by the chosen element and a base uniformizer. -/
theorem subfieldLayerGeneration_iff_adjointLattice_le (b : Eˣ) {π : 𝒪[F]} (hπ : Irreducible π)
    (hgen : Algebra.adjoin F ({(b : E)} : Set E) = ⊤) :
    𝓛.subfieldLayerGeneration E hE b (baseIntegerUnit E hπ.ne_zero) ↔
      adjointLattice 𝓛 (subfieldEmbedding F E V (b : E)) ((𝓛.fieldShift E hE b).toAdd + 1) ≤
        centralizerLattice 𝓛 (subfieldEmbedding F E V (b : E)) 0 ⊔ 𝓛.endFiltration 1 := by
  let g := 𝓛.subfieldStabilizer E hE b
  let B := subfieldEmbedding F E V (b : E)
  let c := baseIntegerUnit E hπ.ne_zero
  have hc : 𝓛.subfieldStabilizer E hE c = 𝓛.uniformizerStabilizer hπ :=
    𝓛.subfieldStabilizer_baseUniformizer E hE hπ
  constructor
  · intro h x hx
    let x₀ : 𝓛.order := ⟨x, hx.1⟩
    let D := 𝓛.layerAction x₀
    have hbD : b ∈ 𝓛.subfieldLayerCommutingSubgroup E hE D :=
      (𝓛.layerAction_commutes_iff x₀ g).mpr hx.2
    have hcD : c ∈ 𝓛.subfieldLayerCommutingSubgroup E hE D := by
      change 𝓛.LayerFamilyCommutes D (𝓛.subfieldStabilizer E hE c)
      rw [hc]
      exact 𝓛.layerAction_commutes_uniformizer hπ x₀
    obtain ⟨y, hy, hDy⟩ := 𝓛.exists_subfield_lift_layers E hE D (h D hbD hcD)
    let yF := y.restrictScalars F
    have hyComm : Commute B yF := by
      apply LinearMap.ext
      intro v
      change (b : E) • y v = y ((b : E) • v)
      exact (y.map_smul (b : E) v).symm
    have hy₀ : yF ∈ centralizerLattice 𝓛 B 0 := ⟨hy, sub_eq_zero.mpr hyComm.eq⟩
    have hdiff : x - yF ∈ 𝓛.endFiltration 1 :=
      (𝓛.layerAction_eq_iff x₀ ⟨yF, hy⟩).mp fun i => (hDy i).symm
    exact Submodule.mem_sup.mpr ⟨yF, hy₀, x - yF, hdiff, by abel⟩
  · intro h D hbD hcD a
    have hbase : 𝓛.LayerFamilyCommutes D (𝓛.uniformizerStabilizer hπ) :=
      hc ▸ (show 𝓛.LayerFamilyCommutes D (𝓛.subfieldStabilizer E hE c) from hcD)
    obtain ⟨x, hxD⟩ := 𝓛.exists_order_lift_layers hπ D hbase
    have hD : 𝓛.layerAction x = D := funext hxD
    have hbx : 𝓛.LayerFamilyCommutes (𝓛.layerAction x) g := hD.symm ▸ hbD
    have hx : x.val ∈ adjointLattice 𝓛 B ((𝓛.fieldShift E hE b).toAdd + 1) :=
      ⟨x.prop, (𝓛.layerAction_commutes_iff x g).mp hbx⟩
    obtain ⟨y, hy, p, hp, hsum⟩ := Submodule.mem_sup.mp (h hx)
    let y₀ : 𝓛.order := ⟨y, hy.1⟩
    have hdiff : x.val - y ∈ 𝓛.endFiltration 1 := by
      rw [← hsum, add_comm y, add_sub_cancel_right]
      exact hp
    have hyD : 𝓛.layerAction y₀ = D := funext fun i =>
      ((𝓛.layerAction_eq_iff x y₀).mpr hdiff i).symm.trans (hxD i)
    have hyComm : Commute B y := sub_eq_zero.mp hy.2
    have haComm : Commute (subfieldEmbedding F E V (a : E)) y :=
      commute_subfield_of_commute_generator E (b : E) y hgen hyComm (a : E)
    have hyAction := 𝓛.layerAction_commutes_of_commute y₀ (𝓛.subfieldStabilizer E hE a) haComm
    exact hyD ▸ hyAction

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsFractionRing 𝒪ₑ[F,E] E] in
private theorem residue_adjoin_eq_top_iff (a : 𝒪ₑ[F,E]) :
    Algebra.adjoin 𝒪[F] ({residue 𝒪ₑ[F,E] a} : Set kₑ[F,E]) = ⊤ ↔
      Algebra.adjoin 𝒪[F]
        ({Ideal.Quotient.mk (subfieldMaximalIdeal F E) a} : Set (subfieldResidueRing F E)) = ⊤ := by
  let f := subfieldResidueEquiv (F := F) E
  have hr : f.toAlgHom.range = ⊤ := by
    apply top_unique
    intro y _
    exact f.surjective y
  have hm : (Algebra.adjoin 𝒪[F]
        ({Ideal.Quotient.mk (subfieldMaximalIdeal F E) a} : Set (subfieldResidueRing F E))).map
          f.toAlgHom = Algebra.adjoin 𝒪[F] ({residue 𝒪ₑ[F,E] a} : Set kₑ[F,E]) := by
    rw [AlgHom.map_adjoin_singleton]
    rfl
  rw [← hm, ← hr, ← Algebra.map_top]
  exact (Subalgebra.map_injective f.injective).eq_iff

/-- The arithmetic minimality condition is precisely containment in the integral
centralizer plus depth one at the next adjoint step. -/
theorem isMinimalOver_iff_adjointLattice_le (b : Eˣ)
    (hgen : Algebra.adjoin F ({(b : E)} : Set E) = ⊤) :
    IsMinimalOver F E (b : E) ↔
      adjointLattice 𝓛 (subfieldEmbedding F E V (b : E)) ((𝓛.fieldShift E hE b).toAdd + 1) ≤
        centralizerLattice 𝓛 (subfieldEmbedding F E V (b : E)) 0 ⊔ 𝓛.endFiltration 1 := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪ₑ[F,E]
  obtain ⟨ν, v, hv⟩ := subfieldUnit_factorization E hϖ b
  let t := (𝓛.fieldShift E hE (subfieldIntegerUnit E hϖ.ne_zero)).toAdd
  let e : ℤ := subfieldRamificationIndex F E
  have ht : 0 < t := 𝓛.fieldShift_uniformizer_pos E hE hϖ
  have hval := 𝓛.subfieldNormalizedValuation_eq_of_factorization E hE hϖ hv
  have hb := 𝓛.fieldShift_eq_mul_of_factorization E hE hϖ.ne_zero hv
  have hperiod : t * e = 𝓛.period := 𝓛.fieldShift_uniformizer_mul_ramification E hE hϖ
  have hc {π : 𝒪[F]} (hπ : Irreducible π) :
      (𝓛.fieldShift E hE (baseIntegerUnit E hπ.ne_zero)).toAdd = t * e :=
    (𝓛.fieldShift_baseUniformizer E hE hπ).trans hperiod.symm
  have hy {π : 𝒪[F]} (hπ : Irreducible π) :
      ∃ u : 𝒪ₑ[F,E]ˣ, (baseIntegerUnit E hπ.ne_zero) ^ (-ν) * b ^ e = subfieldIntegerUnits E u := by
    apply 𝓛.exists_integerUnit_of_fieldShift_zero E hE
    rw [𝓛.fieldShift_zpow_mul E hE, hc hπ, hb]
    ring
  have hycoe {π : 𝒪[F]} (hπ : Irreducible π) (u : 𝒪ₑ[F,E]ˣ)
      (hu : (baseIntegerUnit E hπ.ne_zero) ^ (-ν) * b ^ e = subfieldIntegerUnits E u) :
      ((u : 𝒪ₑ[F,E]) : E) = algebraMap F E (π : F) ^ (-ν) *
        (b : E) ^ subfieldRamificationIndex F E := by
    have h := congrArg (fun z : Eˣ => (z : E)) hu
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, baseIntegerUnit_val] at h
    change algebraMap F E (π : F) ^ (-ν) * (b : E) ^ (subfieldRamificationIndex F E : ℤ) = _ at h
    rwa [zpow_natCast, eq_comm] at h
  have hcriterion {π : 𝒪[F]} (hπ : Irreducible π) (u : 𝒪ₑ[F,E]ˣ)
      (hu : (baseIntegerUnit E hπ.ne_zero) ^ (-ν) * b ^ e = subfieldIntegerUnits E u) :
      (adjointLattice 𝓛 (subfieldEmbedding F E V (b : E)) ((𝓛.fieldShift E hE b).toAdd + 1) ≤
        centralizerLattice 𝓛 (subfieldEmbedding F E V (b : E)) 0 ⊔ 𝓛.endFiltration 1) ↔
      Nat.Coprime ν.natAbs (subfieldRamificationIndex F E) ∧
        Algebra.adjoin 𝒪[F]
          ({Ideal.Quotient.mk (subfieldMaximalIdeal F E) (u : 𝒪ₑ[F,E])} :
            Set (subfieldResidueRing F E)) = ⊤ := by
    rw [← 𝓛.subfieldLayerGeneration_iff_adjointLattice_le E hE b hπ hgen,
      𝓛.subfieldLayerGeneration_iff E hE b (baseIntegerUnit E hπ.ne_zero) hϖ t ν e ht rfl
        hb (hc hπ) u hu,
      residue_adjoin_eq_top_iff E (u : 𝒪ₑ[F,E])]
    rfl
  constructor
  · rintro ⟨_, n, hn, hcop, π, _, hspan, y, hy', hres⟩
    have hnν := WithTop.coe_eq_coe.mp (hn.symm.trans hval)
    subst n
    have hπ : Irreducible π := (irreducible_iff_uniformizer π).mpr hspan.symm
    obtain ⟨u, hu⟩ := hy hπ
    have hEq : y = (u : 𝒪ₑ[F,E]) := Subtype.ext (hy'.trans (hycoe hπ u hu).symm)
    exact (hcriterion hπ u hu).mpr ⟨hcop, hEq ▸ hres⟩
  · intro h
    obtain ⟨π, hπ⟩ := exists_irreducible 𝒪[F]
    obtain ⟨u, hu⟩ := hy hπ
    obtain ⟨hcop, hres⟩ := (hcriterion hπ u hu).mp h
    exact ⟨hgen, ν, hval, hcop, π, hπ.ne_zero, hπ.maximalIdeal_eq.symm, u, hycoe hπ u hu, hres⟩

end Langlands.BushnellKutzko.LatticeChain

namespace Langlands.BushnellKutzko

universe uF uV uE

/-- Arithmetic minimality is the adjoint containment one step above the generator's shift. -/
def MinimalityAtAdjointStepStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (E : Type uE) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
    (𝓛 : LatticeChain 𝒪[F] F V)
    (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer) (b : Eˣ),
    Algebra.adjoin F ({(b : E)} : Set E) = ⊤ →
    let B := subfieldEmbedding F E V (b : E)
    let d := (𝓛.fieldShift E hE b).toAdd
    IsMinimalOver F E (b : E) ↔
      adjointLattice 𝓛 B (d + 1) ≤ centralizerLattice 𝓛 B 0 ⊔ 𝓛.endFiltration 1

theorem minimalityAtAdjointStep : MinimalityAtAdjointStepStatement.{uF,uV,uE} := by
  intro F _ _ _ _ V _ _ E _ _ _ _ 𝓛 hE b hgen
  have := 𝓛.finiteDimensional_subfield E
  have := subfieldIntegers_isDiscreteValuationRing F E
  have := subfieldIntegers_isFractionRing F E
  exact 𝓛.isMinimalOver_iff_adjointLattice_le E hE b hgen

end Langlands.BushnellKutzko
