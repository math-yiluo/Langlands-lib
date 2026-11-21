import Langlands.BushnellKutzko.CriticalDerivedSimpleLift
import Langlands.BushnellKutzko.CriticalDerivedPolynomial
import Langlands.BushnellKutzko.StratumApproximationReduction

/-! # Proof of the critical derived stratum theorem (BK93 (2.4.1)(iii)) -/

noncomputable section

open ValuativeRel IsLocalRing

namespace Langlands.BushnellKutzko

universe uF uE uK uV

namespace CriticalDerived

section Representative

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [FiniteDimensional F E]
  {K : Type uK} [Field K] [Algebra F K] [Module K V] [IsScalarTower F K V]
  [FiniteDimensional F K]

local instance : IsDiscreteValuationRing (subfieldIntegers F E) :=
  subfieldIntegers_isDiscreteValuationRing F E
local instance : IsDiscreteValuationRing (subfieldIntegers F K) :=
  subfieldIntegers_isDiscreteValuationRing F K

set_option maxHeartbeats 700000 in
private theorem exists_representative_of_scalar_matches
    (L : LatticeChain 𝒪[F] F V) (C : LatticeChain 𝒪[E] E V)
    (hlat : ∀ i, (C.lattice i : Set V) = L.lattice i)
    (hE : ∀ u : Eˣ, subfieldUnits F E V u ∈ L.stabilizer)
    (hK : ∀ u : Kˣ, subfieldUnits F K V u ∈ L.stabilizer)
    (φ : subfieldIntegers F E ≃+* 𝒪[E]) (hφ : ∀ a, (φ a : E) = (a : E))
    {d : ℤ} {a : Module.End E V} (ha : restrictEnd a ∉ L.endFiltration (d + 1))
    (haK : ∃ k : K, SymbolEq L d (restrictEnd a) (subfieldEmbedding F K V k))
    (hEK : ∀ (j : ℤ) (e : E), subfieldEmbedding F E V e ∈ L.endFiltration j →
      ∃ k : K, SymbolEq L j (subfieldEmbedding F E V e) (subfieldEmbedding F K V k)) :
    ∃ c : Module.End E V, SymbolEq C d c a ∧
      (∃ h : IsField (elementAlgebra c), letI := h.toField
        ∀ u : (elementAlgebra c)ˣ, subfieldUnits E (elementAlgebra c) V u ∈ C.stabilizer) ∧
      criticalExponent C c ≤ (d : WithBot ℤ) := by
  obtain ⟨u, hu, haSym⟩ := exists_matching_scalar_unit L hK ha haK
  obtain ⟨A, hA, hAs⟩ := exists_unit_of_symbolEq L C hlat hu haSym
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  let π₀ := LatticeChain.uniformizerAsUnit hϖ
  let π : (Module.End E V)ˣ := scalarEndUnit π₀
  let ρ : (Module.End E V)ˣ →* (Module.End F V)ˣ := Units.map restrictEnd.toMonoidHom
  let μ := subfieldUnits F K V
  have hπ : Shifts C C.period π := uniformizerUnit_shifts hϖ C
  have hπF : Shifts L C.period (ρ π) := (shifts_restrict L C hlat).mpr hπ
  have hAF : Shifts L d (ρ A) := (shifts_restrict L C hlat).mpr hAs
  obtain ⟨v, hv, hπSym⟩ := exists_matching_scalar_unit L hK hπF.not_mem_succ
    (hEK C.period (π₀ : E) hπF.1)
  obtain ⟨N⟩ := exists_shiftParameters C.period_spec.1 d
  let w : Kˣ := u ^ (N.h : ℤ) * v ^ (-N.k)
  have hw : Shifts L 0 (μ w) := by
    have h := (hu.zpow (N.h : ℤ)).mul (hv.zpow (-N.k))
    rw [N.residual_degree] at h
    simpa only [w, map_mul, map_zpow] using h
  let ζ : subfieldIntegers F K := ⟨w, (scalar_mem_zero_iff L hK (w : K)).mp hw.1⟩
  have hζ : residue (subfieldIntegers F K) ζ ≠ 0 :=
    fun hz => hw.not_mem_succ ((scalar_mem_one_iff L hK ζ).mpr hz)
  have hASym : SymbolEq L d (↑(ρ A) : Module.End F V) (μ u) := by
    change SymbolEq L d (restrictEnd (A : Module.End E V)) (μ u)
    rw [hA]
    exact haSym
  have hzSym : SymbolEq L 0 (restrictEnd (↑(N.residual A π) : Module.End E V))
      (subfieldEmbedding F K V (ζ : K)) := by
    have h := (SymbolEq.zpow hAF hu hASym (N.h : ℤ)).mul
      (SymbolEq.zpow hπF hv hπSym (-N.k))
    rw [N.residual_degree] at h
    change SymbolEq L 0 (↑(ρ (N.residual A π)) : Module.End F V) (μ w)
    simpa only [ShiftParameters.residual, w, map_mul, map_zpow, Units.val_mul] using h
  obtain ⟨f, hf⟩ := exists_residue_map L hK hE (hEK 0)
  let f' := f.comp (ResidueField.mapEquiv φ.symm).toRingHom
  obtain ⟨P, hP, hP₀, hp, hzP⟩ := exists_residual_polynomial L hK C hlat ζ hζ hzSym f' (by
    intro r
    obtain ⟨t, ht, hr⟩ := hf (φ.symm r)
    refine ⟨t, ?_, ?_⟩
    · rwa [show (φ.symm r : E) = (r : E) from (hφ _).symm.trans
        (congrArg (fun s : 𝒪[E] => (s : E)) (φ.apply_symm_apply r))] at ht
    · exact hr)
  obtain ⟨c, hc, hfC, hkC⟩ := exists_simple_cyclic_lift C A hAs hϖ N P hP hP₀ hp hzP
  rw [hA] at hc
  exact ⟨c, hc, hfC, hkC⟩

end Representative
end CriticalDerived

open CriticalDerived

set_option maxHeartbeats 700000 in
/-- **BK93 (2.4.1)(iii).** The critical derived stratum for any equivalent simple
representative and any tame corestriction is equivalent to a simple stratum. -/
theorem criticalDerivedStratum : CriticalDerivedStratumStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ _ S T hS hk hchain _hn hr hT hST
  obtain ⟨hKf, hKn⟩ := hS.1
  intro hEf
  let := hEf.toField
  let := hKf.toField
  intro s
  let E := elementAlgebra T.b
  let K := elementAlgebra S.b
  let d := -T.r
  let a := s (S.b - T.b)
  have hEn : ∀ u : Eˣ, subfieldUnits F E V u ∈ T.chain.stabilizer := by
    obtain ⟨_, h⟩ := hT.1.1
    exact h
  have hKn' : ∀ u : Kˣ, subfieldUnits F K V u ∈ T.chain.stabilizer := by
    rw [hchain]
    exact hKn
  have hb : S.b - T.b ∈ T.chain.endFiltration d := by
    simpa only [d, hchain, hr] using Stratum.sub_mem_of_equivalent hST
  have hkS : criticalExponent T.chain S.b = (d : WithBot ℤ) := by
    simpa only [d, hchain, hr] using hk
  obtain ⟨⟨ha, ha', haK⟩, hEK⟩ :=
    derived_scalar_symbols T.chain S.b T.b d hKf hEf hb hkS hT.2 s hEn hKn'
  let : FiniteDimensional F E := Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
  let : FiniteDimensional F K := Module.Finite.of_injective K.val.toLinearMap Subtype.val_injective
  let B : LatticeChain (subfieldIntegers F E) E V := T.chain.extensionChain hEn
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  have := LocalField.FiniteExtension.isLocalField F E
  have : IsScalarTower 𝒪[E] E V := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let φ := subfieldIntegerEquiv F E
  let C := B.transfer φ (fun _ => rfl)
  have hBC (i : ℤ) : (B.lattice i : Set V) = C.lattice i := rfl
  have hlat (i : ℤ) : (C.lattice i : Set V) = T.chain.lattice i := rfl
  obtain ⟨c, hc, ⟨hcf, hcn⟩, hck⟩ :=
    exists_representative_of_scalar_matches T.chain C hlat hEn hKn' φ (fun _ => rfl)
      (a := a) ha' (by
        obtain ⟨k, hk, hs⟩ := haK
        exact ⟨k, ha, hk, hs⟩) (by
        intro j e he
        obtain ⟨k, hk, hs⟩ := hEK j e he
        exact ⟨k, he, hk, hs⟩)
  have haC : a ∉ C.endFiltration (d + 1) :=
    fun hm => ha' ((mem_endFiltration_restrictScalars hlat).mp hm)
  have haVal : B.valuation a = (d : WithTop ℤ) := by
    rw [LatticeChain.valuation_congr hBC]
    exact C.valuation_eq_of_mem_of_notMem hc.2.1 haC
  have hcVal : B.valuation c = (d : WithTop ℤ) := by
    rw [LatticeChain.valuation_congr hBC]
    exact C.valuation_eq_of_mem_of_notMem hc.1 (hc.not_mem_succ haC)
  let D : Stratum (subfieldIntegers F E) E V := ⟨B, T.r, T.r - 1, a, by omega, haVal.ge⟩
  let R : Stratum (subfieldIntegers F E) E V := ⟨B, T.r, T.r - 1, c, by omega, hcVal.ge⟩
  refine ⟨D, R, ⟨hT, ⟨elementGenerator T.b, subfieldEmbedding_elementGenerator T.b hEf,
    adjoin_elementGenerator T.b⟩, hb, fun _ => rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, ?_, ?_⟩
  · apply Stratum.equivalent_of_sub_mem (S := D) (T := R) rfl rfl
    change a - c ∈ B.endFiltration (-(T.r - 1))
    rw [LatticeChain.mem_endFiltration_congr hBC, show -(T.r - 1) = d + 1 by dsimp [d]; omega]
    exact hc.symm.2.2
  · refine ⟨⟨⟨hcf, ?_⟩, hcVal⟩, ?_⟩
    · let := hcf.toField
      intro u
      exact (LatticeChain.mem_stabilizer_congr hBC).mpr (hcn u)
    · change criticalExponent B c < ((-(T.r - 1) : ℤ) : WithBot ℤ)
      rw [LatticeChain.criticalExponent_congr hBC]
      exact hck.trans_lt (WithBot.coe_lt_coe.mpr (by dsimp [d]; omega))

end Langlands.BushnellKutzko
