import Langlands.BushnellKutzko.MinimalSimpleStratumPolynomialStatement
import Langlands.BushnellKutzko.MinimalCriticalExponentProof
import Langlands.BushnellKutzko.MinimalElementInvariants
import Langlands.BushnellKutzko.PrincipalChainResidueDegree
import Langlands.BushnellKutzko.LatticeChainLayerIntertwining
import Langlands.BushnellKutzko.SubfieldLayerLifting

/-! # Polynomial labels of simple strata at depth `n − 1`

This module proves `Langlands.BushnellKutzko.MinimalSimpleStratumPolynomialStatement`
(Bushnell–Kutzko 1994, (1.4)–(1.5), printed pp. 112–113, for principal orders).

For a simple stratum `[𝔄, n, n − 1, b]` the algebra `E = F[b]` is a field normalizing the chain
and `b` shifts it by `-n`. The critical exponent makes `b` minimal
(`LatticeChain.isMinimalOver_of_criticalExponent_lt`, through `minimalCriticalExponent` or, for
scalar `b`, `LatticeChain.isMinimalOver_of_mem_range`). The unit `y = π^{n/g} b^{e/g}` lies in
`𝔬_Eˣ`; its residue `c` generates `k_E`, the fundamental polynomial is `f^a` for `f` the image of
the minimal polynomial of `c`, and the invariants of `E` follow. Two such strata with the same `f`
have residues with the same minimal polynomial, which act conjugately on every layer; the layer
automorphisms transported along the orbits of `π` and `b` lift to `u ∈ U(𝔄)`.
-/

open Polynomial ValuativeRel IsLocalRing IsDiscreteValuationRing

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uE uE₁ uE₂

local notation "𝒪ₑ[" F "," E "]" => subfieldIntegers F E

/-- The integral closure of `𝒪_F` is a local extension of `𝒪_F`. -/
theorem subfieldIntegers_isLocalHom (F : Type uF) [Field F] [ValuativeRel F] (E : Type uE)
    [Field E] [Algebra F E] : IsLocalHom (algebraMap 𝒪[F] 𝒪ₑ[F,E]) := by
  have : Algebra.IsIntegral 𝒪[F] 𝒪ₑ[F,E] := inferInstanceAs
    (Algebra.IsIntegral 𝒪[F] (integralClosure 𝒪[F] E))
  have : FaithfulSMul 𝒪[F] 𝒪ₑ[F,E] := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    have h := congrArg (fun z : 𝒪ₑ[F,E] => (z : E)) hxy
    simp only [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply 𝒪[F] F E] at h
    exact Subtype.val_injective ((algebraMap F E).injective h)
  infer_instance

/-- The generator of `F[b]` generates it as an algebra. -/
theorem adjoin_elementAlgebra_generator {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V]
    [Module F V] (b : Module.End F V) :
    Algebra.adjoin F ({(⟨b, Algebra.self_mem_adjoin_singleton F b⟩ : elementAlgebra b)} :
      Set (elementAlgebra b)) = ⊤ := by
  apply Subalgebra.map_injective (f := (elementAlgebra b).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val, Set.image_singleton]
  rfl

/-- A positive power of a monic irreducible polynomial over a field determines it. -/
theorem eq_of_pow_eq_pow_of_irreducible {k : Type*} [Field k] {f p : k[X]} (hf : f.Monic)
    (hfi : Irreducible f) (hp : p.Monic) (hpi : Irreducible p) {a m : ℕ} (ha : 0 < a)
    (h : f ^ a = p ^ m) : f = p := by
  have hdvd : f ∣ p ^ m := h ▸ dvd_pow_self f ha.ne'
  exact eq_of_monic_of_associated hf hp
    (hfi.associated_of_dvd hpi (hfi.prime.dvd_of_dvd_pow hdvd))

namespace LatticeChain

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

section Single

variable (E : Type uE) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)
  [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsFractionRing 𝒪ₑ[F,E] E]

omit [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsFractionRing 𝒪ₑ[F,E] E] in
/-- The unit `ϖ^{n/g} β^{e/g}`, with `g = gcd(e, n)`, has shift zero. -/
theorem fieldShift_fundamentalUnit (β : Eˣ) {n : ℤ} (hβ : (𝓛.fieldShift E hE β).toAdd = -n)
    {π : 𝒪[F]} (hπ : Irreducible π) :
    (𝓛.fieldShift E hE (baseIntegerUnit E hπ.ne_zero ^ (n / (Nat.gcd 𝓛.period n.natAbs : ℤ)) *
      β ^ (𝓛.period / Nat.gcd 𝓛.period n.natAbs))).toAdd = 0 := by
  obtain ⟨e', he'⟩ := Nat.gcd_dvd_left 𝓛.period n.natAbs
  obtain ⟨n', hn'⟩ : ((Nat.gcd 𝓛.period n.natAbs : ℕ) : ℤ) ∣ n :=
    Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
  have hg : 0 < Nat.gcd 𝓛.period n.natAbs := Nat.gcd_pos_of_pos_left _ 𝓛.period_pos
  have hb := 𝓛.fieldShift_baseUniformizer E hE hπ
  simp only [map_mul, map_zpow, map_pow, toAdd_mul, toAdd_zpow, toAdd_pow, hβ]
  rw [show (𝓛.fieldShift E hE (baseIntegerUnit E hπ.ne_zero)).toAdd = 𝓛.period from hb]
  generalize 𝓛.period.gcd n.natAbs = g at he' hn' hg ⊢
  rw [smul_eq_mul, nsmul_eq_mul, hn', he', Int.mul_ediv_cancel_left _ (by exact_mod_cast hg.ne'),
    Nat.mul_div_cancel_left _ hg]
  push_cast
  ring

include hE in
/-- For a generator whose critical exponent lies below `1 - n`, where `-n` is its order
valuation, the generator is minimal; in the scalar case the extension is trivial. -/
theorem isMinimalOver_of_criticalExponent_lt [FiniteDimensional F V] (β : Eˣ)
    (hgen : Algebra.adjoin F ({(β : E)} : Set E) = ⊤) {n : ℤ}
    (hval : 𝓛.valuation (subfieldEmbedding F E V (β : E)) = ((-n : ℤ) : WithTop ℤ))
    (hcrit : criticalExponent 𝓛 (subfieldEmbedding F E V (β : E)) < ((1 - n : ℤ) : WithBot ℤ)) :
    IsMinimalOver F E (β : E) := by
  by_cases hscalar : ∃ a : F, algebraMap F E a = β
  · exact 𝓛.isMinimalOver_of_mem_range E hE β hgen hscalar
  · obtain ⟨k₀, hk₀, hle, heq⟩ := minimalCriticalExponent F V E 𝓛 (β : E) hgen hscalar hE
    apply heq.mp
    rw [hk₀] at hcrit
    have hk : k₀ < 1 - n := WithBot.coe_lt_coe.mp hcrit
    rw [hval] at hle ⊢
    have := WithTop.coe_le_coe.mp hle
    congr 1
    omega

end Single

section Pair

/-- The layer map of `ϖ^{n/g} β^{e/g}` is multiplication by the residue of the corresponding
integral unit. -/
theorem stabilizerLayerEquiv_fundamentalUnit (E : Type uE) [Field E] [Algebra F E] [Module E V]
    [IsScalarTower F E V] (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)
    [IsDiscreteValuationRing 𝒪ₑ[F,E]] (β : Eˣ) {n : ℤ} {π : 𝒪[F]} (hπ : Irreducible π)
    (w : 𝒪ₑ[F,E]ˣ)
    (hw : baseIntegerUnit E hπ.ne_zero ^ (n / (Nat.gcd 𝓛.period n.natAbs : ℤ)) *
      β ^ (𝓛.period / Nat.gcd 𝓛.period n.natAbs) = subfieldIntegerUnits E w) (r : ℤ)
    (h : r = r + 𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ ^
      (n / (Int.gcd (𝓛.period : ℤ) n : ℤ)) * 𝓛.subfieldStabilizer E hE β ^
        ((𝓛.period : ℤ) / (Int.gcd (𝓛.period : ℤ) n : ℤ)))) (q : 𝓛.Layer r) :
    letI := 𝓛.subfieldLayerResidueModule E hE r
    𝓛.stabilizerLayerEquiv _ r r h q = residue 𝒪ₑ[F,E] (w : 𝒪ₑ[F,E]) • q := by
  let := 𝓛.subfieldLayerResidueModule E hE r
  have hgcd : (Int.gcd (𝓛.period : ℤ) n : ℤ) = (Nat.gcd 𝓛.period n.natAbs : ℤ) := rfl
  have hdiv : (𝓛.period : ℤ) / (Nat.gcd 𝓛.period n.natAbs : ℤ) =
      ((𝓛.period / Nat.gcd 𝓛.period n.natAbs : ℕ) : ℤ) := (Int.natCast_div _ _).symm
  have helt : 𝓛.uniformizerStabilizer hπ ^ (n / (Int.gcd (𝓛.period : ℤ) n : ℤ)) *
      𝓛.subfieldStabilizer E hE β ^ ((𝓛.period : ℤ) / (Int.gcd (𝓛.period : ℤ) n : ℤ)) =
      𝓛.subfieldStabilizer E hE (subfieldIntegerUnits E w) := by
    rw [← hw, hgcd, hdiv, zpow_natCast, map_mul, map_zpow, map_pow,
      𝓛.subfieldStabilizer_baseUniformizer E hE hπ]
  have h' : r = r + 𝓛.stabilizerValuation (𝓛.subfieldStabilizer E hE (subfieldIntegerUnits E w)) :=
    helt ▸ h
  rw [𝓛.stabilizerLayerEquiv_congr helt h h', 𝓛.subfieldLayerEquiv_integerUnit E hE w r h' q]

/-- Two minimal generators of normalizing fields with the same shift `-n`, whose fundamental
units have residues with the same minimal polynomial, are conjugate under `U(𝔄)` modulo
`𝔓^{1-n}`. -/
theorem exists_unitFiltration_conj_of_minpoly_eq
    (E₁ : Type uE₁) [Field E₁] [Algebra F E₁] [Module E₁ V] [IsScalarTower F E₁ V]
    (hE₁ : ∀ a : E₁ˣ, subfieldUnits F E₁ V a ∈ 𝓛.stabilizer)
    [IsDiscreteValuationRing 𝒪ₑ[F,E₁]] [IsLocalHom (algebraMap 𝒪[F] 𝒪ₑ[F,E₁])]
    (E₂ : Type uE₂) [Field E₂] [Algebra F E₂] [Module E₂ V] [IsScalarTower F E₂ V]
    (hE₂ : ∀ a : E₂ˣ, subfieldUnits F E₂ V a ∈ 𝓛.stabilizer)
    [IsDiscreteValuationRing 𝒪ₑ[F,E₂]] [IsLocalHom (algebraMap 𝒪[F] 𝒪ₑ[F,E₂])]
    (β₁ : E₁ˣ) (β₂ : E₂ˣ) {n : ℤ} (hβ₁ : (𝓛.fieldShift E₁ hE₁ β₁).toAdd = -n)
    (hβ₂ : (𝓛.fieldShift E₂ hE₂ β₂).toAdd = -n) {π : 𝒪[F]} (hπ : Irreducible π)
    (w₁ : 𝒪ₑ[F,E₁]ˣ) (w₂ : 𝒪ₑ[F,E₂]ˣ)
    (hw₁ : baseIntegerUnit E₁ hπ.ne_zero ^ (n / (Nat.gcd 𝓛.period n.natAbs : ℤ)) *
      β₁ ^ (𝓛.period / Nat.gcd 𝓛.period n.natAbs) = subfieldIntegerUnits E₁ w₁)
    (hw₂ : baseIntegerUnit E₂ hπ.ne_zero ^ (n / (Nat.gcd 𝓛.period n.natAbs : ℤ)) *
      β₂ ^ (𝓛.period / Nat.gcd 𝓛.period n.natAbs) = subfieldIntegerUnits E₂ w₂)
    (hint₁ : IsIntegral (ResidueField 𝒪[F]) (residue 𝒪ₑ[F,E₁] (w₁ : 𝒪ₑ[F,E₁])))
    (h : minpoly (ResidueField 𝒪[F]) (residue 𝒪ₑ[F,E₁] (w₁ : 𝒪ₑ[F,E₁])) =
      minpoly (ResidueField 𝒪[F]) (residue 𝒪ₑ[F,E₂] (w₂ : 𝒪ₑ[F,E₂]))) :
    ∃ u ∈ 𝓛.unitFiltration 0,
      ((u⁻¹ : (Module.End F V)ˣ) : Module.End F V) * subfieldEmbedding F E₁ V (β₁ : E₁) *
        (u : Module.End F V) - subfieldEmbedding F E₂ V (β₂ : E₂) ∈
          𝓛.endFiltration (1 - n) := by
  choose ψ hψ using fun r => 𝓛.exists_layerEquiv_residue_intertwine E₁ hE₁ E₂ hE₂
    (residue 𝒪ₑ[F,E₁] (w₁ : 𝒪ₑ[F,E₁])) (residue 𝒪ₑ[F,E₂] (w₂ : 𝒪ₑ[F,E₂])) hint₁ h r
  have hP : 𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ) = (𝓛.period : ℤ) :=
    𝓛.uniformizerStabilizer_shift hπ
  have hB₁ : 𝓛.stabilizerValuation (𝓛.subfieldStabilizer E₁ hE₁ β₁) = -n := hβ₁
  have hB₂ : 𝓛.stabilizerValuation (𝓛.subfieldStabilizer E₂ hE₂ β₂) = -n := hβ₂
  have hc₁ : Commute (𝓛.uniformizerStabilizer hπ) (𝓛.subfieldStabilizer E₁ hE₁ β₁) := by
    rw [← 𝓛.subfieldStabilizer_baseUniformizer E₁ hE₁ hπ]
    exact (Commute.all (baseIntegerUnit E₁ hπ.ne_zero) β₁).map (𝓛.subfieldStabilizer E₁ hE₁)
  have hc₂ : Commute (𝓛.uniformizerStabilizer hπ) (𝓛.subfieldStabilizer E₂ hE₂ β₂) := by
    rw [← 𝓛.subfieldStabilizer_baseUniformizer E₂ hE₂ hπ]
    exact (Commute.all (baseIntegerUnit E₂ hπ.ne_zero) β₂).map (𝓛.subfieldStabilizer E₂ hE₂)
  have he : (0 : ℤ) < (𝓛.period : ℤ) := by exact_mod_cast 𝓛.period_pos
  obtain ⟨φ, hφP, hφB⟩ := 𝓛.exists_layer_intertwiner hP hB₁ hB₂ hc₁ hc₂ he ψ
    (fun r h₁ h₂ q => by
      rw [𝓛.stabilizerLayerEquiv_fundamentalUnit E₂ hE₂ β₂ hπ w₂ hw₂ r h₂,
        𝓛.stabilizerLayerEquiv_fundamentalUnit E₁ hE₁ β₁ hπ w₁ hw₁ r h₁]
      exact hψ r q)
  obtain ⟨u, hu, hconj⟩ := 𝓛.exists_unitFiltration_conj_sub_mem hπ hB₁ hB₂ φ hφP hφB
  refine ⟨u, hu, ?_⟩
  have e₁ : (((𝓛.subfieldStabilizer E₁ hE₁ β₁ : 𝓛.stabilizer) : (Module.End F V)ˣ) :
      Module.End F V) = subfieldEmbedding F E₁ V (β₁ : E₁) := rfl
  have e₂ : (((𝓛.subfieldStabilizer E₂ hE₂ β₂ : 𝓛.stabilizer) : (Module.End F V)ˣ) :
      Module.End F V) = subfieldEmbedding F E₂ V (β₂ : E₂) := rfl
  rw [e₁, e₂] at hconj
  exact hconj

end Pair

end LatticeChain

section Setup

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The image of `π^k β^l` in `End_F(V)`. -/
theorem subfieldEmbedding_baseIntegerUnit_zpow_mul (E : Type uE) [Field E] [Algebra F E]
    [Module E V] [IsScalarTower F E V] (β : Eˣ) {π : 𝒪[F]} (hπ : π ≠ 0) (k : ℤ) (l : ℕ) :
    subfieldEmbedding F E V ((baseIntegerUnit E hπ ^ k * β ^ l : Eˣ) : E) =
      (algebraMap 𝒪[F] F π ^ k) • subfieldEmbedding F E V (β : E) ^ l := by
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
    baseIntegerUnit_val, ← map_zpow₀, map_mul, map_pow, AlgHom.commutes]
  rw [← Algebra.smul_def]
  rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The fundamental polynomial of a stratum whose generator is the image of `β` is the reduced
characteristic polynomial of the integral unit `π^{n/g} β^{e/g}`. -/
theorem fundamentalPolynomial_eq_reduceIntegralPolynomial [FiniteDimensional F V]
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (S : Stratum 𝒪[F] F V) (hSc : S.chain = L)
    (hSn : S.n = n) (E : Type uE) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
    (β : Eˣ) (hβb : subfieldEmbedding F E V (β : E) = S.b) (π : RingPrimeElement 𝒪[F])
    (w : 𝒪ₑ[F,E]ˣ)
    (hw : baseIntegerUnit E π.2.1 ^ (n / (Nat.gcd L.period n.natAbs : ℤ)) *
      β ^ (L.period / Nat.gcd L.period n.natAbs) = subfieldIntegerUnits E w) :
    S.fundamentalPolynomial π =
      reduceIntegralPolynomial 𝒪[F] F (subfieldEmbedding F E V ((w : 𝒪ₑ[F,E]) : E)).charpoly := by
  subst hSc hSn
  have hfe : S.fundamentalElement π = subfieldEmbedding F E V ((w : 𝒪ₑ[F,E]) : E) := by
    have h1 : S.fundamentalElement π =
        (algebraMap 𝒪[F] F π.1 ^ (S.n / (Nat.gcd S.chain.period S.n.natAbs : ℤ))) •
          S.b ^ (S.chain.period / Nat.gcd S.chain.period S.n.natAbs) := rfl
    have h2 := subfieldEmbedding_baseIntegerUnit_zpow_mul (V := V) E β π.2.1
      (S.n / (Nat.gcd S.chain.period S.n.natAbs : ℤ))
      (S.chain.period / Nat.gcd S.chain.period S.n.natAbs)
    rw [hw, hβb] at h2
    rw [h1, ← h2]
    rfl
  unfold Stratum.fundamentalPolynomial
  rw [hfe]

/-- A simple stratum at depth `n − 1` gives a field `F[b]` normalizing the chain, in which `b`
is a minimal unit of shift `-n`. -/
theorem exists_simpleStratum_minimal [FiniteDimensional F V] (L : LatticeChain 𝒪[F] F V) (n : ℤ)
    (S : Stratum 𝒪[F] F V) (hSc : S.chain = L) (hSn : S.n = n) (hSr : S.r = n - 1)
    (hS : S.IsSimple) :
    ∃ hF : IsField (elementAlgebra S.b),
      letI := hF.toField
      ∃ (hE : ∀ a : (elementAlgebra S.b)ˣ, subfieldUnits F (elementAlgebra S.b) V a ∈ L.stabilizer)
        (β : (elementAlgebra S.b)ˣ),
        (L.fieldShift (elementAlgebra S.b) hE β).toAdd = -n ∧
        IsMinimalOver F (elementAlgebra S.b) (β : elementAlgebra S.b) ∧
        subfieldEmbedding F (elementAlgebra S.b) V (β : elementAlgebra S.b) = S.b := by
  obtain ⟨⟨hF, hE⟩, hv⟩ := hS.1
  subst hSc hSn
  let := hF.toField
  have : FiniteDimensional F (elementAlgebra S.b) := S.chain.finiteDimensional_subfield _
  let β : elementAlgebra S.b := ⟨S.b, Algebra.self_mem_adjoin_singleton F S.b⟩
  have hβ : subfieldEmbedding F (elementAlgebra S.b) V β = S.b := by
    ext v
    rfl
  have hβ0 : β ≠ 0 := by
    intro h
    have h' : S.b = 0 := congrArg Subtype.val h
    rw [h', S.chain.valuation_zero, ← WithTop.LinearOrderedAddCommGroup.coe_neg] at hv
    exact WithTop.top_ne_coe hv
  let u : (elementAlgebra S.b)ˣ := Units.mk0 β hβ0
  have hshift : (S.chain.fieldShift (elementAlgebra S.b) hE u).toAdd = -S.n := by
    have h := S.chain.valuation_eq_shift ⟨subfieldUnits F (elementAlgebra S.b) V u, hE u⟩
    change S.chain.valuation (subfieldEmbedding F (elementAlgebra S.b) V β) = _ at h
    rw [hβ, hv] at h
    change S.chain.stabilizerValuation ⟨subfieldUnits F (elementAlgebra S.b) V u, hE u⟩ = -S.n
    exact_mod_cast h.symm
  refine ⟨hF, hE, u, hshift, ?_, hβ⟩
  have hgen := adjoin_elementAlgebra_generator S.b
  have hval : S.chain.valuation
      (subfieldEmbedding F (elementAlgebra S.b) V (u : elementAlgebra S.b)) =
      ((-S.n : ℤ) : WithTop ℤ) := by
    change S.chain.valuation (subfieldEmbedding F (elementAlgebra S.b) V β) = _
    rw [hβ, hv, WithTop.LinearOrderedAddCommGroup.coe_neg]
  have hcrit : criticalExponent S.chain
      (subfieldEmbedding F (elementAlgebra S.b) V (u : elementAlgebra S.b)) <
        ((1 - S.n : ℤ) : WithBot ℤ) := by
    have h := hS.2
    change criticalExponent S.chain (subfieldEmbedding F (elementAlgebra S.b) V β) < _
    rw [hβ, show (1 - S.n : ℤ) = -S.r by rw [hSr]; ring]
    exact h
  exact S.chain.isMinimalOver_of_criticalExponent_lt _ hE u hgen hval hcrit

end Setup

/-- **Bushnell–Kutzko (1994), (1.4)–(1.5), for principal orders.** At depth `n − 1` the
fundamental polynomial of a simple stratum is a positive power of a monic irreducible
`f ≠ X` of degree dividing `N / e`, the residue degree of `F[b]` is `deg f` and its
ramification index is `e / gcd(e, n)`; equal factors give `U(𝔄)`-conjugacy up to
equivalence. -/
theorem minimalSimpleStratumPolynomial : MinimalSimpleStratumPolynomialStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ _ L n π hL hn SimpleStrata ResiduePolynomial
  have hπ : Irreducible π.1 :=
    (irreducible_iff_uniformizer π.1).mpr (π.2.2.trans (ringJacobson_eq_maximalIdeal _)).symm
  let ι : ResidueField 𝒪[F] →+* 𝒪[F] ⧸ Ring.jacobson 𝒪[F] := residueJacobsonEquiv 𝒪[F]
  have hι : Function.Injective ι := (residueJacobsonEquiv 𝒪[F]).injective
  refine ⟨fun S => ?_, fun S T f a b hfm hfi ha hb hS hT => ?_⟩
  · obtain ⟨S, hSc, hSn, hSr, hSs⟩ := S
    obtain ⟨hF, hE, β, hshift, hmin, hβb⟩ := exists_simpleStratum_minimal L n S hSc hSn hSr hSs
    let := hF.toField
    have : FiniteDimensional F (elementAlgebra S.b) := L.finiteDimensional_subfield _
    have := subfieldIntegers_isLocalHom F (elementAlgebra S.b)
    obtain ⟨w, hw⟩ := L.exists_integerUnit_of_fieldShift_zero _ hE
      (L.fieldShift_fundamentalUnit _ hE β hshift hπ)
    obtain ⟨hint, m, hm, hred⟩ := L.reduceIntegralPolynomial_charpoly_eq_minpoly_pow _ hE w
    obtain ⟨hram, hgen⟩ :=
      L.ramificationIndex_and_residue_adjoin_of_isMinimalOver _ hE β hshift hmin hπ w hw
    have hdeg := natDegree_minpoly_eq_finrank_of_adjoin_eq_top (elementAlgebra S.b) _ hint hgen
    have hres := subfieldResidueDegree_eq_finrank (F := F) (elementAlgebra S.b)
    have hdvd := L.finrank_residueField_dvd_of_isPrincipal hL (elementAlgebra S.b) hE
    have hfund : S.fundamentalPolynomial π =
        ((minpoly (ResidueField 𝒪[F])
          (residue 𝒪ₑ[F, elementAlgebra S.b] (w : 𝒪ₑ[F, elementAlgebra S.b]))).map ι) ^ m :=
      (fundamentalPolynomial_eq_reduceIntegralPolynomial L n S hSc hSn _ β hβb π w hw).trans hred
    refine ⟨(minpoly (ResidueField 𝒪[F])
      (residue 𝒪ₑ[F, elementAlgebra S.b] (w : 𝒪ₑ[F, elementAlgebra S.b]))).map ι, m,
      (minpoly.monic hint).map _, ?_, ?_, hm, hfund, ?_, ?_, ?_⟩
    · change Irreducible (Polynomial.mapEquiv (residueJacobsonEquiv 𝒪[F]) _)
      rw [MulEquiv.irreducible_iff]
      exact minpoly.irreducible hint
    · intro hX
      have h0 : minpoly (ResidueField 𝒪[F])
          (residue 𝒪ₑ[F, elementAlgebra S.b] (w : 𝒪ₑ[F, elementAlgebra S.b])) = X :=
        Polynomial.map_injective ι hι (by rw [hX, Polynomial.map_X])
      have h1 := minpoly.aeval (ResidueField 𝒪[F])
        (residue 𝒪ₑ[F, elementAlgebra S.b] (w : 𝒪ₑ[F, elementAlgebra S.b]))
      rw [h0, aeval_X] at h1
      exact (residue_ne_zero_iff_isUnit _).mpr w.isUnit h1
    · rw [Polynomial.natDegree_map_eq_of_injective hι, hdeg]
      exact hdvd
    · change elementResidueDegree F S.b = _
      unfold elementResidueDegree
      rw [dite_eq_left hF, Polynomial.natDegree_map_eq_of_injective hι, hdeg]
      exact hres
    · change elementRamificationIndex F S.b = _
      unfold elementRamificationIndex
      rw [dite_eq_left hF]
      exact hram
  · obtain ⟨S, hSc, hSn, hSr, hSs⟩ := S
    obtain ⟨T, hTc, hTn, hTr, hTs⟩ := T
    obtain ⟨hF₁, hE₁, β₁, hshift₁, hmin₁, hβb₁⟩ :=
      exists_simpleStratum_minimal L n S hSc hSn hSr hSs
    obtain ⟨hF₂, hE₂, β₂, hshift₂, hmin₂, hβb₂⟩ :=
      exists_simpleStratum_minimal L n T hTc hTn hTr hTs
    let := hF₁.toField
    let := hF₂.toField
    have : FiniteDimensional F (elementAlgebra S.b) := L.finiteDimensional_subfield _
    have : FiniteDimensional F (elementAlgebra T.b) := L.finiteDimensional_subfield _
    have := subfieldIntegers_isLocalHom F (elementAlgebra S.b)
    have := subfieldIntegers_isLocalHom F (elementAlgebra T.b)
    obtain ⟨w₁, hw₁⟩ := L.exists_integerUnit_of_fieldShift_zero _ hE₁
      (L.fieldShift_fundamentalUnit _ hE₁ β₁ hshift₁ hπ)
    obtain ⟨w₂, hw₂⟩ := L.exists_integerUnit_of_fieldShift_zero _ hE₂
      (L.fieldShift_fundamentalUnit _ hE₂ β₂ hshift₂ hπ)
    obtain ⟨hint₁, m₁, hm₁, hred₁⟩ := L.reduceIntegralPolynomial_charpoly_eq_minpoly_pow _ hE₁ w₁
    obtain ⟨hint₂, m₂, hm₂, hred₂⟩ := L.reduceIntegralPolynomial_charpoly_eq_minpoly_pow _ hE₂ w₂
    have hfund₁ : S.fundamentalPolynomial π =
        ((minpoly (ResidueField 𝒪[F])
          (residue 𝒪ₑ[F, elementAlgebra S.b] (w₁ : 𝒪ₑ[F, elementAlgebra S.b]))).map ι) ^ m₁ :=
      (fundamentalPolynomial_eq_reduceIntegralPolynomial L n S hSc hSn _ β₁ hβb₁ π w₁ hw₁).trans
        hred₁
    have hfund₂ : T.fundamentalPolynomial π =
        ((minpoly (ResidueField 𝒪[F])
          (residue 𝒪ₑ[F, elementAlgebra T.b] (w₂ : 𝒪ₑ[F, elementAlgebra T.b]))).map ι) ^ m₂ :=
      (fundamentalPolynomial_eq_reduceIntegralPolynomial L n T hTc hTn _ β₂ hβb₂ π w₂ hw₂).trans
        hred₂
    have : (Ring.jacobson 𝒪[F]).IsMaximal := by
      rw [ringJacobson_eq_maximalIdeal]
      infer_instance
    let : Field (𝒪[F] ⧸ Ring.jacobson 𝒪[F]) := Ideal.Quotient.field _
    have hirr {K : Type uV} [Field K] [Algebra (ResidueField 𝒪[F]) K] (c : K)
        (hc : IsIntegral (ResidueField 𝒪[F]) c) :
        Irreducible ((minpoly (ResidueField 𝒪[F]) c).map ι) := by
      change Irreducible (Polynomial.mapEquiv (residueJacobsonEquiv 𝒪[F]) _)
      rw [MulEquiv.irreducible_iff]
      exact minpoly.irreducible hc
    have hf₁ := eq_of_pow_eq_pow_of_irreducible hfm hfi ((minpoly.monic hint₁).map ι)
      (hirr _ hint₁) ha (hS.symm.trans hfund₁)
    have hf₂ := eq_of_pow_eq_pow_of_irreducible hfm hfi ((minpoly.monic hint₂).map ι)
      (hirr _ hint₂) hb (hT.symm.trans hfund₂)
    have hmin : minpoly (ResidueField 𝒪[F])
        (residue 𝒪ₑ[F, elementAlgebra S.b] (w₁ : 𝒪ₑ[F, elementAlgebra S.b])) =
        minpoly (ResidueField 𝒪[F])
          (residue 𝒪ₑ[F, elementAlgebra T.b] (w₂ : 𝒪ₑ[F, elementAlgebra T.b])) :=
      Polynomial.map_injective ι hι (hf₁.symm.trans hf₂)
    obtain ⟨u, hu, hconj⟩ := L.exists_unitFiltration_conj_of_minpoly_eq (elementAlgebra S.b) hE₁
      (elementAlgebra T.b) hE₂ β₁ β₂ hshift₁ hshift₂ hπ w₁ w₂ hw₁ hw₂ hint₁ hmin
    refine ⟨u, hu, ?_⟩
    rw [hβb₁, hβb₂] at hconj
    change _ - T.b ∈ T.chain.endFiltration (-T.r)
    rw [hTc, hTr, show -(n - 1) = 1 - n by ring]
    exact hconj

end Langlands.BushnellKutzko
