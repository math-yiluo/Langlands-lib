import Langlands.BushnellKutzko.NonmaximalSimpleTypeJacquetStatement
import Langlands.BushnellKutzko.PositiveDepthTypeHeckeInjectivityStatement
import Langlands.BushnellKutzko.TypeHeckeJacquet
import Langlands.BushnellKutzko.IdempotentAdaptedBasis
import Langlands.BushnellKutzko.RelativeSplittingIdempotent
import Langlands.BushnellKutzko.SimpleStratumLatticePropertiesProof
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesProof
import Langlands.BushnellKutzko.FundamentalStratumLevelCore
import Langlands.Representation.TensorProduct.MultiplicityCancellation
import Langlands.BushnellKutzko.IntertwiningTransport

/-! # Jacquet modules of non-maximal simple types of kind (a), from Hecke injectivity -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.PositiveDepthNonmaximalReduction

open BlockIdempotent RelSplitIdempotent

universe uF uρ uπ

section Idempotent

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uF} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

set_option linter.style.haveILetI false in
/-- **An idempotent of `𝔅` with off-diagonal corners in `𝔓`.** For a simple stratum whose
centralizer chain has period at least two there is an idempotent `ε` of `𝔄` commuting with
`β`, different from `0` and `1`, such that `ε x (1 - ε)` and `(1 - ε) x ε` lie in
`𝔓 = End^1(𝓛)` for every `x ∈ 𝔄`. -/
theorem exists_blockIdempotent (S : Stratum 𝒪[F] F V) (hS : S.IsSimple)
    (hp : letI := hS.1.1.fst.toField
      haveI : FiniteDimensional F (elementAlgebra S.b) :=
        S.chain.finiteDimensional_subfield (elementAlgebra S.b)
      haveI := subfieldIntegers_isDiscreteValuationRing F (elementAlgebra S.b)
      2 ≤ (S.chain.subfieldChain (elementAlgebra S.b) hS.1.1.snd).period) :
    ∃ ε : Module.End F V, IsIdempotentElem ε ∧ ε ∈ S.chain.order ∧ ε * S.b = S.b * ε ∧
      (∀ x ∈ S.chain.order, ε * x * (1 - ε) ∈ S.chain.endFiltration 1 ∧
        (1 - ε) * x * ε ∈ S.chain.endFiltration 1) ∧ ε ≠ 0 ∧ ε ≠ 1 := by
  letI := hS.1.1.fst.toField
  haveI : FiniteDimensional F (elementAlgebra S.b) :=
    S.chain.finiteDimensional_subfield (elementAlgebra S.b)
  haveI := subfieldIntegers_isDiscreteValuationRing F (elementAlgebra S.b)
  haveI := subfieldIntegers_isFractionRing F (elementAlgebra S.b)
  let E := elementAlgebra S.b
  have hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ S.chain.stabilizer := hS.1.1.snd
  obtain ⟨πF, hπF⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨m, w, hw⟩ := exists_relSplits_basis (L := E) S.chain hπF hE
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  have hperiod := S.chain.subfieldChain_period_eq_shift E hE hϖ
  have hp2 : 2 ≤ uniformizerShift (𝓛 := S.chain) hE hϖ := by
    change (2 : ℤ) ≤ (S.chain.fieldShift E hE (subfieldIntegerUnit E hϖ.ne_zero)).toAdd
    rw [← hperiod]
    exact_mod_cast hp
  have hpos : 0 < uniformizerShift (𝓛 := S.chain) hE hϖ := by omega
  refine ⟨blockIdempotent S.chain w, isIdempotentElem S.chain w,
    blockIdempotent_mem_order hw, ?_, fun x hx => offDiagonal_mem hϖ hw hpos hx,
    blockIdempotent_ne_zero (hE := hE) hϖ hw, blockIdempotent_ne_one hϖ hw hp2⟩
  ext v
  change blockIdempotent S.chain w (S.b v) = S.b (blockIdempotent S.chain w v)
  have h := blockIdempotent_smul S.chain w (⟨S.b, Algebra.self_mem_adjoin_singleton F S.b⟩ : E) v
  exact h

end Idempotent

section Helpers

/-- Coinvariants along a smaller subgroup surject onto those along a larger one. -/
theorem not_subsingleton_coinvariants_of_le {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ G V) {N N' : Subgroup G} (hle : N' ≤ N)
    (h : ¬ Subsingleton (Jacquet.Coinvariants π N)) : ¬ Subsingleton (Jacquet.Coinvariants π N') := by
  intro hs
  apply h
  refine ⟨fun x y => ?_⟩
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective π N x
  obtain ⟨w, rfl⟩ := Jacquet.mk_surjective π N y
  have hrel : Jacquet.relations π N' ≤ Jacquet.relations π N := by
    rw [Jacquet.relations_eq_span, Jacquet.relations_eq_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨⟨n, u⟩, rfl⟩
    exact ⟨(⟨n.val, hle n.property⟩, u), rfl⟩
  have hv : v ∈ Jacquet.relations π N :=
    hrel ((Jacquet.mk_eq_zero π N' v).mp (Subsingleton.elim _ _))
  have hw : w ∈ Jacquet.relations π N :=
    hrel ((Jacquet.mk_eq_zero π N' w).mp (Subsingleton.elim _ _))
  rw [(Jacquet.mk_eq_zero π N v).mpr hv, (Jacquet.mk_eq_zero π N w).mpr hw]

/-- Conjugation by a unit commuting with `e` maps the unipotent radical of `e` into itself. -/
theorem conj_mem_upperGroup_of_comm {A : Type*} [Ring A] {e : A} {z g : Aˣ}
    (hz : (z : A) * e = e * z) (hg : g ∈ upperGroup e) : z * g * z⁻¹ ∈ upperGroup e := by
  obtain ⟨h1, h2⟩ := hg
  have hzi : ((z⁻¹ : Aˣ) : A) * e = e * ((z⁻¹ : Aˣ) : A) := (leviGroup e).inv_mem hz
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, mul_assoc, hzi, ← mul_assoc, mul_assoc (z : A), h1, hz,
      mul_assoc, Units.mul_inv, mul_one]
  · have hz' : (z : A) * (1 - e) = (1 - e) * z := by rw [mul_sub, sub_mul, mul_one, one_mul, hz]
    rw [Units.val_mul, Units.val_mul, ← mul_assoc, ← mul_assoc, ← hz', mul_assoc (z : A), h2,
      hz', mul_assoc, Units.mul_inv, mul_one]

end Helpers

section AutSide

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uF} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- The `𝔬_F`-subalgebra `𝔍(β, 𝔄)` and the descriptions of `J` and `J^1` by it. -/
theorem exists_jAlgebra (S : Stratum 𝒪[F] F V) (hr : S.r = 0) (hS : S.IsSimple)
    (q : S.DefiningSequenceChoice) :
    ∃ R : Subalgebra 𝒪[F] A,
      (∀ x ∈ R, x ∈ S.chain.order) ∧
      Submodule.span F (R : Set A) = ⊤ ∧
      (∀ x ∈ centralizerLattice S.chain S.b 0, x ∈ R) ∧
      (∀ g : G, g ∈ simpleJ S.chain S.n S.b q.tail ↔
        g ∈ S.chain.unitFiltration 0 ∧ (g : A) ∈ R) ∧
      (∀ g : G, g ∈ simpleJGroup S.chain S.n S.b q.tail 1 ↔
        g ∈ S.chain.unitFiltration 1 ∧ (g : A) ∈ R) := by
  obtain ⟨-, ⟨-, hJlat, -, ⟨R, hR⟩, hQH, hHJ, hJO, -⟩, -⟩ :=
    simpleStratumLatticeProperties F V S hr hS q
  obtain ⟨hcarrier, -⟩ := simpleStratumGroupProperties F V S hr hS q
  refine ⟨R, fun x hx => ?_, ?_, fun x hx => ?_, fun g => ?_, fun g => ?_⟩
  · have hx' : x ∈ simpleJLattice S.chain S.n S.b q.tail := by rw [← hR]; exact hx
    exact hJO hx'
  · have := hJlat.span_eq_top
    rw [← hR] at this
    exact this
  · have hx' : x ∈ simpleJLattice S.chain S.n S.b q.tail := hHJ (hQH hx)
    rw [← hR] at hx'
    exact hx'
  · have h := (hcarrier 0).2
    change g ∈ (simpleJGroup S.chain S.n S.b q.tail 0 : Set G) ↔ _
    rw [h]
    change g ∈ S.chain.unitFiltration 0 ∧ (g : A) ∈ simpleJLattice S.chain S.n S.b q.tail ↔ _
    rw [← hR]
    rfl
  · have h := (hcarrier 1).2
    change g ∈ (simpleJGroup S.chain S.n S.b q.tail 1 : Set G) ↔ _
    rw [h]
    change g ∈ S.chain.unitFiltration 1 ∧ (g : A) ∈ simpleJLattice S.chain S.n S.b q.tail ↔ _
    rw [← hR]
    rfl


end AutSide

section ContractionAlg

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uF} [AddCommGroup V] [Module F V]

/-- The contraction `ζ = ϖ_F ε + (1 - ε)` attached to an idempotent `ε` and a uniformizer. -/
def zeta {ε : Module.End F V} (he : IsIdempotentElem ε) {πF : 𝒪[F]} (hπF : Irreducible πF) :
    (Module.End F V)ˣ :=
  contraction he (scalarUnit (πF : F) (coe_uniformizer_ne_zero hπF)) (scalarUnit_comm _ _)

theorem val_zeta {ε : Module.End F V} (he : IsIdempotentElem ε) {πF : 𝒪[F]}
    (hπF : Irreducible πF) :
    ((zeta he hπF : (Module.End F V)ˣ) : Module.End F V) =
      algebraMap F (Module.End F V) (πF : F) * ε + (1 - ε) := rfl

theorem scalar_pow_mul {πF : 𝒪[F]} (hπF : Irreducible πF) (r : ℕ) (y : Module.End F V) :
    ((scalarUnit (V := V) (πF : F) (coe_uniformizer_ne_zero hπF) : (Module.End F V)ˣ) :
      Module.End F V) ^ r * y = ((πF : F) ^ r) • y := by
  rw [val_scalarUnit, ← map_pow, ← Algebra.smul_def]

theorem scalar_pow_mem {πF : 𝒪[F]} (hπF : Irreducible πF) (Rj : Subalgebra 𝒪[F] (Module.End F V))
    (r : ℕ) :
    ((scalarUnit (V := V) (πF : F) (coe_uniformizer_ne_zero hπF) : (Module.End F V)ˣ) :
      Module.End F V) ^ r ∈ Rj := by
  have h := Rj.algebraMap_mem πF
  rw [IsScalarTower.algebraMap_apply 𝒪[F] F (Module.End F V)] at h
  rw [val_scalarUnit]
  exact pow_mem h r

theorem zeta_mem_leviGroup {ε : Module.End F V} (he : IsIdempotentElem ε) {πF : 𝒪[F]}
    (hπF : Irreducible πF) : zeta he hπF ∈ leviGroup ε := by
  rw [mem_leviGroup, val_zeta he hπF]
  rw [add_mul, mul_add, mul_assoc, he.eq, ← mul_assoc, ← Algebra.commutes, mul_assoc, he.eq,
    sub_mul, mul_sub, one_mul, mul_one, he.eq]

theorem zeta_mem_centralizer {ε : Module.End F V} (he : IsIdempotentElem ε) {πF : 𝒪[F]}
    (hπF : Irreducible πF) {β : Module.End F V} (hεb : ε * β = β * ε) :
    zeta he hπF ∈ centralizerUnitGroup β := by
  change β * ((zeta he hπF : (Module.End F V)ˣ) : Module.End F V) =
    ((zeta he hπF : (Module.End F V)ˣ) : Module.End F V) * β
  rw [val_zeta he hπF, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, ← mul_assoc,
    ← Algebra.commutes, mul_assoc, ← hεb, mul_assoc]

theorem pow_conj_upper_mem {ε : Module.End F V} (he : IsIdempotentElem ε) {πF : 𝒪[F]}
    (hπF : Irreducible πF) (L : LatticeChain 𝒪[F] F V) (Rj : Subalgebra 𝒪[F] (Module.End F V))
    (Jg : Subgroup (Module.End F V)ˣ)
    (hJ : ∀ g : (Module.End F V)ˣ, g ∈ Jg ↔ g ∈ L.unitFiltration 0 ∧ (g : Module.End F V) ∈ Rj)
    (hRL : ∀ x ∈ Rj, x ∈ L.order) (r : ℕ) {u : (Module.End F V)ˣ}
    (hu : u ∈ Jg ⊓ upperGroup ε) :
    zeta he hπF ^ r * u * (zeta he hπF ^ r)⁻¹ ∈ Jg ⊓ upperGroup ε := by
  have hz : zeta he hπF = contraction he (scalarUnit (V := V) (πF : F)
      (coe_uniformizer_ne_zero hπF)) (scalarUnit_comm _ _) := rfl
  obtain ⟨hmem, hval⟩ := pow_conj_upper he _ (scalarUnit_comm (πF : F)
    (coe_uniformizer_ne_zero hπF)) r hu.2
  refine ⟨mem_of_mem_upperGroup L Rj Jg hJ hRL hmem ?_, hmem⟩
  rw [hz, hval, add_sub_cancel_left]
  exact mul_mem (scalar_pow_mem hπF Rj r) (sub_mem ((hJ u).mp hu.1).2 (one_mem _))

theorem pow_conj_lower_mem {ε : Module.End F V} (he : IsIdempotentElem ε) {πF : 𝒪[F]}
    (hπF : Irreducible πF) (L : LatticeChain 𝒪[F] F V) (Rj : Subalgebra 𝒪[F] (Module.End F V))
    (Jg : Subgroup (Module.End F V)ˣ)
    (hJ : ∀ g : (Module.End F V)ˣ, g ∈ Jg ↔ g ∈ L.unitFiltration 0 ∧ (g : Module.End F V) ∈ Rj)
    (hRL : ∀ x ∈ Rj, x ∈ L.order) (r : ℕ) {l : (Module.End F V)ˣ}
    (hl : l ∈ Jg ⊓ lowerGroup ε) :
    (zeta he hπF ^ r)⁻¹ * l * zeta he hπF ^ r ∈ Jg ⊓ lowerGroup ε := by
  have hz : zeta he hπF = contraction he (scalarUnit (V := V) (πF : F)
      (coe_uniformizer_ne_zero hπF)) (scalarUnit_comm _ _) := rfl
  obtain ⟨hmem, hval⟩ := pow_conj_lower he _ (scalarUnit_comm (πF : F)
    (coe_uniformizer_ne_zero hπF)) r hl.2
  refine ⟨mem_of_mem_upperGroup L Rj Jg hJ hRL hmem ?_, hmem⟩
  rw [hz, hval, add_sub_cancel_left]
  exact mul_mem (scalar_pow_mem hπF Rj r) (sub_mem ((hJ l).mp hl.1).2 (one_mem _))

end ContractionAlg

section ContractionLocal

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uF} [AddCommGroup V] [Module F V]

theorem exists_pow_conj_mem {ε : Module.End F V} (he : IsIdempotentElem ε) {πF : 𝒪[F]}
    (hπF : Irreducible πF) (L : LatticeChain 𝒪[F] F V) (Rj : Subalgebra 𝒪[F] (Module.End F V))
    (Jg : Subgroup (Module.End F V)ˣ)
    (hJ : ∀ g : (Module.End F V)ˣ, g ∈ Jg ↔ g ∈ L.unitFiltration 0 ∧ (g : Module.End F V) ∈ Rj)
    (hRL : ∀ x ∈ Rj, x ∈ L.order) (hspan : Submodule.span F (Rj : Set (Module.End F V)) = ⊤)
    {x : (Module.End F V)ˣ} (hx : x ∈ upperGroup ε) :
    ∃ r : ℕ, zeta he hπF ^ r * x * (zeta he hπF ^ r)⁻¹ ∈ Jg := by
  obtain ⟨r, hr⟩ := exists_pow_smul_mem hπF (Subalgebra.toSubmodule Rj) hspan ((x : _) - 1)
  refine ⟨r, ?_⟩
  have hz : zeta he hπF = contraction he (scalarUnit (V := V) (πF : F)
      (coe_uniformizer_ne_zero hπF)) (scalarUnit_comm _ _) := rfl
  obtain ⟨hmem, hval⟩ := pow_conj_upper he _ (scalarUnit_comm (πF : F)
    (coe_uniformizer_ne_zero hπF)) r hx
  refine mem_of_mem_upperGroup L Rj Jg hJ hRL hmem ?_
  rw [hz, hval, add_sub_cancel_left, scalar_pow_mul hπF]
  exact hr

end ContractionLocal


section SigmaInvariance

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uF} [AddCommGroup V] [Module F V]

/-- Let `σ` be a representation of `J` trivial on `J^1`. Then conjugation by a power of the
contraction does not change `σ` on `J ∩ ζ^{-r} J ζ^r`: the identity map intertwines `σ` at
`ζ^r`. -/
theorem sigma_conj_eq {ε : Module.End F V} (he : IsIdempotentElem ε) {πF : 𝒪[F]}
    (hπF : Irreducible πF) (L : LatticeChain 𝒪[F] F V) (Rj : Subalgebra 𝒪[F] (Module.End F V))
    (Jg Jg1 : Subgroup (Module.End F V)ˣ)
    (hJ : ∀ g : (Module.End F V)ˣ, g ∈ Jg ↔ g ∈ L.unitFiltration 0 ∧ (g : Module.End F V) ∈ Rj)
    (hJ1 : ∀ g : (Module.End F V)ˣ, g ∈ Jg1 ↔ g ∈ L.unitFiltration 1 ∧
      (g : Module.End F V) ∈ Rj)
    (hRL : ∀ x ∈ Rj, x ∈ L.order) (heR : ε ∈ Rj)
    (hoff : ∀ x ∈ L.order, ε * x * (1 - ε) ∈ L.endFiltration 1 ∧
      (1 - ε) * x * ε ∈ L.endFiltration 1)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] (σ : Representation ℂ Jg Wσ)
    (hσ : ∀ j : Jg, (j : (Module.End F V)ˣ) ∈ Jg1 → σ j = 1) (r : ℕ) (j : Jg)
    (hj : zeta he hπF ^ r * (j : (Module.End F V)ˣ) * (zeta he hπF ^ r)⁻¹ ∈ Jg) :
    σ ⟨_, hj⟩ = σ j := by
  set x := zeta he hπF ^ r with hxdef
  obtain ⟨u, hu, m, hm, l, hl, hjuml⟩ :=
    exists_factor L Rj Jg hJ hRL he heR hoff (j : (Module.End F V)ˣ) j.property
  have hxm : x * m = m * x := by
    have h1 : zeta he hπF * m = m * zeta he hπF :=
      contraction_comm_levi he _ (scalarUnit_comm (πF : F) (coe_uniformizer_ne_zero hπF)) hm.2
    exact (Commute.pow_left h1 r)
  have hxu := pow_conj_upper_mem he hπF L Rj Jg hJ hRL r hu
  have hxε : ((x : (Module.End F V)ˣ) : Module.End F V) * (1 - ε) =
      (1 - ε) * ((x : (Module.End F V)ˣ) : Module.End F V) := by
    have h0 : x ∈ leviGroup ε := pow_mem (zeta_mem_leviGroup he hπF) r
    rw [mem_leviGroup] at h0
    rw [mul_sub, sub_mul, mul_one, one_mul, h0]
  have hxl_low : x * l * x⁻¹ ∈ lowerGroup ε := conj_mem_upperGroup_of_comm hxε hl.2
  have hconj : x * (j : (Module.End F V)ˣ) * x⁻¹ = (x * u * x⁻¹) * m * (x * l * x⁻¹) := by
    rw [hjuml]
    calc x * (u * m * l) * x⁻¹ = (x * u * x⁻¹) * (x * m) * l * x⁻¹ := by group
      _ = (x * u * x⁻¹) * (m * x) * l * x⁻¹ := by rw [hxm]
      _ = (x * u * x⁻¹) * m * (x * l * x⁻¹) := by group
  have hxl_J : x * l * x⁻¹ ∈ Jg := by
    have : x * l * x⁻¹ = m⁻¹ * (x * u * x⁻¹)⁻¹ * (x * (j : (Module.End F V)ˣ) * x⁻¹) := by
      rw [hconj]; group
    rw [this]
    exact Jg.mul_mem (Jg.mul_mem (Jg.inv_mem hm.1) (Jg.inv_mem hxu.1)) hj
  have hoff' : ∀ y ∈ L.order, ε * y * (1 - ε) ∈ L.endFiltration 1 := fun y hy => (hoff y hy).1
  have hoff'' : ∀ y ∈ L.order, (1 - ε) * y * (1 - (1 - ε)) ∈ L.endFiltration 1 := by
    intro y hy
    rw [sub_sub_cancel]
    exact (hoff y hy).2
  have hJ1u : ∀ k ∈ Jg ⊓ upperGroup ε, k ∈ Jg1 := fun k hk =>
    (hJ1 k).mpr ⟨mem_unitFiltration_one_of_mem_upperGroup L Rj Jg hJ he hoff' hk.1 hk.2,
      ((hJ k).mp hk.1).2⟩
  have hJ1l : ∀ k ∈ Jg ⊓ lowerGroup ε, k ∈ Jg1 := fun k hk =>
    (hJ1 k).mpr ⟨mem_unitFiltration_one_of_mem_upperGroup L Rj Jg hJ he.one_sub hoff'' hk.1
      hk.2, ((hJ k).mp hk.1).2⟩
  have e1 : (⟨_, hj⟩ : Jg) = ⟨_, hxu.1⟩ * ⟨m, hm.1⟩ * ⟨_, hxl_J⟩ := Subtype.ext hconj
  have e2 : j = ⟨u, hu.1⟩ * ⟨m, hm.1⟩ * ⟨l, hl.1⟩ := Subtype.ext hjuml
  rw [e1, e2, map_mul, map_mul, map_mul, map_mul, hσ ⟨_, hxu.1⟩ (hJ1u _ hxu),
    hσ ⟨_, hxl_J⟩ (hJ1l _ ⟨hxl_J, hxl_low⟩), hσ ⟨u, hu.1⟩ (hJ1u _ hu),
    hσ ⟨l, hl.1⟩ (hJ1l _ hl), one_mul, mul_one]

end SigmaInvariance

section TensorIntertwining

/-- If `x` intertwines `κ` and the identity intertwines `σ` at `x`, then `x` intertwines
`κ ⊗ σ`. -/
theorem intertwines_tprod {G : Type*} [Group G] {J : Subgroup G} {W₁ W₂ : Type*}
    [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] [Nontrivial W₂]
    (κ : Representation ℂ J W₁) (σ : Representation ℂ J W₂) (x : G)
    (hκ : Intertwines κ κ x)
    (hσ : ∀ (j : J) (hj : x * (j : G) * x⁻¹ ∈ J), σ ⟨_, hj⟩ = σ j) :
    Intertwines (κ.tprod σ) (κ.tprod σ) x := by
  obtain ⟨f, hf, h⟩ := (selfIntertwines_iff κ x).1 hκ
  refine (selfIntertwines_iff (κ.tprod σ) x).2 ⟨TensorProduct.map f LinearMap.id, ?_, ?_⟩
  · intro h0
    obtain ⟨a, ha⟩ : ∃ a, f a ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hf (LinearMap.ext hall)
    obtain ⟨b, hb⟩ := exists_ne (0 : W₂)
    have := LinearMap.congr_fun h0 (a ⊗ₜ[ℂ] b)
    rw [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.zero_apply] at this
    exact TensorMultiplicity.tmul_ne_zero ha hb this
  · intro j hj v
    induction v using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [Representation.tprod_apply, TensorProduct.map_tmul, LinearMap.id_apply]
      rw [h j hj a, hσ j hj]
    | add v w hv hw => rw [map_add, map_add, hv, hw, ← map_add, ← map_add]

end TensorIntertwining

section Main

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

/-- **Nonzero Jacquet modules for non-maximal simple types of kind (a), from Hecke
injectivity.** For a simple type `(J, ρ)` of kind (a) with `e(𝔅_β | 𝔬_E) ≥ 2`, a smooth
representation `π` containing `ρ` has a nonzero Jacquet module along a conjugate of the unipotent
radical of a proper two-block parabolic, provided the Hecke operators of `(J, ρ)` at elements of
`B_β^×` with nonzero intertwiners are injective on `Hom_J(ρ, π)`. -/
theorem not_subsingleton_jacquet_of_heckeInjective {ψF : AddChar F ℂ}
    {J : Subgroup (GeneralLinear n F)} (ρ : SmoothRep.{0, uF, uρ} ℂ J)
    {S : Stratum 𝒪[F] F (Fin n → F)} {q : S.DefiningSequenceChoice} {e : ℕ}
    (hdata : IsSimpleTypeData (W := (ρ : Type uρ)) ψF S q e (glRepresentationToAut ρ))
    (he2 : 2 ≤ e) (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F))
    (hH : ∀ x : GeneralLinear n F, Matrix.GeneralLinearGroup.toLin x ∈ centralizerUnitGroup S.b →
      ∀ Θ : intertwiningSpace ρ.representation ρ.representation x, Θ ≠ 0 →
      ∀ Φ : ρ.representation.IntertwiningMap (π.representation.comp J.subtype),
        typeHeckeMean ρ.representation π.representation x Θ.toLinearMap Φ.toLinearMap = 0 →
          Φ = 0)
    (hcont : ContainsType π ρ) :
    ∃ (B : GeneralLinear.BlockShape n) (g : GeneralLinear n F), B.parabolic F ≠ ⊤ ∧
      ¬ Subsingleton (Jacquet.Coinvariants π.representation (B.conjugateUnipotent g)) := by
  classical
  have hJco := (GLSimpleTypeData.positiveDepth S q e hdata).isCompact_isOpen
  obtain ⟨Φ, hΦ⟩ := hcont
  obtain ⟨-, hr0, -, hS, hrest⟩ := hdata
  obtain ⟨he, θ, -, dη, η, -, dκ, κ, hκ, f, d, σ₀, -, -, b, φ, -, dσ, σ, -, hσJ1, -, hpair⟩ :=
    hrest
  obtain ⟨-, ⟨L', m, hκtriv⟩, -, hκint⟩ := hκ
  obtain ⟨ε, hε, hεO, hεb, hoff, hε0, hε1⟩ := exists_blockIdempotent S hS (he ▸ he2)
  obtain ⟨Rj, hRL, hspan, hQR, hJ, hJ1⟩ := exists_jAlgebra S hr0 hS q
  have heR : ε ∈ Rj := by
    refine hQR ε ⟨(S.chain.mem_order_iff_mem_endFiltration).mp hεO, ?_⟩
    change (adjointMap 𝒪[F] S.b) ε = 0
    simp [adjointMap, hεb]
  obtain ⟨πF, hπF⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  let toL : GeneralLinear n F ≃* (Module.End F (Fin n → F))ˣ := Matrix.GeneralLinearGroup.toLin
  have hpair' := hpair
  obtain ⟨hJeq, ⟨Ψ⟩⟩ := hpair
  have hmemJ : ∀ g, g ∈ J ↔ toL g ∈ (simpleJ S.chain S.n S.b q.tail) := fun g => by
    rw [← hJeq]
    exact (Subgroup.mem_map_iff_mem (f := toL.toMonoidHom) toL.injective).symm
  let U : Subgroup (GeneralLinear n F) := (upperGroup ε).comap toL.toMonoidHom
  let M : Subgroup (GeneralLinear n F) := (leviGroup ε).comap toL.toMonoidHom
  let Ubar : Subgroup (GeneralLinear n F) := (lowerGroup ε).comap toL.toMonoidHom
  set ζA := zeta hε hπF with hζA
  let ζ : GeneralLinear n F := toL.symm ζA
  have htoLζ : ∀ r : ℕ, toL (ζ ^ r) = ζA ^ r := fun r => by
    rw [map_pow, MulEquiv.apply_symm_apply]
  have htoL_conj : ∀ (r : ℕ) (x : GeneralLinear n F),
      toL (ζ ^ r * x * (ζ ^ r)⁻¹) = ζA ^ r * toL x * (ζA ^ r)⁻¹ := by
    intro r x
    rw [map_mul, map_mul, map_inv, htoLζ]
  have htoL_conj' : ∀ (r : ℕ) (x : GeneralLinear n F),
      toL ((ζ ^ r)⁻¹ * x * ζ ^ r) = (ζA ^ r)⁻¹ * toL x * ζA ^ r := by
    intro r x
    rw [map_mul, map_mul, map_inv, htoLζ]
  -- the contraction on the matrix side
  have hcontr : TypeHeckeJacquet.IsHeckeContraction J U M Ubar ζ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      obtain ⟨u, hu, m', hm', l, hl, hjeq⟩ :=
        exists_factor S.chain Rj (simpleJ S.chain S.n S.b q.tail) hJ hRL hε heR hoff (toL j) ((hmemJ j).mp hj)
      refine ⟨toL.symm u, ⟨(hmemJ _).mpr ?_, ?_⟩, toL.symm m', ⟨(hmemJ _).mpr ?_, ?_⟩,
        toL.symm l, ⟨(hmemJ _).mpr ?_, ?_⟩, toL.injective ?_⟩
      · rw [MulEquiv.apply_symm_apply]; exact hu.1
      · change toL (toL.symm u) ∈ upperGroup ε
        rw [MulEquiv.apply_symm_apply]; exact hu.2
      · rw [MulEquiv.apply_symm_apply]; exact hm'.1
      · change toL (toL.symm m') ∈ leviGroup ε
        rw [MulEquiv.apply_symm_apply]; exact hm'.2
      · rw [MulEquiv.apply_symm_apply]; exact hl.1
      · change toL (toL.symm l) ∈ lowerGroup ε
        rw [MulEquiv.apply_symm_apply]; exact hl.2
      · rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
          MulEquiv.apply_symm_apply, hjeq]
    · rintro m' ⟨-, hm'⟩
      apply toL.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact contraction_comm_levi hε _ (scalarUnit_comm (πF : F)
        (coe_uniformizer_ne_zero hπF)) hm'
    · intro x hx
      change toL (ζ * x * ζ⁻¹) ∈ upperGroup ε
      rw [show ζ * x * ζ⁻¹ = ζ ^ 1 * x * (ζ ^ 1)⁻¹ by rw [pow_one], htoL_conj, pow_one]
      exact conj_mem_upperGroup_of_comm (zeta_mem_leviGroup hε hπF) hx
    · rintro u ⟨hu1, hu2⟩
      rw [hmemJ, show ζ * u * ζ⁻¹ = ζ ^ 1 * u * (ζ ^ 1)⁻¹ by rw [pow_one], htoL_conj]
      exact (pow_conj_upper_mem hε hπF S.chain Rj (simpleJ S.chain S.n S.b q.tail) hJ hRL 1 ⟨(hmemJ u).mp hu1, hu2⟩).1
    · rintro l ⟨hl1, hl2⟩
      have h := pow_conj_lower_mem hε hπF S.chain Rj (simpleJ S.chain S.n S.b q.tail) hJ hRL 1 ⟨(hmemJ l).mp hl1, hl2⟩
      rw [show ζ⁻¹ * l * ζ = (ζ ^ 1)⁻¹ * l * ζ ^ 1 by rw [pow_one]]
      refine ⟨(hmemJ _).mpr ?_, ?_⟩
      · rw [htoL_conj']; exact h.1
      · change toL ((ζ ^ 1)⁻¹ * l * ζ ^ 1) ∈ lowerGroup ε
        rw [htoL_conj']; exact h.2
    · intro x hx
      obtain ⟨r, hr⟩ := exists_pow_conj_mem hε hπF S.chain Rj (simpleJ S.chain S.n S.b q.tail) hJ hRL hspan hx
      exact ⟨r, (hmemJ _).mpr (by rw [htoL_conj]; exact hr)⟩
  -- the type is trivial on a small conjugate of `J ∩ U`
  obtain ⟨N, hN⟩ := LatticeChain.exists_endFiltration_le hπF L' S.chain m
  have hρk : ∀ (j : J) (v : (ρ : Type uρ)),
      Ψ (ρ.representation j v) = (κ.tprod σ) ⟨toL j, (hmemJ j).mp j.2⟩ (Ψ v) := by
    intro j v
    have h := Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap
      ⟨toL j, (hmemJ j).mp j.2⟩ v
    have hk : (MulEquiv.subgroupCongr hJeq).symm ⟨toL j, (hmemJ j).mp j.2⟩ =
        glSubgroupToAutEquiv J j := Subtype.ext rfl
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, hk,
      glRepresentationToAut_apply, Representation.Equiv.coe_toIntertwiningMap] at h
    exact h
  have hshrink : ∃ r₀ : ℕ, ∀ j : J,
      (∃ u ∈ J ⊓ U, (j : GeneralLinear n F) = ζ ^ r₀ * u * (ζ ^ r₀)⁻¹) →
        ρ.representation j = 1 := by
    refine ⟨N.toNat, fun j ⟨u, hu, hju⟩ => ?_⟩
    have huA : toL u ∈ (simpleJ S.chain S.n S.b q.tail) ⊓ upperGroup ε := ⟨(hmemJ u).mp hu.1, hu.2⟩
    have hjA : toL j = ζA ^ N.toNat * toL u * (ζA ^ N.toNat)⁻¹ := by rw [hju, htoL_conj]
    have hper : N ≤ (S.chain.period : ℤ) * N.toNat := by
      have h1 : (1 : ℤ) ≤ S.chain.period := by exact_mod_cast S.chain.period_pos
      have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
      nlinarith [Int.natCast_nonneg N.toNat]
    have hkL' := pow_conj_mem_unitFiltration S.chain Rj (simpleJ S.chain S.n S.b q.tail) hJ hπF hε
      (fun y hy => (hoff y hy).1) L' m N hN N.toNat hper huA
    have hk1 := pow_conj_upper_mem hε hπF S.chain Rj (simpleJ S.chain S.n S.b q.tail) hJ hRL N.toNat huA
    have hkJ1 : ζA ^ N.toNat * toL u * (ζA ^ N.toNat)⁻¹ ∈
        simpleJGroup S.chain S.n S.b q.tail 1 :=
      (hJ1 _).mpr ⟨mem_unitFiltration_one_of_mem_upperGroup S.chain Rj (simpleJ S.chain S.n S.b q.tail) hJ hε
        (fun y hy => (hoff y hy).1) hk1.1 hk1.2, ((hJ _).mp hk1.1).2⟩
    let k : (simpleJ S.chain S.n S.b q.tail) := ⟨toL j, (hmemJ j).mp j.2⟩
    have hκk : κ k = 1 := hκtriv k (by change toL j ∈ _; rw [hjA]; exact hkL')
    have hσk : σ k = 1 := hσJ1 k (by change toL j ∈ _; rw [hjA]; exact hkJ1)
    refine LinearMap.ext fun v => Ψ.toLinearEquiv.injective ?_
    change Ψ (ρ.representation j v) = Ψ v
    rw [hρk, Representation.tprod_apply]
    change TensorProduct.map (κ k) (σ k) (Ψ v) = Ψ v
    rw [hκk, hσk, TensorProduct.map_one, Module.End.one_apply]
  -- nontriviality of the carriers
  have hWnt : ∃ w : (ρ : Type uρ), w ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hΦ (Representation.IntertwiningMap.ext (LinearMap.ext fun w => by
      rw [hall w, map_zero, map_zero]))
  have hσnt : Nontrivial (Fin dσ → ℂ) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    obtain ⟨w, hw⟩ := hWnt
    have hzero : ∀ z : TensorProduct ℂ (Fin dκ → ℂ) (Fin dσ → ℂ), z = 0 := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a b => rw [Subsingleton.elim b 0, TensorProduct.tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    apply hw
    apply Ψ.toLinearEquiv.injective
    rw [map_zero]
    exact hzero _
  -- intertwiners at the powers of the contraction
  have hHecke : ∀ r : ℕ, ∃ Θ : intertwiningSpace ρ.representation ρ.representation (ζ ^ r),
      ∀ Φ' : ρ.representation.IntertwiningMap (π.representation.comp J.subtype),
        typeHeckeMean ρ.representation π.representation (ζ ^ r) Θ.toLinearMap
          Φ'.toLinearMap = 0 → Φ' = 0 := by
    intro r
    have hcent : ζA ^ r ∈ centralizerUnitGroup S.b :=
      pow_mem (zeta_mem_centralizer hε hπF hεb) r
    have hκr : Intertwines κ κ (ζA ^ r) := hκint _ hcent
    have hlamr : Intertwines (κ.tprod σ) (κ.tprod σ) (ζA ^ r) :=
      intertwines_tprod κ σ _ hκr (fun j hj => sigma_conj_eq hε hπF S.chain Rj (simpleJ S.chain S.n S.b q.tail)
        (simpleJGroup S.chain S.n S.b q.tail 1) hJ hJ1 hRL heR hoff σ hσJ1 r j hj)
    have hρA : Intertwines (glRepresentationToAut ρ) (glRepresentationToAut ρ) (ζA ^ r) := by
      have h1 := IsPairIsomorphic.selfIntertwining_eq hpair'
      have h2 : ζA ^ r ∈ representationSelfIntertwining (κ.tprod σ) := hlamr
      rw [← h1] at h2
      exact h2
    have hcomp : (glRepresentationToAut ρ).comp (glSubgroupToAutEquiv J).toMonoidHom =
        ρ.representation := by
      ext j : 1
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        glRepresentationToAut_apply]
    have hρr : Intertwines ρ.representation ρ.representation (ζ ^ r) := by
      have h := (selfIntertwines_comp_mulEquiv_iff toL.toMonoidHom toL.injective
        (glSubgroupToAutEquiv J) (fun _ => rfl) (glRepresentationToAut ρ) (ζ ^ r)).mpr
        (by
          change Intertwines _ _ (toL (ζ ^ r))
          rw [htoLζ]
          exact hρA)
      rwa [hcomp] at h
    obtain ⟨Θ, hΘ⟩ := hρr
    refine ⟨Θ, hH (ζ ^ r) ?_ Θ hΘ⟩
    change toL (ζ ^ r) ∈ _
    rw [htoLζ]
    exact hcent
  have : FiniteDimensional ℂ (ρ : Type uρ) :=
    LinearEquiv.finiteDimensional Ψ.toLinearEquiv.symm
  have hnot := TypeHeckeJacquet.not_subsingleton_coinvariants_of_heckeInjective
    π.representation π.isSmooth hJco.2 hJco.1 ρ.representation ρ.isSmooth hcontr hshrink hHecke
    Φ hΦ
  obtain ⟨B, g, hB, hBU⟩ := exists_blockShape hε hε0 hε1
  exact ⟨B, g, hB, not_subsingleton_coinvariants_of_le π.representation
    (fun x hx => hBU x hx) hnot⟩

/-- **The reduction.** Injectivity of the Hecke operators of simple types of kind (a)
(`PositiveDepthTypeHeckeInjectivityStatement`) implies the Jacquet nonvanishing statement
`PositiveDepthNonmaximalTypeJacquetStatement`. -/
theorem positiveDepthNonmaximalTypeJacquet_of_heckeInjectivity
    (hH : PositiveDepthTypeHeckeInjectivityStatement.{uF, uρ, uπ}) :
    PositiveDepthNonmaximalTypeJacquetStatement.{uF, uρ, uπ} := by
  intro F _ _ _ _ n hn ψF J ρ S q e hdata he2 π hcont
  exact not_subsingleton_jacquet_of_heckeInjective ρ hdata he2 π
    (fun x hx Θ hΘ Φ => hH F n hn ψF J ρ S q e hdata x hx Θ hΘ π Φ) hcont

end Main

end Langlands.BushnellKutzko.PositiveDepthNonmaximalReduction

namespace Langlands.BushnellKutzko

universe uF uρ uπ

/-- **Reduction of the Jacquet nonvanishing for kind (a) to Hecke injectivity.** The injectivity
of the Hecke operators of simple types of kind (a) on `Hom_J(ρ, π)`
(`PositiveDepthTypeHeckeInjectivityStatement`) implies
`PositiveDepthNonmaximalTypeJacquetStatement`, with the same universes for the field, the type
and the representation. -/
def PositiveDepthNonmaximalTypeJacquetReductionStatement : Prop :=
  PositiveDepthTypeHeckeInjectivityStatement.{uF, uρ, uπ} →
    PositiveDepthNonmaximalTypeJacquetStatement.{uF, uρ, uπ}

/-- The reduction holds. -/
theorem positiveDepthNonmaximalTypeJacquetReduction :
    PositiveDepthNonmaximalTypeJacquetReductionStatement.{uF, uρ, uπ} :=
  PositiveDepthNonmaximalReduction.positiveDepthNonmaximalTypeJacquet_of_heckeInjectivity

end Langlands.BushnellKutzko
