import Langlands.BushnellKutzko.PureStratumTopNonsplitProof
import Langlands.BushnellKutzko.SubfieldChainLayers
import Langlands.BushnellKutzko.PureStratumApproximationFieldInvariants
import Langlands.BushnellKutzko.IrreducibleAnnihilatorConjugacy

/-! # Residues of integral units of a normalizing field

Let `E` be a field acting on `V` whose units normalize a lattice chain over `𝒪_F`, and let `w` be
a unit of the integral closure `𝔬_E` of `𝒪_F` in `E`, with residue `c` in `k_E`.
`LatticeChain.reduceIntegralPolynomial_charpoly_eq_minpoly_pow` shows that the reduction modulo
`𝔭_F` of the characteristic polynomial of `w` acting on `V` is a positive power of the minimal
polynomial of `c` over `k_F`, transported to `𝒪_F / Jac(𝒪_F)`. This refines
`LatticeChain.exists_reduceIntegralPolynomial_charpoly_eq_pow` by naming the irreducible factor.

On each successive quotient `L_r / L_{r+1}` the residue field `k_E` acts compatibly with `k_F`.
`LatticeChain.exists_layerEquiv_residue_intertwine` shows that two such residues, from two
normalizing fields, with the same minimal polynomial over `k_F` act conjugately on every layer.
-/

open Polynomial ValuativeRel IsLocalRing

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uE

/-- The residue field of a local ring as the quotient by its Jacobson radical. -/
def residueJacobsonEquiv (O : Type*) [CommRing O] [IsLocalRing O] :
    ResidueField O ≃+* O ⧸ Ring.jacobson O :=
  Ideal.quotEquivOfEq (ringJacobson_eq_maximalIdeal O).symm

/-- The residue class of `a` corresponds to its class modulo the Jacobson radical. -/
@[simp] theorem residueJacobsonEquiv_residue (O : Type*) [CommRing O] [IsLocalRing O] (a : O) :
    residueJacobsonEquiv O (residue O a) = Ideal.Quotient.mk (Ring.jacobson O) a :=
  rfl

/-- Reducing an integral polynomial modulo the maximal ideal and transporting the coefficients
gives its reduction modulo the Jacobson radical. -/
theorem map_residue_map_residueJacobsonEquiv (O : Type*) [CommRing O] [IsLocalRing O]
    (P : O[X]) :
    (P.map (residue O)).map (residueJacobsonEquiv O : ResidueField O →+* O ⧸ Ring.jacobson O) =
      P.map (Ideal.Quotient.mk (Ring.jacobson O)) := by
  rw [Polynomial.map_map]
  rfl

local notation "𝒪ₑ[" F "," E "]" => subfieldIntegers F E

namespace LatticeChain

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)
  (E : Type uE) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)
  [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsLocalHom (algebraMap 𝒪[F] 𝒪ₑ[F,E])]

include hE in
/-- The reduced characteristic polynomial of an integral unit of a normalizing field is a
positive power of the image of the minimal polynomial of its residue. -/
theorem reduceIntegralPolynomial_charpoly_eq_minpoly_pow [FiniteDimensional F V]
    (w : 𝒪ₑ[F,E]ˣ) :
    IsIntegral (ResidueField 𝒪[F]) (residue 𝒪ₑ[F,E] (w : 𝒪ₑ[F,E])) ∧
    ∃ m : ℕ, 0 < m ∧
      reduceIntegralPolynomial 𝒪[F] F
          (subfieldEmbedding F E V ((w : 𝒪ₑ[F,E]) : E)).charpoly =
        ((minpoly (ResidueField 𝒪[F]) (residue 𝒪ₑ[F,E] (w : 𝒪ₑ[F,E]))).map
          (residueJacobsonEquiv 𝒪[F] : ResidueField 𝒪[F] →+* 𝒪[F] ⧸ Ring.jacobson 𝒪[F])) ^ m := by
  classical
  have : Algebra.IsIntegral 𝒪[F] 𝒪ₑ[F,E] := inferInstanceAs
    (Algebra.IsIntegral 𝒪[F] (integralClosure 𝒪[F] E))
  let c := residue 𝒪ₑ[F,E] (w : 𝒪ₑ[F,E])
  have hcomp : (algebraMap (ResidueField 𝒪[F]) (ResidueField 𝒪ₑ[F,E])).comp (residue 𝒪[F]) =
      (residue 𝒪ₑ[F,E]).comp (algebraMap 𝒪[F] 𝒪ₑ[F,E]) := rfl
  have hint : IsIntegral (ResidueField 𝒪[F]) c :=
    (Algebra.IsIntegral.isIntegral (R := 𝒪[F]) (w : 𝒪ₑ[F,E])).map_of_comp_eq
      (residue 𝒪[F]) (residue 𝒪ₑ[F,E]) hcomp
  refine ⟨hint, ?_⟩
  obtain ⟨P, hPmap, -, -⟩ := lifts_and_degree_eq_and_monic
    (mem_lifts_of_surjective residue_surjective _) (minpoly.monic hint)
  have hz : residue 𝒪ₑ[F,E] (aeval (w : 𝒪ₑ[F,E]) P) = 0 := by
    have h := minpoly.aeval (ResidueField 𝒪[F]) c
    rw [← hPmap, aeval_def, eval₂_map, hcomp, ← hom_eval₂, ← aeval_def] at h
    exact h
  have hzm := (residue_eq_zero_iff _).mp hz
  obtain ⟨ϖE, hϖE⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪ₑ[F,E]
  rw [hϖE.maximalIdeal_eq, Ideal.mem_span_singleton'] at hzm
  obtain ⟨d, hd⟩ := hzm
  have hstep : ∀ i (v : V), v ∈ 𝓛.lattice i →
      ((aeval (w : 𝒪ₑ[F,E]) P : 𝒪ₑ[F,E]) : E) • v ∈ 𝓛.lattice (i + 1) := by
    intro i v hv
    rw [← hd]
    have hs := 𝓛.fieldShift_uniformizer_pos E hE hϖE
    have h1 : ((ϖE : 𝒪ₑ[F,E]) : E) • v ∈ 𝓛.lattice (i + 1) :=
      𝓛.antitone (by omega) ((𝓛.mem_lattice_fieldShift E hE
        (Units.mk0 (ϖE : E) (fun h => hϖE.ne_zero (Subtype.ext h))) i).mpr hv)
    have h2 := 𝓛.subfieldInteger_smul_mem E hE (i + 1) d h1
    rwa [Subalgebra.coe_mul, mul_smul]
  have hpow : ∀ t : ℕ, ∀ i (v : V), v ∈ 𝓛.lattice i →
      (((aeval (w : 𝒪ₑ[F,E]) P) ^ t : 𝒪ₑ[F,E]) : E) • v ∈ 𝓛.lattice (i + t) := by
    intro t
    induction t with
    | zero =>
      intro i v hv
      simpa using hv
    | succ t ih =>
      intro i v hv
      rw [pow_succ', Subalgebra.coe_mul, mul_smul, Nat.cast_succ, ← add_assoc]
      exact hstep _ _ (ih i v hv)
  have hYeval : ∀ (Q : 𝒪[F][X]) (v : V),
      aeval (subfieldEmbedding F E V ((w : 𝒪ₑ[F,E]) : E)) (Q.map (algebraMap 𝒪[F] F)) v =
        ((aeval (w : 𝒪ₑ[F,E]) Q : 𝒪ₑ[F,E]) : E) • v := by
    intro Q v
    rw [aeval_algHom_apply, subfieldEmbedding_apply, aeval_map_algebraMap,
      show ((w : 𝒪ₑ[F,E]) : E) = algebraMap 𝒪ₑ[F,E] E (w : 𝒪ₑ[F,E]) from rfl,
      aeval_algebraMap_apply]
    rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hQ : ∀ v ∈ 𝓛.lattice 0, ∃ w' ∈ 𝓛.lattice 0,
      aeval (subfieldEmbedding F E V ((w : 𝒪ₑ[F,E]) : E))
          ((P ^ 𝓛.period).map (algebraMap 𝒪[F] F)) v = (ϖ : F) • w' := by
    intro v hv
    rw [hYeval, map_pow]
    have hx := hpow 𝓛.period 0 v hv
    refine ⟨(ϖ : F)⁻¹ •
      ((((aeval (w : 𝒪ₑ[F,E]) P) ^ 𝓛.period : 𝒪ₑ[F,E]) : E) • v), ?_, ?_⟩
    · apply (𝓛.uniformizer_lattice_mem_iff hϖ 0 _).mp
      rw [smul_inv_smul₀ hϖ0]
      exact hx
    · rw [smul_inv_smul₀ hϖ0]
  have hYL : ∀ v ∈ 𝓛.lattice 0,
      subfieldEmbedding F E V ((w : 𝒪ₑ[F,E]) : E) v ∈ 𝓛.lattice 0 := by
    intro v hv
    rw [subfieldEmbedding_apply]
    exact 𝓛.subfieldInteger_smul_mem E hE 0 w hv
  have hPJ : P.map (Ideal.Quotient.mk (Ring.jacobson 𝒪[F])) =
      (minpoly (ResidueField 𝒪[F]) c).map
        (residueJacobsonEquiv 𝒪[F] : ResidueField 𝒪[F] →+* 𝒪[F] ⧸ Ring.jacobson 𝒪[F]) := by
    rw [← hPmap, map_residue_map_residueJacobsonEquiv]
  have hPm : (P.map (Ideal.Quotient.mk (Ring.jacobson 𝒪[F]))).Monic := by
    rw [hPJ]
    exact (minpoly.monic hint).map _
  have hPirr : Irreducible (P.map (Ideal.Quotient.mk (Ring.jacobson 𝒪[F]))) := by
    have : (Ring.jacobson 𝒪[F]).IsMaximal := by
      rw [ringJacobson_eq_maximalIdeal]
      infer_instance
    let : Field (𝒪[F] ⧸ Ring.jacobson 𝒪[F]) := Ideal.Quotient.field _
    rw [hPJ, ← Polynomial.mapEquiv_apply, MulEquiv.irreducible_iff]
    exact minpoly.irreducible hint
  obtain ⟨m, hm, h⟩ := 𝓛.reduceIntegralPolynomial_charpoly_eq_pow hϖ _ hYL hPm hPirr 𝓛.period hQ
  exact ⟨m, hm, h.trans (by rw [hPJ])⟩

/-- The base residue field, through the extension residue field, acts on each layer by its own
residue action. -/
theorem subfieldLayer_isScalarTower_residue (i : ℤ) :
    letI := 𝓛.subfieldLayerResidueModule E hE i
    IsScalarTower (ResidueField 𝒪[F]) (ResidueField 𝒪ₑ[F,E]) (𝓛.Layer i) := by
  let := 𝓛.subfieldLayerResidueModule E hE i
  have := 𝓛.subfieldLayerResidueTower E hE i
  refine IsScalarTower.of_algebraMap_smul fun a q => ?_
  obtain ⟨a₀, rfl⟩ := residue_surjective a
  change (algebraMap 𝒪[F] (ResidueField 𝒪ₑ[F,E]) a₀) • q =
    (algebraMap 𝒪[F] (ResidueField 𝒪[F]) a₀) • q
  rw [algebraMap_smul, algebraMap_smul]

end LatticeChain

namespace LatticeChain

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

/-- Two residues of normalizing extensions with the same minimal polynomial over the base residue
field act conjugately on every layer of the chain. -/
theorem exists_layerEquiv_residue_intertwine
    (E₁ : Type*) [Field E₁] [Algebra F E₁] [Module E₁ V] [IsScalarTower F E₁ V]
    (hE₁ : ∀ a : E₁ˣ, subfieldUnits F E₁ V a ∈ 𝓛.stabilizer)
    [IsDiscreteValuationRing 𝒪ₑ[F,E₁]] [IsLocalHom (algebraMap 𝒪[F] 𝒪ₑ[F,E₁])]
    (E₂ : Type*) [Field E₂] [Algebra F E₂] [Module E₂ V] [IsScalarTower F E₂ V]
    (hE₂ : ∀ a : E₂ˣ, subfieldUnits F E₂ V a ∈ 𝓛.stabilizer)
    [IsDiscreteValuationRing 𝒪ₑ[F,E₂]] [IsLocalHom (algebraMap 𝒪[F] 𝒪ₑ[F,E₂])]
    (c₁ : ResidueField 𝒪ₑ[F,E₁]) (c₂ : ResidueField 𝒪ₑ[F,E₂])
    (hc₁ : IsIntegral (ResidueField 𝒪[F]) c₁)
    (h : minpoly (ResidueField 𝒪[F]) c₁ = minpoly (ResidueField 𝒪[F]) c₂) (r : ℤ) :
    ∃ ψ : 𝓛.Layer r ≃ₗ[𝒪[F]] 𝓛.Layer r, ∀ q : 𝓛.Layer r,
      letI := 𝓛.subfieldLayerResidueModule E₁ hE₁ r
      letI := 𝓛.subfieldLayerResidueModule E₂ hE₂ r
      ψ (c₂ • q) = c₁ • ψ q := by
  let := 𝓛.subfieldLayerResidueModule E₁ hE₁ r
  let := 𝓛.subfieldLayerResidueModule E₂ hE₂ r
  have := 𝓛.subfieldLayer_isScalarTower_residue E₁ hE₁ r
  have := 𝓛.subfieldLayer_isScalarTower_residue E₂ hE₂ r
  have : Module.Finite 𝒪[F] (𝓛.lattice r) := Module.Finite.iff_fg.mpr (𝓛.fg_lattice r)
  have : Module.Finite (ResidueField 𝒪[F]) (𝓛.Layer r) :=
    Module.Finite.of_restrictScalars_finite 𝒪[F] _ _
  let A := Algebra.lsmul (ResidueField 𝒪[F]) (ResidueField 𝒪[F]) (𝓛.Layer r) c₂
  let B := Algebra.lsmul (ResidueField 𝒪[F]) (ResidueField 𝒪[F]) (𝓛.Layer r) c₁
  have hA : aeval A (minpoly (ResidueField 𝒪[F]) c₁) = 0 := by
    rw [h, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hB : aeval B (minpoly (ResidueField 𝒪[F]) c₁) = 0 := by
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  obtain ⟨φ, hφ⟩ := exists_linearEquiv_conj_of_aeval_irreducible (minpoly.irreducible hc₁) hA hB
  exact ⟨φ.restrictScalars 𝒪[F], fun q => hφ q⟩

end LatticeChain

end Langlands.BushnellKutzko
