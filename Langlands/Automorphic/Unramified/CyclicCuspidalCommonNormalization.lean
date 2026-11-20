import Langlands.Automorphic.AssociatedCentralCharacter.GoodPlaces
import Langlands.Automorphic.CentralCharacterTopCoefficient
import Langlands.Automorphic.CuspidalContragredientExistenceProof
import Langlands.Automorphic.HeckeTwist.CuspidalSpectralTwist
import Langlands.Automorphic.Unramified.CyclicCuspidalFiberStatement
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Global.Factors.HeckeEulerProduct
import Langlands.Global.Factors.RelativeWeilLocalEulerBridge
import Langlands.Global.GlobalPlaceTopologyFacts

/-! # Common unitary normalization for the cyclic cuspidal fibre argument -/

noncomputable section

universe uF uE uS uT

set_option autoImplicit false

open scoped NumberField NNReal

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

variable {F : Type uF} [Field F] [NumberField F]

private theorem exists_norm_ideleClass_rpow (ω : HeckeCharacter F) :
    ∃ a : ℝ, ∀ x : IdeleClasses F,
      ‖(ω x : ℂ)‖ = ((IdeleAbsoluteValue.ideleClass F x : ℝ≥0) : ℝ) ^ a := by
  classical
  let w : NumberField.InfinitePlace F := Classical.arbitrary _
  obtain ⟨j, hj⟩ := HeckeEulerProduct.exists_norm_ringHom w
  obtain ⟨b, hb⟩ := HeckeEulerProduct.exists_norm_infiniteComponent_ray ω j hj
  have hm : (0 : ℝ) < w.mult := by exact_mod_cast NumberField.InfinitePlace.mult_pos (w := w)
  refine ⟨b / w.mult, fun x => ?_⟩
  let q : ℝ := ((IdeleAbsoluteValue.ideleClass F x : ℝ≥0) : ℝ)
  have hq : 0 < q := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (IdeleAbsoluteValue.ideleClass F x).ne_zero)
  let t : ℝ := Real.log q / w.mult
  let y := infiniteClassInclusion F w (HeckeEulerProduct.ray j t)
  have ht : (w.mult : ℝ) * t = Real.log q := by
    dsimp [t]
    field_simp
  have hy : IdeleAbsoluteValue.ideleClass F y = IdeleAbsoluteValue.ideleClass F x := by
    apply Units.ext
    apply NNReal.eq
    change ((IdeleAbsoluteValue.ideleClass F y : ℝ≥0) : ℝ) = q
    dsimp only [y]
    rw [IdeleAbsoluteValue.coe_ideleClass_infiniteClassInclusion,
      HeckeEulerProduct.norm_ray j hj, ← Real.exp_nat_mul, ht, Real.exp_log hq]
  have hxy : IdeleAbsoluteValue.ideleClass F (x / y) = 1 := by
    rw [map_div, hy, div_self']
  have hunit := HeckeEulerProduct.norm_eq_one_of_ideleClass_eq_one ω hxy
  have hyp : ‖(ω y : ℂ)‖ = Real.exp (b * t) := hb t
  rw [map_div, Units.val_div_eq_div_val, norm_div, div_eq_one_iff_eq
    (norm_ne_zero_iff.mpr (ω y).ne_zero)] at hunit
  rw [hunit, hyp, Real.rpow_def_of_pos hq]
  congr 1
  dsimp [t]
  ring

section TopCoefficient

open ContinuousRationalFunctions

local instance (r : ℕ) : AddCommGroup (RationalInvariantFunctions F r) := Submodule.addCommGroup _
local instance (r : ℕ) : AddCommGroup (ContinuousRationalFunctions F r) := Submodule.addCommGroup _
local instance (r : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F r) := Submodule.addCommGroup _
local instance (r : ℕ) : AddCommGroup (AutomorphicForms F r) := Submodule.addCommGroup _
local instance (r : ℕ) : AddCommGroup (StableAutomorphicFunctions F r) := Submodule.addCommGroup _
local instance {r : ℕ} (T : OperatorRealization F r) : AddCommGroup T.Space := Submodule.addCommGroup _

private theorem finiteUniformizerValue_eq_spectrum_prod [CompactSpace (AdeleQuotient F)]
    {r : ℕ} {T : CuspidalOperatorRealization F r} {ω : HeckeCharacter F}
    (hω : T.HasCentralCharacter ω) (P : CuspidalSpectralPresentation.{uF, uS} T)
    (v : FinitePlace F) (hv : v ∉ P.exceptional) :
    ω.finiteUniformizerValue v = (P.spectralSystem.eigenvalues v hv : Multiset ℂˣ).prod := by
  let π := (CompletionPadic.padicField v).canonicalTopologicalData.uniformizerUnit
  have hz : finiteIdeleInclusion F v π ∈ T.realization.centralCharacterSubgroup ω :=
    (T.realization.mem_centralCharacterSubgroup ω _).mpr
      (fun f x => T.realization.centralCharacter_evaluate ω hω f _ x)
  obtain ⟨b, hb⟩ := P.exists_spherical_ne_zero v hv
  have hb₀ : (b : T.realization.Space) ≠ 0 := fun h => hb (Subtype.ext h)
  have hωb := (T.realization.finiteIdeleInclusion_mem_centralCharacterSubgroup_iff ω v π).mp hz
    (b : T.realization.Space)
  have hcorner := congrArg Subtype.val (P.corner_eq_smul v hv b (Fin.last (r + 1)))
  have htop := standardHecke_cornerAction_last (CompletionPadic.padicField v)
    (T.realization.localRepresentation v)
    (T.realization.localRepresentation_isSmooth_canonical v) b
  have hdiag := standardDiagonal_last (CompletionPadic.padicField v) (r := r)
  have hs := standardHeckeScalar_last (CompletionPadic.padicField v)
    (P.spectralSystem.eigenvalues v hv)
  apply Units.ext
  refine smul_left_injective ℂ hb₀ ?_
  have hscalar := congrArg
    (fun g => T.realization.localRepresentation v g (b : T.realization.Space)) hdiag
  calc
    (ω.finiteUniformizerValue v : ℂ) • (b : T.realization.Space) = _ := hωb.symm
    _ = _ := hscalar.symm
    _ = _ := htop.symm
    _ = _ := hcorner
    _ = _ := Submodule.coe_smul _ b
    _ = _ := congrArg (fun c : ℂ => c • (b : T.realization.Space))
      (hs.trans (elementaryCoefficient_rank _))

end TopCoefficient

private theorem norm_ideleClass_uniformizer (v : FinitePlace F) :
    ((IdeleAbsoluteValue.ideleClass F (finiteClassInclusion F v
      (CompletionPadic.padicField v).canonicalTopologicalData.uniformizerUnit) : ℝ≥0) : ℝ) =
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [IdeleAbsoluteValue.coe_ideleClass_finiteClassInclusion,
    ← CompletionPadic.topologicalData_eq_canonicalTopologicalData]
  exact HeckeEulerProduct.norm_uniformizerUnit v

private theorem unitarizingCharacter_eq_of_sameResidueDegreePowers
    {E : Type uE} [Field E] [NumberField E] [Algebra F E]
    [CompactSpace (AdeleQuotient F)] {r : ℕ} {T U : CuspidalOperatorRealization F r}
    {ω ω' : HeckeCharacter F} (hω : T.HasCentralCharacter ω) (hω' : U.HasCentralCharacter ω')
    (P : CuspidalSpectralPresentation.{uF, uS} T) (Q : CuspidalSpectralPresentation.{uF, uT} U)
    (h : SpectralSystem.SameResidueDegreePowers E P.spectralSystem Q.spectralSystem) :
    unitarizingCharacter r ω = unitarizingCharacter r ω' := by
  classical
  obtain ⟨a, ha⟩ := exists_norm_ideleClass_rpow ω
  obtain ⟨b, hb⟩ := exists_norm_ideleClass_rpow ω'
  let _ : Infinite (FinitePlace F) := numberField_finitePlaces_infinite F
  obtain ⟨v, hv, hv', he⟩ := h.exists
  let w := placeAbove E v
  let f := w.1.asIdeal.inertiaDeg (𝓞 F)
  have hf : f ≠ 0 := (w.1.asIdeal.inertiaDeg_pos (𝓞 F)).ne'
  have hdet := congrArg (fun z : Eigenvalues (r + 1) => (z : Multiset ℂˣ).prod) (he w).2
  simp only [Eigenvalues.power, Sym.coe_map, Multiset.prod_map_pow] at hdet
  change (Multiset.map id _).prod ^ f = (Multiset.map id _).prod ^ f at hdet
  simp only [Multiset.map_id] at hdet
  rw [← finiteUniformizerValue_eq_spectrum_prod hω P v hv,
    ← finiteUniformizerValue_eq_spectrum_prod hω' Q v hv'] at hdet
  have hnorm := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) hdet
  simp only [Units.val_pow_eq_pow_val, norm_pow] at hnorm
  have hnorm' := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hf).mp hnorm
  let x := finiteClassInclusion F v (CompletionPadic.padicField v).canonicalTopologicalData.uniformizerUnit
  change ‖(ω x : ℂ)‖ = ‖(ω' x : ℂ)‖ at hnorm'
  rw [ha, hb, norm_ideleClass_uniformizer] at hnorm'
  have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hab : a = b := (Real.rpow_right_inj (inv_pos.mpr (zero_lt_one.trans hq))
    (inv_lt_one_of_one_lt₀ hq).ne).mp hnorm'
  apply ContinuousMonoidHom.ext
  intro z
  apply Units.ext
  change (↑(‖(ω z : ℂ)‖ ^ (-1 / ((r : ℝ) + 1)) : ℝ) : ℂ) =
    (↑(‖(ω' z : ℂ)‖ ^ (-1 / ((r : ℝ) + 1)) : ℝ) : ℂ)
  rw [ha, hb, hab]

/-- The common residue-degree comparison of genuine spectra permits one Hecke
character to unitarize both actual realizations and preserve the comparison. -/
def CyclicCuspidalCommonNormalizationStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] (r : ℕ) (T U : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{uF, uS} T) (Q : CuspidalSpectralPresentation.{uF, uT} U),
    SpectralSystem.SameResidueDegreePowers E P.spectralSystem Q.spectralSystem →
    ∃ μ : HeckeCharacter F,
      HasUnitaryCentralCharacter (T.heckeDeterminantTwist μ) ∧
      HasUnitaryCentralCharacter (U.heckeDeterminantTwist μ) ∧
      SpectralSystem.SameResidueDegreePowers E
        (P.heckeDeterminantTwist μ).spectralSystem (Q.heckeDeterminantTwist μ).spectralSystem

/-- The common unitarizing twist used in Arthur–Clozel III.3.1. -/
theorem cyclicCuspidalCommonNormalization :
    CyclicCuspidalCommonNormalizationStatement.{uF, uE, uS, uT} := by
  intro F E _ _ _ _ _ _ r T U P Q h
  obtain ⟨ω, hω, -⟩ := T.realization.existsUnique_hasCentralCharacter T.irreducible
  obtain ⟨ω', hω', -⟩ := U.realization.existsUnique_hasCentralCharacter U.irreducible
  let μ := unitarizingCharacter r ω
  have hμ := unitarizingCharacter_eq_of_sameResidueDegreePowers hω hω' P Q h
  refine ⟨μ, hasUnitaryCentralCharacter_heckeDeterminantTwist_unitarizingCharacter T hω,
    ?_, ?_⟩
  · change HasUnitaryCentralCharacter (U.heckeDeterminantTwist (unitarizingCharacter r ω))
    rw [hμ]
    exact hasUnitaryCentralCharacter_heckeDeterminantTwist_unitarizingCharacter U hω'
  · filter_upwards [h,
      (P.heckeDeterminantTwist μ).exceptional.eventually_cofinite_notMem,
      (Q.heckeDeterminantTwist μ).exceptional.eventually_cofinite_notMem] with v hv hp hq
    obtain ⟨hP, hQ, hv⟩ := hv
    refine ⟨hp, hq, fun w => ⟨(hv w).1, ?_⟩⟩
    change (Eigenvalues.scale (μ.finiteUniformizerValue v) (P.spectralSystem.eigenvalues v hP)).power _ =
      (Eigenvalues.scale (μ.finiteUniformizerValue v) (Q.spectralSystem.eigenvalues v hQ)).power _
    rw [Eigenvalues.power_scale, Eigenvalues.power_scale, (hv w).2]

end Langlands.Automorphic.Unramified
