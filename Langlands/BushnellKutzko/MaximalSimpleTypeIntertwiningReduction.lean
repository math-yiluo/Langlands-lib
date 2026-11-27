import Langlands.BushnellKutzko.MaximalSimpleTypeIntertwiningStatement
import Langlands.BushnellKutzko.BetaExtensionTwistStatement
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesProof
import Langlands.BushnellKutzko.RelativeCuspidalLayer
import Langlands.Correspondence.HenniartUnramified.Extension
import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Langlands.Representation.Induction.OpenNormalRestrictionSemisimple

/-! # Maximal-simple-type intertwining from the beta-extension twist -/

noncomputable section

open ValuativeRel IsLocalRing
open scoped Pointwise

namespace Langlands.BushnellKutzko

section Representations

variable {G W W' : Type*} [Group G] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']
  {J J' : Subgroup G} {ρ : Representation ℂ J W} {σ : Representation ℂ J' W'}

private theorem isIrreducible_iff_of_pairIso (h : IsPairIsomorphic ρ σ) :
    ρ.IsIrreducible ↔ σ.IsIrreducible := by
  obtain ⟨rfl, ⟨e⟩⟩ := h
  have he : ρ.comp (MulEquiv.subgroupCongr (rfl : J = J)).symm.toMonoidHom = ρ := by
    ext j : 1
    rfl
  rw [he] at e
  exact CentralEigenspaceSplitting.isIrreducible_iff_of_equiv e

private theorem pairIso_conj_of_intertwines_inv (hρ : ρ.IsIrreducible) {x : G}
    (hx : x ∈ Subgroup.normalizer J) (h : Intertwines ρ ρ x⁻¹) :
    IsPairIsomorphic (conjRepresentation x ρ) ρ := by
  have hJ : Langlands.Group.RelativeWeyl.conjugateSubgroup x J = J :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  let e := (conjSubgroupEquiv x J).trans (MulEquiv.subgroupCongr hJ)
  have he (j : J) : (e j : G) = x * (j : G) * x⁻¹ := rfl
  have hInv (j : J) : (e.symm j : G) = x⁻¹ * (j : G) * x := by
    have heq := he (e.symm j)
    rw [e.apply_symm_apply] at heq
    rw [heq]
    group
  let τ := ρ.comp e.symm.toMonoidHom
  have hτ : Representation.IsIrreducible τ :=
    Induction.isIrreducible_comp_of_surjective ρ e.symm.toMonoidHom e.symm.surjective hρ
  obtain ⟨f, hf, hEq⟩ := (selfIntertwines_iff ρ x⁻¹).1 h
  let T : Representation.IntertwiningMap τ ρ := ⟨f, fun j => LinearMap.ext fun w => by
    have hh : x⁻¹ * (j : G) * (x⁻¹)⁻¹ ∈ J := by
      rw [inv_inv, ← hInv j]
      exact (e.symm j).2
    change f (ρ (e.symm j) w) = ρ j (f w)
    rw [show e.symm j = ⟨_, hh⟩ from Subtype.ext (by simpa only [inv_inv] using hInv j)]
    exact hEq j hh w⟩
  have hT : T ≠ 0 := fun heq => hf (congrArg Representation.IntertwiningMap.toLinearMap heq)
  let := hτ
  let := hρ
  exact ⟨hJ, ⟨T.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero T).resolve_right hT)⟩⟩

private theorem normalizing_middle_product (J U : Subgroup G) (hU : U ≤ J)
    (E : Set G) (hN : ∀ x ∈ E, x ∈ Subgroup.normalizer J) :
    ((J : Set G) * (E * (U : Set G))) * (J : Set G) = E * (J : Set G) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨j, hj, _, ⟨a, ha, u, hu, rfl⟩, rfl⟩, k, hk, rfl⟩
    have hconj := (Subgroup.mem_normalizer_iff''.1 (hN a ha) j).1 hj
    refine ⟨a, ha, a⁻¹ * j * a * u * k, J.mul_mem (J.mul_mem hconj (hU hu)) hk, ?_⟩
    change a * (a⁻¹ * j * a * u * k) = j * (a * u) * k
    group
  · rintro _ ⟨a, ha, j, hj, rfl⟩
    refine ⟨a, ⟨1, one_mem J, a, ⟨a, ha, 1, one_mem U, mul_one a⟩, one_mul a⟩, j, hj, rfl⟩

end Representations

universe uF uV uW

/-- The beta-extension twist in the coordinate representation spaces used by simple type
data implies maximal-simple-type intertwining for arbitrary representation carriers. -/
def MaximalSimpleTypeIntertwiningReductionStatement : Prop :=
  BetaExtensionTwistStatement.{uF, uV, 0, 0, 0} →
    MaximalSimpleTypeIntertwiningStatement.{uF, uV, uW}

set_option maxHeartbeats 1800000 in
/-- The period-one intertwining calculation reduces the maximal-simple-type
conclusion to the beta-extension twist. -/
theorem maximalSimpleTypeIntertwining_of_twist :
    MaximalSimpleTypeIntertwiningReductionStatement.{uF, uV, uW} := by
  intro hTwist F _ _ _ _ V _ _ ψ hψ J W _ _ ρ
  refine ⟨?_, fun L hL => levelZeroSimpleTypeIntertwining L hL⟩
  intro S q h
  obtain ⟨_, hr, _, hS, hp, θ, hθ, dη, η, hη, dκ, κ, hκ, n, d, σ₀, hσ₀, hc,
    b, φ, hφ, dσ, σ, _, hσtriv, ⟨hσeq⟩, hpair⟩ := h
  let E := elementAlgebra S.b
  let : Field E := hS.1.1.fst.toField
  let : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
  let : IsDiscreteValuationRing (subfieldIntegers F E) := subfieldIntegers_isDiscreteValuationRing F E
  let J₀ := simpleJ S.chain S.n S.b q.tail
  let U := relativeUnitFiltration S.chain S.b 0
  let G := (Module.End F V)ˣ
  let Eunits : Set G := {x | (x : Module.End F V) ∈ E}
  let N := Subgroup.normalizer (J₀ : Set G)
  have hEunits : Set.range (subfieldUnits F E V) = Eunits :=
    range_subfieldUnits_elementAlgebra S.chain S.b hS.1.1.fst
  have hSubgroup : J = J₀ := hpair.choose
  have hCentralizer (a : Eˣ) : subfieldUnits F E V a ∈ centralizerUnitGroup S.b := by
    rw [← centralizerUnitsRestrictScalars_range]
    exact ⟨_, centralizerUnitsRestrictScalars_scalar S.b hS.1.1.fst a⟩
  have hNorm : ∀ x ∈ Eunits, x ∈ N := by
    intro x hx
    rw [← hEunits] at hx
    obtain ⟨a, rfl⟩ := hx
    exact ((simpleStratumGroupProperties F V S hr hS q).2.2.1 0).2
      ⟨hCentralizer a, hS.1.1.snd a⟩
  let : IsSimpleModule (MonoidAlgebra ℂ _) σ₀.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ₀).mp hσ₀
  let : Nontrivial (Fin d → ℂ) := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (GeneralLinear n (ResidueField (subfieldIntegers F E)))) σ₀.asModule
  obtain ⟨hSurj, hInt⟩ := relativeCuspidalLayer S hS hp.symm n σ₀ hc b φ hφ
  let incl := Subgroup.inclusion (relativeUnitFiltration_le_simpleJ S.chain S.n S.b q.tail)
  have hσIrr : σ.IsIrreducible := by
    have hI : Representation.IsIrreducible (σ₀.comp ((Pi.evalMonoidHom _ 0).comp φ)) :=
      Induction.isIrreducible_comp_of_surjective _ _ hSurj hσ₀
    have hI' := (CentralEigenspaceSplitting.isIrreducible_iff_of_equiv
      (hσeq.trans (tensorPowerOneEquiv σ₀ φ))).2 hI
    exact FiniteRepresentation.SplitDegree.isIrreducible_of_comp σ incl hI'
  obtain ⟨hTw, _, hIrr⟩ := hTwist F V ψ hψ S hr hS q θ hθ _ η hη _ κ hκ _ σ hσIrr hσtriv
  have hMid : {y : G | y ∈ centralizerUnitGroup S.b ∧
      y ∈ representationSelfIntertwining (σ.comp incl)} = Eunits * (U : Set G) := by
    have he : representationSelfIntertwining (σ.comp incl) =
        representationSelfIntertwining ((tensorPowerRepresentation σ₀ 1).comp φ) := by
      ext y
      exact ⟨selfIntertwines_of_equiv hσeq, selfIntertwines_of_equiv hσeq.symm⟩
    rw [he, hInt, hEunits]
  have hEq : representationSelfIntertwining ρ = Eunits * (J : Set G) := by
    rw [hpair.selfIntertwining_eq, hTw]
    change ((J₀ : Set G) * {y : G | y ∈ centralizerUnitGroup S.b ∧
      y ∈ representationSelfIntertwining (σ.comp incl)}) * (J₀ : Set G) = _
    rw [hMid, hSubgroup]
    exact normalizing_middle_product J₀ U
      (relativeUnitFiltration_le_simpleJ S.chain S.n S.b q.tail) Eunits hNorm
  refine ⟨?_, hEq⟩
  intro x hx
  change x ∈ Eunits at hx
  have hxN : x ∈ Subgroup.normalizer J := hSubgroup ▸ hNorm x hx
  have hinv : x⁻¹ ∈ Eunits := by
    rw [← hEunits] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a⁻¹, map_inv _ _⟩
  have hxI : x⁻¹ ∈ representationSelfIntertwining ρ := by
    rw [hEq]
    exact ⟨x⁻¹, hinv, 1, one_mem J, mul_one _⟩
  exact pairIso_conj_of_intertwines_inv ((isIrreducible_iff_of_pairIso hpair).2 hIrr) hxN hxI

end Langlands.BushnellKutzko
