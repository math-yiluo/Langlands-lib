import Langlands.ClassFieldTheory.Local.NYLL.UniverseTransportStatement
import Langlands.ClassFieldTheory.Local.NYLL.UniverseZeroModel

/-! # Universe transport of finite abelian local reciprocity -/

namespace Langlands.LocalClassField.NYLL

universe u v

/-- Finite abelian local reciprocity at field universes zero implies it at
arbitrary independent field universes. -/
theorem finiteAbelianReciprocityUniverseTransport :
    FiniteAbelianReciprocityUniverseTransportStatement.{u, v} := by
  intro H p _ F E _ _ _ _ TF TE
  let := universeZeroAlgebra F E
  have := universeZeroAlgebra_isScalarTower F E
  have := universeZeroAlgebra_finiteDimensional F E
  have := universeZeroAlgebra_isAbelianGalois F E
  let TF₀ := (universeZeroModel F).canonicalTopologicalData
  let TE₀ := (universeZeroModel E).canonicalTopologicalData
  obtain ⟨r₀, hgeom, hiner⟩ := H p (universeZeroModel F) (universeZeroModel E) TF₀ TE₀
  let := TF₀.topology
  let := TF.topology
  let eF := universeZeroEquiv F
  let eE := universeZeroEquiv E
  let Q := universeZeroNormQuotientEquiv F E TF₀ TF
  let G := universeZeroGaloisEquiv F E
  have hQ : ∀ a : F.Carrierˣ, Q.symm (QuotientGroup.mk a) =
      QuotientGroup.mk (Units.mapEquiv eF.toRingEquiv.symm.toMulEquiv a) :=
    universeZeroNormQuotientEquiv_symm_mk F E TF₀ TF
  have hord : ∀ a : F.Carrierˣ,
      TF₀.ord ((Units.mapEquiv eF.toRingEquiv.symm.toMulEquiv a :
        (universeZeroModel F).Carrierˣ) : (universeZeroModel F).Carrier) =
        TF.ord (a : F.Carrier) := by
    intro a
    rw [← ord_eq_of_algEquiv eF TF₀ TF]
    exact congrArg TF.ord (eF.apply_symm_apply (a : F.Carrier))
  have hval : ∀ y : (universeZeroModel E).Carrier,
      TE.discreteValuation (eE y) = TE₀.discreteValuation y :=
    discreteValuation_eq_of_algEquiv eE TE₀ TE
  refine ⟨Q.symm.trans (r₀.trans G), ?_, ?_⟩
  · intro a ha x hx
    have hx₀ : TE₀.discreteValuation (eE.symm x) ≤ 1 := by
      rw [← hval, AlgEquiv.apply_symm_apply]
      exact hx
    have h := hgeom _ ((hord a).trans ha) (eE.symm x) hx₀
    have hq : TF.residueCardinality = TF₀.residueCardinality :=
      residueCardinality_eq_of_algEquiv eF TF₀ TF
    have key : ((Q.symm.trans (r₀.trans G)) (QuotientGroup.mk a)).symm x -
        x ^ TF.residueCardinality =
        eE ((r₀ (QuotientGroup.mk (Units.mapEquiv eF.toRingEquiv.symm.toMulEquiv a))).symm
          (eE.symm x) - eE.symm x ^ TF₀.residueCardinality) := by
      rw [hq, map_sub, map_pow, AlgEquiv.apply_symm_apply]
      rfl
    rw [key, hval]
    exact h
  · intro σ
    have hσ := hiner (G.symm σ)
    have hG : ∀ y : (universeZeroModel E).Carrier, eE ((G.symm σ) y) = σ (eE y) := by
      intro y
      exact eE.apply_symm_apply (σ (eE y))
    constructor
    · rintro ⟨a, ha, hra⟩
      have hr : r₀ (QuotientGroup.mk (Units.mapEquiv eF.toRingEquiv.symm.toMulEquiv a)) =
          G.symm σ := by
        rw [← hra, ← hQ]
        exact (G.symm_apply_apply _).symm
      have h₀ := hσ.1 ⟨_, (hord a).trans ha, hr⟩
      intro x hx
      have h := h₀ (eE.symm x) (by rw [← hval, AlgEquiv.apply_symm_apply]; exact hx)
      rw [← hval, map_sub, hG, AlgEquiv.apply_symm_apply] at h
      exact h
    · intro hR
      obtain ⟨a₀, ha₀, hr⟩ := hσ.2 (fun y hy => by
        have h := hR (eE y) (by rw [hval]; exact hy)
        rw [← hval, map_sub, hG]
        exact h)
      refine ⟨Units.mapEquiv eF.toRingEquiv.toMulEquiv a₀, ?_, ?_⟩
      · rw [← ha₀]
        exact ord_eq_of_algEquiv eF TF₀ TF (a₀ : (universeZeroModel F).Carrier)
      · have hc : Units.mapEquiv eF.toRingEquiv.symm.toMulEquiv
            (Units.mapEquiv eF.toRingEquiv.toMulEquiv a₀) = a₀ :=
          Units.ext (eF.symm_apply_apply (a₀ : (universeZeroModel F).Carrier))
        change G (r₀ (Q.symm (QuotientGroup.mk _))) = σ
        rw [hQ, hc, hr]
        exact G.apply_symm_apply σ

end Langlands.LocalClassField.NYLL
