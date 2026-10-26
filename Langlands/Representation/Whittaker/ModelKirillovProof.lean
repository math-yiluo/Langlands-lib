import Langlands.Representation.Whittaker.ModelKirillovStatement
import Langlands.Representation.Whittaker.PrerequisiteInterfaces

/-! # Conditional Kirillov lifting into actual coefficient models -/

noncomputable section

namespace Langlands.Whittaker

open HarmonicAnalysis GeneralLinear RankinSelberg
open scoped BigOperators

universe uF uV

/-- Transport the assumed canonical Kirillov lifting to every supplied topology
and the coefficient image of every specified nonzero Whittaker functional. -/
theorem modelKirillovTransfer : ModelKirillovTransferStatement.{uF, uV} := by
  intro h p hp F T
  have hT : T.topology = F.canonicalTopologicalData.topology :=
    T.topology_eq_canonicalModule.trans
      F.canonicalTopologicalData.topology_eq_canonicalModule.symm
  rw [hT]
  let := F.canonicalTopologicalData.topology
  intro n V _ _ π ψ hπ ℓ hℓ φ hφ
  obtain ⟨e⟩ := hπ.2.2
  have heℓ : e ℓ ≠ 0 := by
    intro hz
    apply hℓ
    exact congrArg Subtype.val (e.injective (hz.trans e.map_zero.symm))
  have huniq (ℓ' : Module.Dual ℂ V) (hℓ' : EntrywiseEquivariant π ψ.complex ℓ') :
      ∃ c : ℂ, ℓ' = c • ℓ.val := by
    let L : glFunctionals ψ n π :=
      ⟨ℓ', (mem_glFunctionals_iff_entrywise ψ π ℓ').mpr hℓ'⟩
    refine ⟨e L / e ℓ, ?_⟩
    have hL : L = (e L / e ℓ) • ℓ := by
      apply e.injective
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ heℓ]
    exact congrArg Subtype.val hL
  have hψ : ψ.complex ≠ 1 := by
    intro hz
    apply ψ.nontrivial
    ext x
    exact DFunLike.congr_fun hz x
  have hcov :
      ∀ u q : Langlands.GeneralLinear (n + 1) F.Carrier,
        ((∀ i j, j < i → u.val i j = 0) ∧ ∀ i, u.val i i = 1) →
        (∀ a, q.val (Fin.last n) a = if a = Fin.last n then 1 else 0) →
        φ.val (u * q) =
          (∏ i : Fin n, ψ.complex (u.val i.castSucc i.succ)) * φ.val q := by
    intro u q hu _
    simpa only [standardCharacter_eq_product] using
      φ.property (⟨u, hu⟩ : upperUnipotent (n + 1) F.Carrier) q
  have hsupp :
      ∃ C : Set (Langlands.GeneralLinear (n + 1) F.Carrier), IsCompact C ∧
        ∀ q : Langlands.GeneralLinear (n + 1) F.Carrier,
          (∀ a, q.val (Fin.last n) a = if a = Fin.last n then 1 else 0) →
          φ.val q ≠ 0 →
          ∃ u c : Langlands.GeneralLinear (n + 1) F.Carrier,
            ((∀ i j, j < i → u.val i j = 0) ∧ ∀ i, u.val i i = 1) ∧
              c ∈ C ∧ q = u * c := by
    obtain ⟨C, hC, hsupport⟩ := hφ.2
    refine ⟨C, hC, ?_⟩
    intro q hq hne
    obtain ⟨u, c, hc, huc⟩ := hsupport q hq hne
    exact ⟨u.val, c, u.property, hc, huc⟩
  obtain ⟨v, hv⟩ := h p hp F n V π ψ.complex
    ψ.continuous_complex hψ ψ.norm_complex hπ.1 hπ.2.1 ℓ.val hℓ
    (fun g hg v =>
      (mem_glFunctionals_iff_entrywise ψ π ℓ.val).mp ℓ.property g hg.1 hg.2 v)
    (fun ℓ' hℓ' => huniq ℓ' (fun g hlow hdiag => hℓ' g ⟨hlow, hdiag⟩))
    φ.val ⟨hcov, hφ.1, hsupp⟩
  exact ⟨modelMap π ℓ v, hv⟩

end Langlands.Whittaker
