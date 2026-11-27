import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingOpenGroups
import Langlands.Global.LeftCosetSemidirectNormalizedIntegral

/-! # Haar measures on the open cell

The radical `U'(𝔸)`, in additive matrix coordinates, and the block diagonal group
`N_(t+1)(𝔸) × N_(r+1)(𝔸)` have compact quotients by their rational points. Normalizing the three
Haar measures by the masses of their rational quotients, the semidirect product coordinates
`(Y, m) ↦ u'(Y) diag(m)` identify the normalized Haar measure of `N₀(𝔸)` with the product of the
normalized Haar measures of the factors. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open NumberField MeasureTheory Matrix Set

namespace Langlands.Global.CuspidalPairEisenstein.Unfolding

open RankinSelbergGlobal RowEchelon PrimitiveAdelicHeight LeftCosetSpace

variable (F : Type u) [Field F] [NumberField F] (r t : ℕ)

local instance openMeasureAdelesLocallyCompact : LocallyCompactSpace (Adeles F) :=
  adeles_locallyCompactSpace F

local instance openMeasureAdelesSecondCountable : SecondCountableTopology (Adeles F) :=
  adeles_secondCountableTopology F

local instance openMeasureAdelesT2 : T2Space (Adeles F) :=
  GeneralLinearBlockSemidirect.adeleRing_t2Space F

instance radicalLocallyCompact : LocallyCompactSpace (Radical F r t) :=
  inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (r + 1) → Adeles F))

instance radicalSecondCountable : SecondCountableTopology (Radical F r t) :=
  inferInstanceAs (SecondCountableTopology (Fin (t + 1) → Fin (r + 1) → Adeles F))

instance radicalMeasurableSpace : MeasurableSpace (Radical F r t) := borel _

instance radicalBorelSpace : BorelSpace (Radical F r t) := ⟨rfl⟩

/-- A compact set meeting every orbit of `N₀(F)` in `N₀(𝔸)`. -/
theorem exists_isCompact_cover_Γ₀ (n : ℕ) :
    ∃ K : Set (unipotentAdelic F n), IsCompact K ∧ ∀ x, ∃ c ∈ Γ₀ F n, c * x ∈ K := by
  obtain ⟨K, hK, hcover⟩ := exists_isCompact_pattern_cover F n ∅
  refine ⟨Subtype.val '' K, hK.image continuous_subtype_val, fun x => ?_⟩
  have hx : x ∈ pattern F n ∅ := (mem_pattern_iff F n ∅ x).mpr (by simp)
  obtain ⟨c, hc, hcK⟩ := hcover ⟨x, hx⟩
  exact ⟨c, hc, ⟨_, hcK, rfl⟩⟩

theorem isDiscrete_radicalLattice :
    IsDiscrete (((Γ₀ F (r + t + 2)).comap (radicalHom F r t) : Subgroup (Radical F r t)) :
      Set (Radical F r t)) :=
  (isDiscrete_Γ₀ F _).preimage (continuous_radicalHom F r t).continuousOn
    (isEmbedding_radicalHom F r t).injective

theorem isFiniteMeasure_radicalQuotient :
    IsFiniteMeasure (haarQuotientMeasure ((Γ₀ F (r + t + 2)).comap (radicalHom F r t))
      (isDiscrete_radicalLattice F r t)) := by
  obtain ⟨D, hDc, hD⟩ := AdelicGroupPoints.exists_isCompact_algebraMap_add_mem F
  let K : Set (Radical F r t) :=
    Multiplicative.ofAdd '' Set.pi univ fun _ => Set.pi univ fun _ => D
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hDc).image continuous_ofAdd
  refine isFiniteMeasure_haarQuotientMeasure_of_isCompact _ _ hK fun Y => ?_
  choose c hc using fun i j => hD (Y.toAdd i j)
  let C : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F) := fun i j => algebraMap F _ (c i j)
  refine ⟨Multiplicative.ofAdd C, ?_, ⟨C + Y.toAdd, fun i _ j _ => hc i j, rfl⟩⟩
  change radicalHom F r t (Multiplicative.ofAdd C) ∈ Γ₀ F (r + t + 2)
  rw [mem_Γ₀_iff_entries]
  intro i j
  rw [toMat_radicalHom, toAdd_ofAdd, openCellUnipotent_eq_ofSum, toMat_entry_ofSum]
  rcases (swapBlocks r t).symm i with a | a <;> rcases (swapBlocks r t).symm j with b | b
  · exact ⟨if a = b then 1 else 0, by simp [Matrix.one_apply]⟩
  · exact ⟨c a b, rfl⟩
  · exact ⟨0, by simp⟩
  · exact ⟨if a = b then 1 else 0, by simp [Matrix.one_apply]⟩

theorem isFiniteMeasure_leviQuotient :
    IsFiniteMeasure (haarQuotientMeasure (leviLattice F r t) (isDiscrete_leviLattice F r t)) := by
  obtain ⟨K₁, hK₁, h₁⟩ := exists_isCompact_cover_Γ₀ F (t + 1)
  obtain ⟨K₂, hK₂, h₂⟩ := exists_isCompact_cover_Γ₀ F (r + 1)
  refine isFiniteMeasure_haarQuotientMeasure_of_isCompact _ _ (hK₁.prod hK₂) fun m => ?_
  obtain ⟨c₁, hc₁, hm₁⟩ := h₁ m.1
  obtain ⟨c₂, hc₂, hm₂⟩ := h₂ m.2
  exact ⟨(c₁, c₂), ⟨hc₁, hc₂⟩, ⟨hm₁, hm₂⟩⟩

/-- The normalized Haar measures of `N₀(𝔸)`, of the radical and of the block diagonal group. -/
abbrev haarH : Measure (unipotentAdelic F (r + t + 2)) :=
  Semidirect.latticeNormalizedHaar (Γ₀ F (r + t + 2)) (isDiscrete_Γ₀ F _)

abbrev haarN : Measure (Radical F r t) :=
  Semidirect.latticeNormalizedHaar ((Γ₀ F (r + t + 2)).comap (radicalHom F r t))
    (isDiscrete_radicalLattice F r t)

abbrev haarM : Measure (LeviPart F r t) :=
  Semidirect.latticeNormalizedHaar (leviLattice F r t) (isDiscrete_leviLattice F r t)

/-- The product coordinates `(Y, m) ↦ u'(Y) diag(m)` of `N₀(𝔸)`. -/
abbrev openProd : Radical F r t × LeviPart F r t ≃ₜ unipotentAdelic F (r + t + 2) :=
  Semidirect.prodHomeomorph (radicalHom F r t) (leviHom F r t) (projHom F r t)
    (projHom_leviHom F r t) (exists_radicalHom_eq F r t) (projHom_radicalHom F r t)
    (isEmbedding_radicalHom F r t) (continuous_leviHom F r t) (continuous_projHom F r t)

theorem openProd_apply (x : Radical F r t × LeviPart F r t) :
    openProd F r t x = radicalHom F r t x.1 * leviHom F r t x.2 := rfl

/-- **Normalized Haar measure in the open-cell coordinates.** -/
theorem haarH_eq_map_prod :
    haarH F r t = ((haarN F r t).prod (haarM F r t)).map (openProd F r t) := by
  have hN := isFiniteMeasure_radicalQuotient F r t
  have hM := isFiniteMeasure_leviQuotient F r t
  exact Semidirect.semidirectNormalizedHaar (radicalHom F r t) (leviHom F r t) (projHom F r t)
    (projHom_leviHom F r t) (exists_radicalHom_eq F r t) (projHom_radicalHom F r t)
    (isEmbedding_radicalHom F r t) (continuous_leviHom F r t) (continuous_projHom F r t)
    (Γ₀ F (r + t + 2)) (isDiscrete_Γ₀ F _) (leviLattice F r t) (isDiscrete_leviLattice F r t)
    (isDiscrete_radicalLattice F r t) (fun m hm => leviHom_mem_Γ₀ F r t hm)
    (fun h hh => projHom_mem_leviLattice F r t hh) hN hM

end Langlands.Global.CuspidalPairEisenstein.Unfolding
