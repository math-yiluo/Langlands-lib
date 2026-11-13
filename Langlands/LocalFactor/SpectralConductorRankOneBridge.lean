import Langlands.LocalFactor.SpectralConductorInduction
import Langlands.LocalFactor.SpectralConductorRankOneStatement
import Langlands.LocalFactor.SpectralConductorEpsilon

/-!
# From the rank-one statement to the class sums of `M/L`

The Galois group of `M/L`, with its actual action on the integer ring of `M`,
is identified with the subgroup of `Gal(M/F)` fixing `L`; inertia and lower
ramification groups correspond. A character of `W_L` presented at `M` descends
to a character of the inertia group of `M/L`, and its inertia Artin sum is the
class sum `lClassSum` of the induction identity.
-/

noncomputable section

namespace Langlands.LocalFactor.SpectralConductor

open Module Ramification Ramification.Padic CommonClosure ConductorExponent Weil.Local
open scoped BigOperators

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
  (L : Extension F) (hLM : L.field ≤ M.toIntermediateField)

/-- The algebra structures of `M` over `L` used in the rank-one statement. -/
abbrev algebraL : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra

abbrev algebraLM : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
  (IntermediateField.inclusion hLM).toAlgebra

/-- An `L`-automorphism of `M` is an `F`-automorphism. -/
def galLtoF :
    letI := algebraLM F M L hLM
    ((absoluteFiniteExtension F M).Carrier ≃ₐ[L.field] (absoluteFiniteExtension F M).Carrier) →*
      GalM F M := by
  letI := algebraLM F M L hLM
  exact
  { toFun := fun σ =>
      { toRingEquiv := σ.toRingEquiv
        commutes' := fun x => σ.commutes (algebraMap F.Carrier L.field x) }
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

theorem galLtoF_apply :
    letI := algebraLM F M L hLM
    ∀ (σ : (absoluteFiniteExtension F M).Carrier ≃ₐ[L.field] (absoluteFiniteExtension F M).Carrier)
      (y : (absoluteFiniteExtension F M).Carrier), galLtoF F M L hLM σ y = σ y := by
  intro σ y
  rfl

abbrev towerLM :
    letI := algebraL F L
    letI := algebraLM F M L hLM
    IsScalarTower (Padic p) L.field (absoluteFiniteExtension F M).Carrier :=
  letI := algebraL F L
  letI := algebraLM F M L hLM
  IsScalarTower.of_algebraMap_eq' rfl

theorem galLtoF_mem_fixingM :
    letI := algebraLM F M L hLM
    ∀ σ : (absoluteFiniteExtension F M).Carrier ≃ₐ[L.field] (absoluteFiniteExtension F M).Carrier,
      galLtoF F M L hLM σ ∈ fixingM F M L := by
  let := algebraLM F M L hLM
  intro σ y hy
  have := σ.commutes (⟨(y : AlgebraicClosure F.Carrier), hy⟩ : L.field)
  rw [galLtoF_apply]
  convert this using 2 <;> exact Subtype.ext rfl

/-- An element of `Gal(M/F)` fixing `L`, as an `L`-automorphism of `M`. -/
def galFtoL (δ : GalM F M) (hδ : δ ∈ fixingM F M L) :
    letI := algebraLM F M L hLM
    (absoluteFiniteExtension F M).Carrier ≃ₐ[L.field] (absoluteFiniteExtension F M).Carrier :=
  letI := algebraLM F M L hLM
  { toRingEquiv := δ.toRingEquiv
    commutes' := fun x => hδ (IntermediateField.inclusion hLM x) x.2 }

theorem galLtoF_galFtoL (δ : GalM F M) (hδ : δ ∈ fixingM F M L) :
    galLtoF F M L hLM (galFtoL F M L hLM δ hδ) = δ := by
  ext y
  rfl

theorem galLtoF_injective : Function.Injective (galLtoF F M L hLM) := by
  let := algebraLM F M L hLM
  intro σ τ h
  ext y
  have := congrArg (fun δ : GalM F M => ((δ y : (absoluteFiniteExtension F M).Carrier) :
    AlgebraicClosure F.Carrier)) h
  exact this

/-- `L`-automorphisms act on the integer ring of `M` as the corresponding
`F`-automorphisms. -/
theorem integerAutomorphism_galLtoF :
    letI := algebraL F L
    letI := algebraLM F M L hLM
    letI := towerLM F M L hLM
    ∀ σ : (absoluteFiniteExtension F M).Carrier ≃ₐ[L.field] (absoluteFiniteExtension F M).Carrier,
      integerAutomorphism (dataM F M) L.field σ =
        integerAutomorphism (dataM F M) F.Carrier (galLtoF F M L hLM σ) := by
  intro σ
  ext x
  rfl

theorem mem_inertia_iff :
    letI := algebraL F L
    letI := algebraLM F M L hLM
    letI := towerLM F M L hLM
    ∀ σ : (absoluteFiniteExtension F M).Carrier ≃ₐ[L.field] (absoluteFiniteExtension F M).Carrier,
      σ ∈ inertia (dataM F M) L.field ↔ galLtoF F M L hLM σ ∈ inertiaM F M := by
  intro σ
  let := algebraL F L
  let := algebraLM F M L hLM
  let := towerLM F M L hLM
  have h : integerAutHom (dataM F M) L.field σ =
      integerAutHom (dataM F M) F.Carrier (galLtoF F M L hLM σ) :=
    integerAutomorphism_galLtoF F M L hLM σ
  change residueHom (dataM F M) L.field σ = 1 ↔
    residueHom (dataM F M) F.Carrier (galLtoF F M L hLM σ) = 1
  unfold residueHom
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h]

theorem mem_lowerRamificationGroup_iff (i : ℕ) :
    letI := algebraL F L
    letI := algebraLM F M L hLM
    letI := towerLM F M L hLM
    ∀ σ : (absoluteFiniteExtension F M).Carrier ≃ₐ[L.field] (absoluteFiniteExtension F M).Carrier,
      σ ∈ lowerRamificationGroup (dataM F M) L.field i ↔
        galLtoF F M L hLM σ ∈ lowerRamificationGroup (dataM F M) F.Carrier i := by
  intro σ
  rw [mem_lowerRamificationGroup, mem_lowerRamificationGroup, integerAutomorphism_galLtoF]

theorem galoisLowerCount_galLtoF (b : ℕ) :
    letI := algebraL F L
    letI := algebraLM F M L hLM
    letI := towerLM F M L hLM
    ∀ σ : (absoluteFiniteExtension F M).Carrier ≃ₐ[L.field] (absoluteFiniteExtension F M).Carrier,
      galoisLowerCount (dataM F M) L.field b σ =
        galoisLowerCount (dataM F M) F.Carrier b (galLtoF F M L hLM σ) := by
  classical
  intro σ
  unfold galoisLowerCount
  congr 1

theorem lowerBound_spec_L :
    letI := algebraL F L
    letI := algebraLM F M L hLM
    letI := towerLM F M L hLM
    ∀ i ≥ lowerBound F M, lowerRamificationGroup (dataM F M) L.field i = ⊥ := by
  intro i hi
  rw [eq_bot_iff]
  intro σ hσ
  rw [mem_lowerRamificationGroup_iff, lowerBound_spec F M i hi, Subgroup.mem_bot] at hσ
  rw [Subgroup.mem_bot]
  exact galLtoF_injective F M L hLM (hσ.trans (map_one _).symm)

section Descent

variable {F M L hLM}
variable (χ : weilSubgroup F L →ₜ* ℂˣ) (hχ : IsPresentedAt F M L χ)

/-- The image in `Gal(M/F)` of an inertia element of `M/L`, as an element of
the inertia group of `M/F`. -/
def inertiaLtoM :
    letI := algebraL F L
    letI := algebraLM F M L hLM
    letI := towerLM F M L hLM
    inertia (dataM F M) L.field → inertiaM F M := by
  letI := algebraL F L
  letI := algebraLM F M L hLM
  letI := towerLM F M L hLM
  exact fun σ => ⟨galLtoF F M L hLM σ.1, (mem_inertia_iff F M L hLM σ.1).mp σ.2⟩

include hχ in
/-- A presented character descends to the inertia group of `M/L`. -/
def descendedCharacter :
    letI := algebraL F L
    letI := algebraLM F M L hLM
    letI := towerLM F M L hLM
    inertia (dataM F M) L.field →* ℂˣ := by
  letI := algebraL F L
  letI := algebraLM F M L hLM
  letI := towerLM F M L hLM
  exact
  { toFun := fun σ => χ (liftL F M L hLM (inertiaLtoM σ) (galLtoF_mem_fixingM F M L hLM σ.1))
    map_one' := by
      apply hχ
      · exact (inertiaSection F M _).2
      · change restrictionM F M (inertiaSection F M _ : localWeilGroup F) = 1
        rw [restrictionM_inertiaSection]
        exact map_one (galLtoF F M L hLM)
    map_mul' := fun σ τ => by
      rw [← map_mul]
      apply hχ.eq
      · exact (inertiaSection F M _).2
      · exact (localInertia F).mul_mem (inertiaSection F M _).2 (inertiaSection F M _).2
      · change restrictionM F M (inertiaSection F M _ : localWeilGroup F) =
          restrictionM F M ((inertiaSection F M _ : localWeilGroup F) *
            (inertiaSection F M _ : localWeilGroup F))
        rw [map_mul, restrictionM_inertiaSection, restrictionM_inertiaSection,
          restrictionM_inertiaSection]
        exact map_mul (galLtoF F M L hLM) σ.1 τ.1 }

theorem descendedCharacter_apply :
    letI := algebraL F L
    letI := algebraLM F M L hLM
    letI := towerLM F M L hLM
    ∀ σ : inertia (dataM F M) L.field, descendedCharacter χ hχ σ =
      χ (liftL F M L hLM (inertiaLtoM σ) (galLtoF_mem_fixingM F M L hLM σ.1)) :=
  fun _ => rfl

/-- The descended character agrees with `χ` in the sense of the rank-one statement. -/
theorem descendedCharacter_compat :
    letI := algebraL F L
    letI := algebraLM F M L hLM
    letI := towerLM F M L hLM
    ∀ (w : weilSubgroup F L), (w : localWeilGroup F) ∈ localInertia F →
      ∀ σ : inertia (dataM F M) L.field,
        (∀ y : (absoluteFiniteExtension F M).Carrier,
          ((σ : (absoluteFiniteExtension F M).Carrier ≃ₐ[L.field]
            (absoluteFiniteExtension F M).Carrier) y : AlgebraicClosure F.Carrier) =
            AlgEquiv.toAlgHom (localProjection F (w : localWeilGroup F))
              (y : AlgebraicClosure F.Carrier)) →
        descendedCharacter χ hχ σ = χ w := by
  intro w hw σ hσ
  rw [descendedCharacter_apply]
  apply hχ.eq
  · exact (inertiaSection F M _).2
  · exact hw
  · change restrictionM F M (inertiaSection F M _ : localWeilGroup F) = _
    rw [restrictionM_inertiaSection]
    ext y
    change ((σ.1 y : (absoluteFiniteExtension F M).Carrier) : AlgebraicClosure F.Carrier) = _
    rw [hσ y, restrictionM_apply]
    rfl

theorem trace_rankOneCharacterRepresentation {G : Type*} [Group G] (ρ : G →* ℂˣ) (g : G) :
    (finrank ℂ ℂ : ℂ) - LinearMap.trace ℂ ℂ (LocalClassField.rankOneCharacterRepresentation ρ g) =
      1 - (ρ g : ℂ) := by
  have h : LocalClassField.rankOneCharacterRepresentation ρ g = (ρ g : ℂ) • LinearMap.id := by
    ext
    simp
  rw [h, LinearMap.map_smul, LinearMap.trace_id, Module.finrank_self]
  simp

/-- The inertia Artin sum of the descended character is the class sum of `M/L`. -/
theorem inertiaArtinConductor_descendedCharacter :
    letI := algebraL F L
    letI := algebraLM F M L hLM
    letI := towerLM F M L hLM
    ((inertiaArtinConductor (dataM F M) L.field
        (LocalClassField.rankOneCharacterRepresentation (descendedCharacter χ hχ)) : ℚ) : ℂ) =
      lClassSum F M L hLM χ := by
  classical
  let := algebraL F L
  let := algebraLM F M L hLM
  let := towerLM F M L hLM
  have hfinG : Finite ((absoluteFiniteExtension F M).Carrier ≃ₐ[L.field]
      (absoluteFiniteExtension F M).Carrier) :=
    automorphismGroup_finite' (E := absoluteFiniteExtension F M) L.field
  let hfin : Fintype (inertia (dataM F M) L.field) := Fintype.ofFinite _
  rw [inertiaArtinConductor_eq_classSum' (dataM F M) L.field hfin _ (lowerBound F M)
    (lowerBound_spec_L F M L hLM)]
  simp only [trace_rankOneCharacterRepresentation]
  have hinj : Function.Injective (fun σ : inertia (dataM F M) L.field =>
      (inertiaLtoM σ : inertiaM F M)) := by
    intro σ τ h
    apply Subtype.ext
    apply galLtoF_injective F M L hLM
    exact congrArg (fun δ : inertiaM F M => (δ : GalM F M)) h
  have hcard : Nat.card (inertia (dataM F M) L.field) = Nat.card (inertiaL F M L) := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun σ => ⟨galLtoF F M L hLM σ.1,
      galLtoF_mem_fixingM F M L hLM σ.1, (mem_inertia_iff F M L hLM σ.1).mp σ.2⟩) ⟨?_, ?_⟩
    · intro σ τ h
      apply Subtype.ext
      apply galLtoF_injective F M L hLM
      exact congrArg (fun δ : inertiaL F M L => (δ : GalM F M)) h
    · rintro ⟨δ, hfix, hin⟩
      refine ⟨⟨galFtoL F M L hLM δ hfix, (mem_inertia_iff F M L hLM _).mpr ?_⟩, ?_⟩
      · rw [galLtoF_galFtoL]; exact hin
      · exact Subtype.ext (galLtoF_galFtoL F M L hLM δ hfix)
  have key : ∀ σ : inertia (dataM F M) L.field,
      (galoisLowerCount (dataM F M) L.field (lowerBound F M) σ : ℂ) *
          (1 - (descendedCharacter χ hχ σ : ℂ)) =
        if hδ : ((inertiaLtoM σ : inertiaM F M) : GalM F M) ∈ fixingM F M L then
          (galoisLowerCount (dataM F M) F.Carrier (lowerBound F M) (inertiaLtoM σ) : ℂ) *
            (1 - χ (liftL F M L hLM (inertiaLtoM σ) hδ))
        else 0 := by
    intro σ
    rw [dite_eq_left (show ((inertiaLtoM σ : inertiaM F M) : GalM F M) ∈ fixingM F M L from
      galLtoF_mem_fixingM F M L hLM σ.1), galoisLowerCount_galLtoF, descendedCharacter_apply]
    rfl
  unfold lClassSum
  rw [hcard]
  congr 1
  refine Finset.sum_bij_ne_zero (fun σ _ _ => inertiaLtoM σ)
    (fun _ _ _ => @Finset.mem_univ _ (inertiaFintype F M) _)
    (fun σ _ _ τ _ _ h => hinj h) ?_ (fun σ _ _ => key σ)
  intro δ _ hδ
  by_cases hfix : (δ : GalM F M) ∈ fixingM F M L
  · let σ : inertia (dataM F M) L.field := ⟨galFtoL F M L hLM δ hfix,
      (mem_inertia_iff F M L hLM _).mpr (by rw [galLtoF_galFtoL]; exact δ.2)⟩
    have hσ : inertiaLtoM σ = δ := Subtype.ext (galLtoF_galFtoL F M L hLM δ hfix)
    refine ⟨σ, @Finset.mem_univ _ hfin _, ?_, hσ⟩
    rw [key σ, hσ]
    exact hδ
  · exact absurd (dite_eq_right (fun h => hfix h)) hδ

include hχ in
/-- The rank-one statement computes the class sum of a presented character. -/
theorem lClassSum_eq_characterConductor (hR : CommonClosureRankOneConductorStatement F)
    (e : ReciprocityFamily F) (he : NormalizedReciprocity F e) :
    lClassSum F M L hLM χ = (characterConductor e L χ : ℂ) := by
  rw [← inertiaArtinConductor_descendedCharacter χ hχ]
  have h := hR e he L M hLM χ (descendedCharacter χ hχ) (descendedCharacter_compat χ hχ)
  have h' := congrArg (fun q : ℚ => (q : ℂ)) h
  simp only [Rat.cast_natCast] at h'
  exact h'

end Descent

end Langlands.LocalFactor.SpectralConductor
