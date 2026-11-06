import Langlands.Geometry.Analytic.StrictTestDomain.IdealCoverDescent

/-! # Refinement transfer for actual strict rational ideal descent -/

noncomputable section

universe u v w

namespace Langlands.Analytic.StrictTestDomain

open CategoryTheory RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {ι : Type v} {κ : Type w}

/-- Extend a prescribed ideal family through chosen actual rational refinement
restrictions, retaining the chosen index function. -/
def refinedIdealFamily (D : ι → RationalData K P) (E : κ → RationalData K P)
    (k : κ → ι) (inc : ∀ j, E j ⟶ D (k j))
    (I : ∀ i, Ideal (D i).algebra) : ∀ j, Ideal (E j).algebra :=
  fun j => (inc j).restriction.closedIdealMap (I (k j))

/-- Refinement transports compatible ideals to compatible ideals. -/
theorem refinedIdealFamily_compatible
    (D : ι → RationalData K P) (E : κ → RationalData K P)
    (k : κ → ι) (inc : ∀ j, E j ⟶ D (k j))
    (I : ∀ i, Ideal (D i).algebra) (hI : CompatibleIdealSections D I) :
    CompatibleIdealSections E (refinedIdealFamily D E k inc I) := by
  intro j l
  rw [refinedIdealFamily, refinedIdealFamily,
    BoundedAlgHom.closedIdealMap_comp, BoundedAlgHom.closedIdealMap_comp]
  apply compatible_ideals_apply _ _ (hI (k j) (k l))
  rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
    Inclusion.restriction_comp_baseMap, BoundedAlgHom.comp_assoc,
    Inclusion.restriction_comp_baseMap, Inclusion.restriction_comp_baseMap]

private theorem refinedIdealFamily_on_pullback
    (D : ι → RationalData K P) (E : κ → RationalData K P)
    (k : κ → ι) (inc : ∀ j, E j ⟶ D (k j))
    (I : ∀ i, Ideal (D i).algebra) (hI : CompatibleIdealSections D I)
    (i : ι) (j : κ) :
    ((E j).pullback (D i).baseMap).baseMap.closedIdealMap (I i) =
      ((E j).comparison (D i).baseMap).closedIdealMap
        (refinedIdealFamily D E k inc I j) := by
  rw [refinedIdealFamily, BoundedAlgHom.closedIdealMap_comp]
  apply compatible_ideals_apply _ _ (hI i (k j))
  rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
    comparison_comp_baseMap]

/-- A point-covering rational refinement preserves the explicit contraction
of a compatible ideal family. -/
theorem idealSectionContraction_refinedIdealFamily (hK : ∃ c : K, 1 < ‖c‖)
    [Finite κ] (D : ι → RationalData K P) (E : κ → RationalData K P)
    (hE : ∀ x : BanachSpectrum P, ∃ j, x ∈ (E j).locus)
    (k : κ → ι) (inc : ∀ j, E j ⟶ D (k j))
    (I : ∀ i, Ideal (D i).algebra) (hI : CompatibleIdealSections D I) :
    idealSectionContraction E (refinedIdealFamily D E k inc I) =
      idealSectionContraction D I := by
  ext a
  rw [mem_idealSectionContraction, mem_idealSectionContraction]
  constructor
  · intro ha i
    apply idealCoverSeparated_of_covers hK (fun j => (E j).pullback (D i).baseMap)
      (fun x => hE (BanachSpectrum.comap (D i).baseMap.toBoundedRingHom x)) (I i)
      ((D i).baseMap a)
    intro j
    rw [refinedIdealFamily_on_pullback D E k inc I hI i j]
    have h := congrArg
      (fun f : BoundedAlgHom K P ((E j).pullback (D i).baseMap).algebra => f a)
      ((E j).comparison_comp_baseMap (D i).baseMap)
    exact h ▸ ((E j).comparison (D i).baseMap).mem_closedIdealMap (ha j)
  · intro ha j
    have h := congrArg (fun f : BoundedAlgHom K P (E j).algebra => f a)
      (inc j).restriction_comp_baseMap
    exact h ▸ (inc j).restriction.mem_closedIdealMap (ha (k j))

namespace IdealCoverDescent

/-- Effectiveness on a finite rational point-covering refinement proves
effectiveness for the original rational family. -/
theorem of_refinement (hK : ∃ c : K, 1 < ‖c‖) [Finite κ]
    (D : ι → RationalData K P) (E : κ → RationalData K P)
    (hEcover : ∀ x : BanachSpectrum P, ∃ j, x ∈ (E j).locus)
    (k : κ → ι) (inc : ∀ j, E j ⟶ D (k j))
    (hE : IdealCoverDescent E) : IdealCoverDescent D := by
  intro I hI i
  let J := refinedIdealFamily D E k inc I
  have hJ := refinedIdealFamily_compatible D E k inc I hI
  have heff := hE J hJ
  have hcontract := idealSectionContraction_refinedIdealFamily hK D E hEcover k inc I hI
  apply (idealCoverSeparated_of_covers hK (fun j => (E j).pullback (D i).baseMap)
    (fun x => hEcover (BanachSpectrum.comap (D i).baseMap.toBoundedRingHom x))).eq_of_extensions
  intro j
  rw [refinedIdealFamily_on_pullback D E k inc I hI i j,
    BoundedAlgHom.closedIdealMap_comp]
  rw [← comparison_comp_baseMap, ← BoundedAlgHom.closedIdealMap_comp,
    ← hcontract]
  exact congrArg (((E j).comparison (D i).baseMap).closedIdealMap) (heff j)

/-- A bijective reindexing preserves effectiveness, using its inverse index
choice as an actual refinement. -/
theorem of_reindex (hK : ∃ c : K, 1 < ‖c‖) [Finite κ]
    (D : ι → RationalData K P)
    (hD : ∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus)
    (e : κ ≃ ι) (hE : IdealCoverDescent (fun j => D (e j))) :
    IdealCoverDescent D := by
  apply of_refinement hK D (fun j => D (e j)) ?_ e (fun j => 𝟙 (D (e j))) hE
  intro x
  obtain ⟨i, hi⟩ := hD x
  exact ⟨e.symm i, by simpa only [Equiv.apply_symm_apply] using hi⟩

end IdealCoverDescent

end Langlands.Analytic.StrictTestDomain
