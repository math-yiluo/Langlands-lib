import Langlands.Representation.Smooth.Factorization.CyclicSelection
import Langlands.Representation.Smooth.Factorization.CyclicSelectionStatement
import Langlands.Representation.Smooth.Factorization.CyclicExtractionProof
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.RestrictedTensor.TailSmooth

/-! # Selection through coordinate splittings -/

noncomputable section
open scoped Classical

namespace Langlands.FlathSelection

open RestrictedTensor MeasureTheory

universe uI uG uV

/-- A conditional selection adapter. The actual coordinate splittings, the
smooth-tail consequence, and the two-factor extraction theorem remain inputs. -/
theorem selection_of_splittings
    (hextract : TwoFactorCyclicExtractionStatement.{uG, max uI uG, uV})
    (ι : Type uI) (G : ι → Type uG) [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)]
    [∀ i, TotallyDisconnectedSpace (G i)]
    [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    (μ : ∀ i, Measure (G i)) [∀ i, Measure.IsHaarMeasure (μ i)]
    [∀ i, Measure.Regular (μ i)] (H : ∀ i, Subgroup (G i))
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (RestrictedGroup G H) V)
    (hH : ∀ i, IsOpen (H i : Set (G i)) ∧ IsCompact (H i : Set (G i)))
    (hcomm : ∀ᶠ i in Filter.cofinite, SphericalHeckeCommutative (μ i) (H i))
    (hadm : IsAdmissible π) (hirr : π.IsIrreducible)
    (C : ι → Type (max uI uG)) [∀ i, Group (C i)]
    [∀ i, TopologicalSpace (C i)] [∀ i, IsTopologicalGroup (C i)]
    [∀ i, T2Space (C i)] [∀ i, LocallyCompactSpace (C i)]
    [∀ i, TotallyDisconnectedSpace (C i)]
    (split : ∀ i, (G i × C i) ≃ₜ* RestrictedGroup G H)
    (hsplit : ∀ i g, split i (g, 1) = RestrictedProduct.mulSingleMonoidHom H i g)
    (htail : ∀ v : V, ∃ E : Finset ι, v ∈ tailFixedSubmodule H π E) :
    ∃ (E : Finset ι) (v : V), v ≠ 0 ∧
      (∀ g : RestrictedGroup G H,
        (∀ i ∈ E, g i = 1) → (∀ i ∉ E, g i ∈ H i) → π g v = v) ∧
      (∀ i,
        let σ := π.comp (RestrictedProduct.mulSingleMonoidHom H i)
        IsAdmissible (Cyclic.orbitSpan σ v).toRepresentation ∧
          (Cyclic.orbitSpan σ v).toRepresentation.IsIrreducible) ∧
      (∀ i ∉ E,
        let σ := π.comp (RestrictedProduct.mulSingleMonoidHom H i)
        v ∈ fixedVectors σ (H i) ∧
          Module.finrank ℂ
            (fixedVectors (Cyclic.orbitSpan σ v).toRepresentation (H i)) = 1) := by
  classical
  let := hirr
  have : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (RestrictedGroup G H)) π.asModule
  obtain ⟨v, hv0⟩ := exists_ne (0 : V)
  obtain ⟨E₀, hv⟩ := htail v
  have hlocal (i : ι) :
      (π.comp (split i).toMonoidHom).comp (MonoidHom.inl (G i) (C i)) =
        π.comp (RestrictedProduct.mulSingleMonoidHom H i) := by
    ext g x
    change π (split i (g, 1)) x = π (RestrictedProduct.mulSingleMonoidHom H i g) x
    rw [hsplit]
  have ha (i : ι) : IsAdmissible (π.comp (split i).toMonoidHom) :=
    isAdmissible_comp_continuousMulEquiv π (split i) hadm
  have hr (i : ι) : Representation.IsIrreducible (π.comp (split i).toMonoidHom) :=
    (CuspidalSupport.isIrreducible_comp_iff π (split i).toMonoidHom
      (split i).surjective).mpr hirr
  have hrefine : ∀ i x, x ≠ 0 →
      ∃ y : V, y ∈ Cyclic.orbitSpan
          (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) x ∧
        y ≠ 0 ∧ GoodCyclic (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) y := by
    intro i x hx0
    have h := hextract.1 (G i) (C i) V (π.comp (split i).toMonoidHom)
      (ha i) (hr i) x hx0
    rw [hlocal] at h
    exact h
  have hspherical : ∀ᶠ i in Filter.cofinite, ∀ x : V, x ≠ 0 →
      x ∈ fixedVectors (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) (H i) →
      GoodCyclic (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) x ∧
        Module.finrank ℂ (fixedVectors
          (Cyclic.orbitSpan (π.comp (RestrictedProduct.mulSingleMonoidHom H i)) x).toRepresentation
            (H i)) = 1 := by
    filter_upwards [hcomm] with i hi
    intro x hx0 hx
    let U : OpenSubgroup (G i) := ⟨H i, (hH i).1⟩
    have h := hextract.2 (G i) (C i) (μ i) U (hH i).2 V
      (π.comp (split i).toMonoidHom) hi (ha i) (hr i) x hx0
    rw [hlocal] at h
    obtain ⟨hgood, hirred, hdim⟩ := h hx
    exact ⟨⟨hgood, hirred⟩, hdim⟩
  obtain ⟨E, w, _, hw0, hw, hgood, hsph⟩ :=
    select_of_extraction H π E₀ v hv0 hv hrefine hspherical
  exact ⟨E, w, hw0, hw, hgood, hsph⟩

/-- Actual restricted-product topology discharges all inputs except the
published two-factor extraction proposition. -/
theorem selection_of_twoFactorCyclicExtraction
    (hextract : TwoFactorCyclicExtractionStatement.{uG, max uI uG, uV}) :
    FlathCyclicVectorSelectionStatement.{uI, uG, uV} := by
  intro ι G _ _ _ _ _ _ _ _ μ _ _ H V _ _ π hH hcomm hadm hirr
  let C (i : ι) := ComplementGroup H {i}
  let (i : ι) : IsTopologicalGroup (C i) :=
    restrictedGroup_isTopologicalGroup (fun j : {j // j ∉ ({i} : Finset ι)} => H j)
      (fun j => (hH j).1)
  let (i : ι) : LocallyCompactSpace (C i) :=
    restrictedGroup_locallyCompactSpace (fun j : {j // j ∉ ({i} : Finset ι)} => H j)
      (fun j => (hH j).1) (fun j => (hH j).2)
  exact selection_of_splittings hextract ι G μ H V π hH hcomm hadm hirr C
    (fun i => (singletonSplitEquiv H (fun j => (hH j).1) i).symm)
    (fun i g => singletonSplitEquiv_symm_mulSingle H (fun j => (hH j).1) i g)
    (fun v => exists_tail_fixed_of_isSmooth H (fun j => (hH j).1) π hadm.1 v)

end Langlands.FlathSelection

namespace Langlands

universe uI uG uV

/-- Simultaneous cyclic-factor selection in the actual restricted product. -/
theorem flathCyclicVectorSelection :
    FlathCyclicVectorSelectionStatement.{uI, uG, uV} :=
  FlathSelection.selection_of_twoFactorCyclicExtraction
    twoFactorCyclicExtraction.{uG, max uI uG, uV}

end Langlands
