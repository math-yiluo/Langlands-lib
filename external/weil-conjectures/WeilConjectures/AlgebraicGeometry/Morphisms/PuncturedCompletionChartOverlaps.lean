/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionChartSectionModules
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionChartLocalization

/-!
# Localization of actual chart sections on double intersections

## References

* Stacks Project, Tag 0BLH, first two proof paragraphs
* Tag 05EL, item (1)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- Localization identifies actual chart sections with sections on double intersections. -/
theorem exists_chart_overlap_localizations
    {A : Type u} [CommRing A] {Y : Scheme.{u}} (h : Y ⟶ Spec (.of A))
    (t : ℕ) (f : Fin t → A)
    (hV : ∀ i, IsAffineOpen (h ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))) :
    let M := fun i ↦ chartSectionModule h (f i)
    ∃ (alpha_overlap : ∀ i j,
        FormalGlueing.localize (f j) (FormalGlueing.piece (f i) (M i)) ≃ₗ[A]
          FormalGlueing.localize (f i) (FormalGlueing.piece (f j) (M j)))
      (b : ∀ i j, FormalGlueing.localize (f i) (FormalGlueing.piece (f j) (M j)) ≃+
        Γ(Y, (h ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) ⊓
          (h ⁻¹ᵁ PrimeSpectrum.basicOpen (f j)))),
      (∀ i j m, b i j (alpha_overlap i j (LocalizedModule.mk m 1)) =
        Y.presheaf.map (homOfLE inf_le_left).op m) ∧
      (∀ i j m, b i j (LocalizedModule.mk m 1) =
        Y.presheaf.map (homOfLE inf_le_right).op m) ∧
      (∀ i j (a : A) m, b i j (a • m) =
        ((ΓSpecIso (.of A)).inv ≫ h.appTop ≫
          Y.presheaf.map (homOfLE (le_top :
            (h ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) ⊓
              (h ⁻¹ᵁ PrimeSpectrum.basicOpen (f j)) ≤ ⊤)).op).hom a * b i j m) := by
  classical
  dsimp
  let (i j : Fin t) : Module A Γ(Y,
      (h ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) ⊓ (h ⁻¹ᵁ PrimeSpectrum.basicOpen (f j))) :=
    Module.compHom _ ((ΓSpecIso (.of A)).inv ≫ h.appTop ≫
      Y.presheaf.map (homOfLE (le_top :
        (h ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) ⊓
          (h ⁻¹ᵁ PrimeSpectrum.basicOpen (f j)) ≤ ⊤)).op).hom
  choose b hb using fun i j ↦ exists_chart_section_localization h (f i) (f j) (hV j)
    ((h ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) ⊓ (h ⁻¹ᵁ PrimeSpectrum.basicOpen (f j))) rfl
  choose c hc using fun i j ↦ exists_chart_section_localization h (f j) (f i) (hV i)
    ((h ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) ⊓ (h ⁻¹ᵁ PrimeSpectrum.basicOpen (f j)))
    (inf_comm _ _)
  refine ⟨fun i j ↦ (c i j).trans (b i j).symm, fun i j ↦ (b i j).toAddEquiv, ?_,
    ?_, ?_⟩
  · intro i j m
    change b i j ((b i j).symm (c i j (LocalizedModule.mk m 1))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hc i j m
  · exact hb
  · intro i j a m
    exact (b i j).map_smul a m

end AlgebraicGeometry.Scheme.CompletionGluingData
