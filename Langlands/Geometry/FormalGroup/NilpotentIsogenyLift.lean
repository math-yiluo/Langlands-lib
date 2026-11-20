import Langlands.Geometry.FormalGroup.NilpotentOpenBaseChange
import Langlands.Geometry.FormalGroup.IsogenyDual
import Langlands.Geometry.FormalGroup.ScalarCompositesIsogeny

/-! # Lifting integral isogenies up to a scalar power -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {π : O}

namespace Hom

/-- An actual isogeny lifts across a nilpotent thickening after scalar multiplication. -/
theorem IsIsogeny.exists_lift_smul_of_nilpotent (φ : R →ₐ[O] S)
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ.toRingHom))
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π)
    {f₀ : Hom (M.map φ) (N.map φ)} (hf₀ : f₀.IsIsogeny) :
    ∃ (k : ℕ) (f : Hom M N), f.IsIsogeny ∧ f.map φ = π ^ k • f₀ := by
  obtain ⟨j, hj⟩ := hf₀.exists_dual (hM.map φ) (hN.map φ)
  obtain ⟨g₀, -, hgf₀, hfg₀⟩ := hj j le_rfl
  obtain ⟨k, f, hf⟩ := Hom.exists_lift_smul_of_nilpotent φ hφ hI hN.torsion f₀
  obtain ⟨l, g, hg⟩ := Hom.exists_lift_smul_of_nilpotent φ hφ hI hM.torsion g₀
  have hgf : g.comp f = M.scalarHom (π ^ (k + l + j)) := by
    apply map_injective_of_nilpotent φ hφ hI hM hM.torsion
    change (g.comp f).map φ = (M.scalarHom (π ^ (k + l + j))).map φ
    rw [map_comp, hg, hf, smul_comp, comp_smul, hgf₀, scalarHom_map]
    simp only [scalarHom, smul_smul, pow_add, mul_assoc, mul_comm]
  have hfg : f.comp g = N.scalarHom (π ^ (k + l + j)) := by
    apply map_injective_of_nilpotent φ hφ hI hN hN.torsion
    change (f.comp g).map φ = (N.scalarHom (π ^ (k + l + j))).map φ
    rw [map_comp, hf, hg, smul_comp, comp_smul, hfg₀, scalarHom_map]
    simp only [scalarHom, smul_smul, pow_add, mul_assoc]
  exact ⟨k, f, isIsogeny_of_scalarComposites_overRing hM hN hgf hfg, hf⟩

set_option maxHeartbeats 400000 in
/-- Lift an actual isogeny numerator on the inverse image of a basic open. -/
theorem IsIsogeny.exists_openBaseChange_eq_smul_basicOpen (φ : R →ₐ[O] S)
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ.toRingHom))
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) (r : R)
    {f₀ : OpenIntegralHom (M.map φ) (N.map φ)
      ((coefficientOpenMap φ).obj (PrimeSpectrum.basicOpen r))}
    (hf₀ : f₀.IsIsogeny) :
    ∃ (k : ℕ) (f : OpenIntegralHom M N (PrimeSpectrum.basicOpen r)),
      f.IsIsogeny ∧ openBaseChange φ (PrimeSpectrum.basicOpen r) f = π ^ k • f₀ := by
  let U := PrimeSpectrum.basicOpen r
  let α := IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))
  let β := coefficientSectionMap φ U
  let δ := IsScalarTower.toAlgHom O S
    ((coefficientStructurePresheaf S).obj (op ((coefficientOpenMap φ).obj U)))
  let h := coefficientSectionMap_structural φ U
  let eM := mapSquareIso M α β φ δ h
  let eN := mapSquareIso N α β φ δ h
  let g₀ := eN.inv.comp (f₀.comp eM.hom)
  have hg₀ : g₀.IsIsogeny := by
    apply isIsogeny_of_isoSquare f₀ g₀ eM.symm eN.symm _ hf₀
    change (eN.inv.comp (f₀.comp eM.hom)).comp eM.inv = eN.inv.comp f₀
    rw [comp_assoc, comp_assoc, Iso.hom_inv, comp_id]
  obtain ⟨hβ, hker⟩ := coefficientSectionMap_basicOpen_nilpotent φ hφ hI r
  obtain ⟨k, f, hf, he⟩ := hg₀.exists_lift_smul_of_nilpotent β hβ hker (hM.map α) (hN.map α)
  refine ⟨k, f, hf, ?_⟩
  change eN.hom.comp ((f.map β).comp eM.inv) = π ^ k • f₀
  rw [he, smul_comp, comp_smul]
  change π ^ k • eN.hom.comp ((eN.inv.comp (f₀.comp eM.hom)).comp eM.inv) = _
  rw [comp_assoc eN.inv, comp_assoc f₀, Iso.hom_inv, comp_id,
    ← comp_assoc eN.hom, Iso.hom_inv, id_comp]

end Hom

end Langlands.FormalGroup.ModuleLaw
