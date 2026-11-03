import Langlands.AbelianScheme.InvertibleMultiplication
import Langlands.AbelianScheme.MultiplicationEtale
import Langlands.CategoryTheory.RationalizationIntegralInverse

/-! # Finite etale isogenies from exact integral inverse-multiple data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

variable {S : Scheme.{u}} {A B : AbelianScheme S}

/-- Both actual maps in positive inverse-multiple data are finite etale isogenies
when their common multiplier is invertible on the base. -/
theorem integralInverseData_finiteEtaleIsogenies
    (d : Rationalization.IntegralInverseData A B) (hpos : 0 < d.multiple)
    (hn : IsUnit (d.multiple : Γ(S, ⊤))) :
    IsIsogeny d.hom ∧ Etale (hom d.hom) ∧
      IsIsogeny d.inv ∧ Etale (hom d.inv) := by
  let n := d.multiple.toNat
  have hcast : (n : ℤ) = d.multiple := Int.toNat_of_nonneg (le_of_lt hpos)
  have hn' : IsUnit (n : Γ(S, ⊤)) := by
    rw [← hcast, Int.cast_natCast] at hn
    exact hn
  have hA : IsIsogeny (d.multiple • 𝟙 A) := by
    rw [← hcast]
    exact multiplication_isIsogeny_of_isUnit A n hn'
  have hB : IsIsogeny (d.multiple • 𝟙 B) := by
    rw [← hcast]
    exact multiplication_isIsogeny_of_isUnit B n hn'
  have : Etale (hom d.hom ≫ hom d.inv) := by
    rw [← hom_comp, d.hom_inv, ← hcast]
    exact multiplication_etale A n hn'
  have : Etale (hom d.inv ≫ hom d.hom) := by
    rw [← hom_comp, d.inv_hom, ← hcast]
    exact multiplication_etale B n hn'
  have : IsFinite (hom d.hom ≫ hom d.inv) := by
    rw [← hom_comp, d.hom_inv]
    exact hA.1
  have : IsFinite (hom d.inv ≫ hom d.hom) := by
    rw [← hom_comp, d.inv_hom]
    exact hB.1
  have : IsSeparated (hom d.hom ≫ B.X.hom) := by
    rw [Over.w]
    infer_instance
  have : IsSeparated (hom d.inv ≫ A.X.hom) := by
    rw [Over.w]
    infer_instance
  have : IsSeparated (hom d.hom) := IsSeparated.of_comp _ B.X.hom
  have : IsSeparated (hom d.inv) := IsSeparated.of_comp _ A.X.hom
  have : IsFinite (hom d.hom) := IsFinite.of_comp _ (hom d.inv)
  have : IsFinite (hom d.inv) := IsFinite.of_comp _ (hom d.hom)
  have : FormallyUnramified (hom d.hom) := FormallyUnramified.of_comp _ (hom d.inv)
  have : FormallyUnramified (hom d.inv) := FormallyUnramified.of_comp _ (hom d.hom)
  have : Etale (hom d.hom) := Etale.of_comp _ (hom d.inv)
  have : Etale (hom d.inv) := Etale.of_comp _ (hom d.hom)
  have hsurjA : Surjective (hom d.hom ≫ hom d.inv) := by
    rw [← hom_comp, d.hom_inv]
    exact hA.2.2
  have hsurjB : Surjective (hom d.inv ≫ hom d.hom) := by
    rw [← hom_comp, d.inv_hom]
    exact hB.2.2
  have : Surjective (hom d.hom) := ⟨fun b => by
    obtain ⟨b', hb'⟩ := hsurjB.surj b
    exact ⟨hom d.inv b', by simpa only [Scheme.Hom.comp_apply] using hb'⟩⟩
  have : Surjective (hom d.inv) := ⟨fun a => by
    obtain ⟨a', ha'⟩ := hsurjA.surj a
    exact ⟨hom d.hom a', by simpa only [Scheme.Hom.comp_apply] using ha'⟩⟩
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩, inferInstance,
    ⟨inferInstance, inferInstance, inferInstance⟩, inferInstance⟩

/-- Retain the exact supplied integral data, bundled with the proved finite etale
isogeny properties of its two maps. -/
def finiteEtaleIntegralInverseData
    (d : Rationalization.IntegralInverseData A B) (hpos : 0 < d.multiple)
    (hn : IsUnit (d.multiple : Γ(S, ⊤))) :
    { e : Rationalization.IntegralInverseData A B //
      IsIsogeny e.hom ∧ Etale (hom e.hom) ∧
        IsIsogeny e.inv ∧ Etale (hom e.inv) } :=
  ⟨d, integralInverseData_finiteEtaleIsogenies d hpos hn⟩

@[simp] theorem finiteEtaleIntegralInverseData_val
    (d : Rationalization.IntegralInverseData A B) (hpos : 0 < d.multiple)
    (hn : IsUnit (d.multiple : Γ(S, ⊤))) :
    (finiteEtaleIntegralInverseData d hpos hn).val = d := rfl

end Langlands.AbelianScheme
