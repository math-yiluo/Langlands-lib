import Langlands.GroupScheme.Rational.QuasiSplitRegularClassRationalStatement
import Langlands.GroupScheme.Rational.QuasiSplitSteinbergQuotientStatement
import Langlands.GroupScheme.Torus.RationalDensity
import Langlands.GroupScheme.BaseChangeReflection

/-! # Reduction: rational points of strongly regular classes from Steinberg's class quotient -/

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every morphism between spectra of fields is an epimorphism: it is the spectrum of a field
extension, hence flat and surjective. -/
theorem epi_spec_field {E L : Type u} [Field E] [Field L]
    (f : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L)) : Epi f := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  let _ : Algebra L E := φ.hom.toAlgebra
  have hφ : φ = CommRingCat.ofHom (algebraMap L E) := rfl
  obtain ⟨h1, h2, -⟩ := fieldExtension_fpqc L E
  rw [hφ]
  exact Flat.epi_of_flat_of_surjective _

/-- **Reduction of Borel–Springer 8.6 to Steinberg's class quotient.** If every simply
connected quasi-split group admits a class quotient `ρ : G → V` as in
`QuasiSplitSteinbergQuotientStatement`, then every Galois-stable strongly regular geometric
conjugacy class of such a group contains a rational point. -/
def QuasiSplitRegularClassRationalReductionStatement : Prop :=
  QuasiSplitSteinbergQuotientStatement.{u} → QuasiSplitRegularClassRationalStatement.{u}

/-- Proof of the reduction: the point `z ≫ ρ` of `V` is Galois-fixed, so it descends to a
`K`-point; this is the image of a `K`-point `x` of `G`, and `x` is conjugate to `z` because both
lie in a strongly regular fibre of `ρ`. -/
theorem quasiSplitRegularClassRationalReduction :
    QuasiSplitRegularClassRationalReductionStatement.{u} := by
  intro h K L _ _ _ _ _ G hsc hqs z S j hS hj hcent hstab
  obtain ⟨V, ρ, hinv, hsep, hrat⟩ := h K G hsc hqs
  -- The `L`-point `z ≫ ρ` of `V` is fixed by `Gal(L/K)`.
  have hfix : ∀ σ : L ≃ₐ[K] L,
      TorusDensity.specGal σ ≫ (z ≫ ρ).left = (z ≫ ρ).left := by
    intro σ
    obtain ⟨E, _, _, q, g, hg⟩ := hstab
      (Over.homMk (TorusDensity.specGal σ) (TorusDensity.specGal_comp_specBase σ))
    have h1 := hinv g (q ≫ z)
    rw [hg] at h1
    have h2 := congrArg CommaMorphism.left h1
    simp only [Over.comp_left, Over.homMk_left, Category.assoc] at h2
    have := epi_spec_field q.left
    exact (cancel_epi q.left).1 h2
  -- Galois descent gives a `K`-point `v` of `V`.
  obtain ⟨v, hv⟩ := TorusDensity.exists_rationalPoint_of_fixed V (z ≫ ρ).left
    (Over.w (z ≫ ρ)) hfix
  have hvz : toUnit _ ≫ v = z ≫ ρ := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, ← hv]
    congr 1
  -- Steinberg's rationality: `v` is the image of a `K`-rational point `x`.
  obtain ⟨x, hx⟩ := hrat v L z S j hS hj hcent hvz
  -- Strongly regular fibres are geometric conjugacy classes.
  obtain ⟨E, _, _, q, g, hg⟩ := hsep L (toUnit _ ≫ x) z S j hS hj hcent
    (by rw [Category.assoc, hx, hvz])
  refine ⟨x, E, inferInstance, inferInstance, q, g, ?_⟩
  rw [← Category.assoc, comp_toUnit] at hg
  exact hg

end Langlands.GroupScheme
