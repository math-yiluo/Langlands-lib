import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ResidueField

/-! # The reduced induced closed subscheme on a closed set -/

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.ReducedSubscheme

variable {X : Scheme.{u}}

/-- The closed subscheme cut out by the vanishing ideal of a closed set is reduced. -/
theorem isReduced_vanishingIdeal_subscheme (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hred : ∀ U : X.affineOpens, IsReduced (Spec (CommRingCat.of (Γ(X, U) ⧸ I.ideal U))) := by
    intro U
    have hrad : (I.ideal U).IsRadical := by
      change ((Scheme.IdealSheafData.vanishingIdeal Z).ideal U).IsRadical
      rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    have : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp hrad
    infer_instance
  have : ∀ i, IsReduced (I.subschemeCover.openCover.X i) := hred
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

theorem range_subschemeι_vanishingIdeal (Z : Closeds X) :
    Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = Z := by
  rw [Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- A quasi-compact morphism from a reduced scheme whose range lies in a closed set factors
through the reduced induced closed subscheme on it. -/
theorem exists_lift_vanishingIdeal {T : Scheme.{u}} [IsReduced T] (g : T ⟶ X) [QuasiCompact g]
    (Z : Closeds X) (h : Set.range g ⊆ Z) :
    ∃ g' : T ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
      g' ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = g := by
  have hle : Scheme.IdealSheafData.vanishingIdeal Z ≤ g.ker := by
    rw [Scheme.IdealSheafData.le_def]
    intro U s hs
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal] at hs
    apply eq_zero_of_basicOpen_eq_bot
    rw [← Scheme.preimage_basicOpen]
    ext t
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro ht
    have htU : g t ∈ (U : X.Opens) := X.basicOpen_le s ht
    have hfrom := U.2.fromSpec_primeIdealOf ⟨g t, htU⟩
    have hZ : U.2.primeIdealOf ⟨g t, htU⟩ ∈ U.2.fromSpec ⁻¹' (Z : Set X) := by
      show U.2.fromSpec (U.2.primeIdealOf ⟨g t, htU⟩) ∈ (Z : Set X)
      rw [hfrom]
      exact h ⟨t, rfl⟩
    have hsp := (PrimeSpectrum.mem_vanishingIdeal _ _).mp hs _ hZ
    have hb : U.2.primeIdealOf ⟨g t, htU⟩ ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := by
      change U.2.fromSpec (U.2.primeIdealOf ⟨g t, htU⟩) ∈ X.basicOpen s
      rw [hfrom]
      exact ht
    rw [U.2.fromSpec_preimage_basicOpen] at hb
    exact hb hsp
  exact ⟨g.toImage ≫ Scheme.IdealSheafData.inclusion hle, by
    rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, Scheme.Hom.toImage_imageι]⟩

end Langlands.AlgebraicGeometry.ReducedSubscheme
