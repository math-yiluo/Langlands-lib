import Langlands.AlgebraicGeometry.Picard.MixedLineBundleEuler
import Langlands.AlgebraicGeometry.Picard.IntegralAmpleSectionCokernelProof
import Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingDimensionProof
import Langlands.AlgebraicGeometry.Modules.IntegralSupportDimensionProof

/-! # Mixed Euler coefficients from actual section cokernels -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Langlands.SchemeModule Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

private local instance (X : Scheme.{u}) : (structureModule X).IsQuasicoherent :=
  (LineBundle.trivial X).property.isQuasicoherent

private local instance {X : Scheme.{u}} (N : LineBundle X) : N.obj.IsQuasicoherent :=
  N.property.isQuasicoherent

local instance {X : Scheme.{u}} (N : LineBundle X) (s : GlobalSections N.obj) :
    (cokernel (sectionHom N.obj s)).IsQuasicoherent :=
  QuasicoherentLocal.isQuasicoherent_cokernel (sectionHom N.obj s)

variable {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- The mixed coefficient is nonnegative and detects the section cokernel's
failure of the next smaller support bound. This predicate asserts no criterion
without a proof and does not assume that the section has a vanishing point. -/
def MixedEulerCoefficientDetectsSectionSupport (L N : LineBundle X)
    (s : GlobalSections N.obj) (d : ℕ) : Prop :=
  0 ≤ mixedLineBundleEulerCoefficient f L N (d + 1) ∧
    (0 < mixedLineBundleEulerCoefficient f L N (d + 1) ↔
      ¬ HasSupportDimensionLT (cokernel (sectionHom N.obj s)) d)

/-- A generically generating section on an integral scheme identifies the
mixed Euler polynomial with the actual cokernel Euler polynomial at every
common truncation. -/
theorem mixedLineBundleEulerPolynomial_eq_sectionCokernel [IsIntegral X]
    (L N : LineBundle X) (s : GlobalSections N.obj)
    (hs : (trivializationOpen N.obj s : Set X).Nonempty)
    (hQ : HasFiniteAffineSections (cokernel (sectionHom N.obj s))) (d : ℕ) :
    mixedLineBundleEulerPolynomial f L N d =
      coherentEulerPolynomial f (cokernel (sectionHom N.obj s)) hQ L d := by
  let S := ShortComplex.cokernelSequence (sectionHom N.obj s)
  have : S.X₁.IsQuasicoherent := inferInstanceAs (structureModule X).IsQuasicoherent
  have : S.X₂.IsQuasicoherent := inferInstanceAs N.obj.IsQuasicoherent
  have : S.X₃.IsQuasicoherent :=
    inferInstanceAs (cokernel (sectionHom N.obj s)).IsQuasicoherent
  have hadd := coherentEulerPolynomial_add f S
    (shortExact_sectionHom_cokernel N.obj s hs)
    (hasFiniteAffineSections_structureSheaf X) (hasFiniteAffineSections_lineBundle N)
    hQ L d
  change coherentEulerPolynomial f N.obj _ L d =
    lineBundleEulerPolynomial f L d +
      coherentEulerPolynomial f (cokernel (sectionHom N.obj s)) hQ L d at hadd
  unfold mixedLineBundleEulerPolynomial
  rw [hadd, add_sub_cancel_left]

/-- The mixed coefficient agrees with the leading cokernel coefficient at
its support bound; the two truncations are identified by reconstruction. -/
theorem mixedLineBundleEulerCoefficient_eq_sectionCokernel
    [IsIntegral X] [IsNoetherian X] [X.IsSeparated]
    (L N : LineBundle X) (s : GlobalSections N.obj)
    (hs : (trivializationOpen N.obj s : Set X).Nonempty)
    (hQ : HasFiniteAffineSections (cokernel (sectionHom N.obj s))) (d : ℕ)
    (hS : HasSupportDimensionLT (cokernel (sectionHom N.obj s)) (d + 1)) :
    mixedLineBundleEulerCoefficient f L N (d + 1) =
      (coherentEulerPolynomial f (cokernel (sectionHom N.obj s)) hQ L d).coeff d := by
  unfold mixedLineBundleEulerCoefficient
  rw [mixedLineBundleEulerPolynomial_eq_sectionCokernel f L N s hs hQ (d + 1),
    Nat.add_sub_cancel,
    coherentEulerPolynomial_eq_of_supportDimensionLT f
      (cokernel (sectionHom N.obj s)) hQ L (d + 1) d
      (hS.mono (by omega)) hS]

/-- The published ample coherent coefficient criterion applies to the
actual section cokernel and hence to this mixed coefficient. -/
theorem mixedEulerCoefficientDetectsSectionSupport
    [IsIntegral X] [IsNoetherian X] [X.IsSeparated]
    (L N : LineBundle X) (hL : L.IsAmple) (s : GlobalSections N.obj)
    (hs : (trivializationOpen N.obj s : Set X).Nonempty) (d : ℕ)
    (hS : HasSupportDimensionLT (cokernel (sectionHom N.obj s)) (d + 1)) :
    MixedEulerCoefficientDetectsSectionSupport f L N s d := by
  let hQ := (hasFiniteAffineSections_lineBundle N).cokernel (sectionHom N.obj s)
  have hcrit := ampleCoherentEulerCoefficientReduction coherentIntegralIdealFiltration
    d K X f (cokernel (sectionHom N.obj s)) hQ L hL hS
  unfold MixedEulerCoefficientDetectsSectionSupport
  rw [mixedLineBundleEulerCoefficient_eq_sectionCokernel f L N s hs hQ d hS]
  exact hcrit

/-- On a smooth proper geometrically connected scheme in positive relative
dimension, any coefficient bundle with a section having both a frame point
and a nonframe point has positive mixed coefficient against an ample bundle. -/
theorem mixedLineBundleEulerCoefficient_pos_of_section (d : ℕ)
    (hsmooth : SmoothOfRelativeDimension (d + 1) f)
    (hconnected : GeometricallyConnected f)
    (L N : LineBundle X) (hL : L.IsAmple) (s : GlobalSections N.obj)
    (hs : (trivializationOpen N.obj s : Set X).Nonempty)
    (hz : ∃ x : X, x ∉ trivializationOpen N.obj s) :
    0 < mixedLineBundleEulerCoefficient f L N (d + 1) := by
  let : SmoothOfRelativeDimension (d + 1) f := hsmooth
  let : Smooth f := SmoothOfRelativeDimension.smooth (d + 1) f
  let : GeometricallyConnected f := hconnected
  let : GeometricallyIntegral f :=
    Langlands.AbelianScheme.smoothGeometricIntegrality K X f inferInstance hconnected
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : IsNoetherian X := ⟨⟩
  let : X.IsSeparated :=
    (HasAffineProperty.iff_of_isAffine (P := @IsSeparated) (f := f)).mp inferInstance
  have hdim := lineBundleSectionVanishingDimension K X f (d + 1) hsmooth
    inferInstance hconnected N s hs hz
  have hQdim : supportDimension (cokernel (sectionHom N.obj s)) =
      (d : WithBot ℕ∞) := by
    rw [supportDimension_sectionHom_cokernel N s hs]
    apply le_antisymm
    · apply ENat.WithBot.lt_add_one_iff.mp
      apply ENat.WithBot.add_one_le_natCast_iff.mp
      exact hdim.le
    · by_contra h
      have hlt : topologicalKrullDim {x : X // x ∉ trivializationOpen N.obj s} <
          (d : WithBot ℕ∞) := lt_of_not_ge h
      have hle := ENat.WithBot.add_one_le_natCast_iff.mpr hlt
      rw [hdim] at hle
      have : d + 1 ≤ d := by exact_mod_cast hle
      exact Nat.not_succ_le_self d this
  have hQbound : HasSupportDimensionLT (cokernel (sectionHom N.obj s)) (d + 1) := by
    apply (hasSupportDimensionLT_iff_supportDimension _ (d + 1)).mpr
    rw [hQdim]
    exact_mod_cast Nat.lt_succ_self d
  have hQnot : ¬ HasSupportDimensionLT (cokernel (sectionHom N.obj s)) d := by
    intro h
    have hlt := (hasSupportDimensionLT_iff_supportDimension _ d).mp h
    rw [hQdim] at hlt
    exact lt_irrefl _ hlt
  exact (mixedEulerCoefficientDetectsSectionSupport f L N hL s hs d hQbound).2.mpr hQnot

end Langlands.AlgebraicGeometry.Picard
