import Langlands.AlgebraicGeometry.Modules.IntegralAmpleEulerCoefficientProof
import Langlands.AlgebraicGeometry.Modules.CoherentEulerFiltration
import Langlands.AlgebraicGeometry.Modules.CoherentEulerPushforward

/-! # Ample coefficients from integral ideal filtrations -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- A nonzero coherent integral ideal satisfies the successor-dimensional
coefficient criterion once the lower-dimensional criterion is known. -/
theorem eulerCoefficientDetectsSupport_integral_ideal
    (d : ℕ) (ih : AmpleCoherentEulerCoefficientInDimension.{u} d)
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    [IsNoetherian X] [X.IsSeparated]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (I : X.Modules) [I.IsQuasicoherent] (hI : HasFiniteAffineSections I)
    (ι : I ⟶ structureModule X) [Mono ι] (hne : ¬ IsZero I)
    (L : Picard.LineBundle X) (hL : L.IsAmple)
    (hS : HasSupportDimensionLT I (d + 1 + 1)) :
    EulerCoefficientDetectsSupport f I hI L (d + 1) := by
  by_cases hsmall : HasSupportDimensionLT I (d + 1)
  · have hz := coherentEulerPolynomial_coeff_eq_zero_of_supportDimensionLT
      f I hI L (d + 1) hsmall
    constructor
    · rw [hz]
    · rw [hz]
      exact iff_of_false (lt_irrefl _) (fun h => h hsmall)
  · have hXle : topologicalKrullDim X ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := by
      apply ENat.WithBot.lt_add_one_iff.mp
      have hlt := (hasSupportDimensionLT_iff_supportDimension I (d + 1 + 1)).mp hS
      rw [supportDimension_ideal X I ι hne] at hlt
      simpa only [Nat.cast_add, Nat.cast_one] using hlt
    have hXge : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X := by
      apply le_of_not_gt
      intro hlt
      apply hsmall
      apply (hasSupportDimensionLT_iff_supportDimension I (d + 1)).mpr
      rwa [supportDimension_ideal X I ι hne]
    have hpos := integral_lineBundleEulerPolynomial_coeff_pos
      d ih K X f L hL (le_antisymm hXle hXge)
    have heq := coherentEulerPolynomial_ideal_coeff_eq_structureModule
      f I hI ι hne L (d + 1) hXle
    have hIpos : 0 < (coherentEulerPolynomial f I hI L (d + 1)).coeff (d + 1) := by
      rwa [heq]
    exact ⟨hIpos.le, iff_of_true hIpos hsmall⟩

/-- Closed pushforward transports the integral-ideal coefficient criterion
using the actual projection formula and equality of support dimensions. -/
theorem eulerCoefficientDetectsSupport_closed_ideal
    (d : ℕ) (ih : AmpleCoherentEulerCoefficientInDimension.{u} d)
    (K : Type u) [Field K] (X : Scheme.{u})
    [IsNoetherian X] [X.IsSeparated]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (I : Z.Modules) [I.IsQuasicoherent] (hI : HasFiniteAffineSections I)
    (ι : I ⟶ structureModule Z) [Mono ι] (hne : ¬ IsZero I)
    (hP : HasFiniteAffineSections ((Scheme.Modules.pushforward i).obj I))
    (L : Picard.LineBundle X) (hL : L.IsAmple)
    (hS : HasSupportDimensionLT ((Scheme.Modules.pushforward i).obj I) (d + 1 + 1)) :
    letI := QuasicoherentLocal.isQuasicoherent_pushforward i I
    EulerCoefficientDetectsSupport f ((Scheme.Modules.pushforward i).obj I)
      hP L (d + 1) := by
  let : ((Scheme.Modules.pushforward i).obj I).IsQuasicoherent :=
    QuasicoherentLocal.isQuasicoherent_pushforward i I
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  let : CompactSpace Z := i.isClosedEmbedding.compactSpace
  let : IsNoetherian Z := ⟨⟩
  let : Z.IsSeparated := ⟨by
    rw [← terminal.comp_from i]
    infer_instance⟩
  have hZ := (hasSupportDimensionLT_pushforward_iff i i.isClosedEmbedding I
    (d + 1 + 1)).mp hS
  have hpos := eulerCoefficientDetectsSupport_integral_ideal d ih K Z (i ≫ f)
    I hI ι hne ((Picard.LineBundle.pullback i).obj L)
    (Picard.closedImmersionPullbackAmple X Z i L inferInstance hL) hZ
  unfold EulerCoefficientDetectsSupport at hpos ⊢
  rw [coherentEulerPolynomial_pushforward f i I hI hP L (d + 1),
    hasSupportDimensionLT_pushforward_iff i i.isClosedEmbedding I (d + 1)]
  exact hpos

/-- An actual finite integral-ideal filtration propagates the successor
criterion from its graded factors to every coherent sheaf. -/
theorem ampleCoherentEulerCoefficient_succ
    (hfil : CoherentIntegralIdealFiltrationStatement.{u})
    (d : ℕ) (ih : AmpleCoherentEulerCoefficientInDimension.{u} d) :
    AmpleCoherentEulerCoefficientInDimension.{u} (d + 1) := by
  classical
  intro K _ X f _ _ _ M _ hM L hL hS
  obtain ⟨n, T, h0, ⟨iM⟩, hcoh, hstep⟩ := hfil X M inferInstance hM
  choose Z i hi hZ I ι hι hIc hI hne α β hcomp hshort using hstep
  let F : CoherentFiltration X n :=
    { term := T
      factor := fun j => (Scheme.Modules.pushforward (i j)).obj (I j)
      zero := h0
      inclusion := α
      projection := β
      comp_zero := hcomp
      shortExact := hshort
      term_quasicoherent := fun j => (hcoh j).1
      term_finite := fun j => (hcoh j).2
      factor_quasicoherent := fun j => by
        let : IsClosedImmersion (i j) := hi j
        let : (I j).IsQuasicoherent := hIc j
        exact QuasicoherentLocal.isQuasicoherent_pushforward (i j) (I j)
      factor_finite := fun j => by
        let : IsClosedImmersion (i j) := hi j
        exact (hI j).pushforward (i j) }
  have hfactor : ∀ j, HasSupportDimensionLT (F.factor j) (d + 1 + 1) :=
    (F.hasSupportDimensionLT_iff (d + 1 + 1)).mp (hS.of_iso iM.symm)
  apply F.coherentEulerPolynomial_coeff_nonneg_and_pos_iff_of_iso f M hM iM L (d + 1)
  intro j
  let : IsClosedImmersion (i j) := hi j
  let : IsIntegral (Z j) := hZ j
  let : (I j).IsQuasicoherent := hIc j
  let : Mono (ι j) := hι j
  exact eulerCoefficientDetectsSupport_closed_ideal d ih K X f
    (Z j) (i j) (I j) (hI j) (ι j) (hne j)
    (F.factor_finite j) L hL (hfactor j)

/-- Finite integral-ideal filtrations imply the ample coefficient criterion
in every finite support dimension, including the zero sheaf. -/
theorem ampleCoherentEulerCoefficientReduction :
    AmpleCoherentEulerCoefficientReductionStatement.{u} := by
  intro hfil d
  induction d with
  | zero =>
      intro K _ X f _ _ _ M _ hM L _ hS
      exact eulerCoefficientDetectsSupport_zero f M hM L hS
  | succ d ih =>
      exact ampleCoherentEulerCoefficient_succ hfil d ih

end Langlands.AlgebraicGeometry.Modules.DerivedSections
