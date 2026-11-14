import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductRestrictionStatement
import Langlands.Representation.Derivative.MirabolicProductRestrictionCasts

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductRestrictionCasts`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductRestrictionCasts` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous MirabolicProductRestrictionStatement generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
open Langlands.GeneralLinear
universe uF uV uW uD vD

variable {F : LocalFieldPackage.{uF}}

namespace MirabolicProductRestriction
open Langlands.Derivative.MirabolicProductRestriction hiding exists_exact_comp_mirabolicRankCast generalLinearRankCast_comp_restriction mirabolicRankCast_comp mirabolicRankCast_eq_pullback restrictedProduct restrictedProduct_eq restrictionQuotient restrictionQuotient_eq restrictionSubobject restrictionSubobject_eq
/-- Restriction after a rank cast is restriction followed by the mirabolic cast. -/
theorem generalLinearRankCast_comp_restriction (T : F.TopologicalData) {c d : ℕ}
    (h : c = d) (h' : c + 1 = d + 1) :
    letI := T.topology
    generalLinearRankCast.{uF, uW} T h' ⋙ generalLinearRestriction T d =
      generalLinearRestriction T c ⋙ mirabolicRankCast T h := by
  subst h
  rfl

/-- Two successive mirabolic rank casts are one cast. -/
theorem mirabolicRankCast_comp (T : F.TopologicalData) {a b c : ℕ} (h : a = b)
    (h' : b = c) :
    letI := T.topology
    mirabolicRankCast.{uF, uW} T h ⋙ mirabolicRankCast T h' =
      mirabolicRankCast T (h.trans h') := by
  subst h h'
  rfl

/-- Exactness data on functors to `P_(c+1)` give exactness data after a rank cast. -/
theorem exists_exact_comp_mirabolicRankCast (T : F.TopologicalData)
    {D : Type uD} [Category.{vD} D] {c d : ℕ} (h : c = d)
    {F₁ F₂ F₃ : letI := T.topology
      D ⥤ SmoothRep.{0, uF, uW} ℂ (mirabolic c F.Carrier)}
    (H : letI := T.topology
      ∃ (i : F₁ ⟶ F₂) (q : F₂ ⟶ F₃), ∀ X, ExactAt (i.app X) (q.app X)) :
    letI := T.topology
    ∃ (i : F₁ ⋙ mirabolicRankCast T h ⟶ F₂ ⋙ mirabolicRankCast T h)
      (q : F₂ ⋙ mirabolicRankCast T h ⟶ F₃ ⋙ mirabolicRankCast T h),
      ∀ X, ExactAt (i.app X) (q.app X) := by
  subst h
  exact H

/-- The mirabolic rank cast is pullback along `mirabolicCast`. -/
theorem mirabolicRankCast_eq_pullback (T : F.TopologicalData) {c d : ℕ} (h : c = d) :
    letI := T.topology
    mirabolicRankCast.{uF, uW} T h =
      MixedProductTensor.pullbackFunctor (mirabolicCast (K := F.Carrier) h.symm).toMonoidHom
        (mirabolicCast (K := F.Carrier) h.symm).continuous := by
  subst h
  rfl

variable (T : F.TopologicalData) (m n : ℕ)

theorem restrictedProduct_eq :
    letI := T.topology
    restrictedProduct.{uF, uV} T m n =
      T.binaryNormalizedProductFunctor (m + 1) (n + 1) ⋙
        generalLinearRestriction T ((m + 1) + n) ⋙
          mirabolicRankCast T (show (m + 1) + n = m + n + 1 by omega) := by
  let := T.topology
  change T.binaryNormalizedProductFunctor (m + 1) (n + 1) ⋙
      (generalLinearRankCast T (show (m + 1) + n + 1 = (m + n + 1) + 1 by omega) ⋙
        generalLinearRestriction T (m + n + 1)) = _
  rw [generalLinearRankCast_comp_restriction T (show (m + 1) + n = m + n + 1 by omega)]

theorem restrictionSubobject_eq :
    letI := T.topology
    restrictionSubobject.{uF, uV} T m n =
      ((generalLinearRestriction T m).prod
          (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier))) ⋙
        T.rightMixedProductFunctor (n + 1) m ⋙
          MixedProductTensor.pullbackFunctor
            (mirabolicCast (K := F.Carrier) (show (n + 1) + m = (m + 1) + n by omega).symm).toMonoidHom
            (mirabolicCast (K := F.Carrier) (show (n + 1) + m = (m + 1) + n by omega).symm).continuous) ⋙
        mirabolicRankCast T (show (m + 1) + n = m + n + 1 by omega) := by
  let := T.topology
  change _ ⋙ T.rightMixedProductFunctor (n + 1) m ⋙
      mirabolicRankCast T (show (n + 1) + m = m + n + 1 by omega) = _
  rw [← mirabolicRankCast_comp T (show (n + 1) + m = (m + 1) + n by omega)
    (show (m + 1) + n = m + n + 1 by omega),
    mirabolicRankCast_eq_pullback T (show (n + 1) + m = (m + 1) + n by omega)]
  rfl

theorem restrictionQuotient_eq :
    letI := T.topology
    restrictionQuotient.{uF, uV} T m n =
      ((𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))).prod
          (generalLinearRestriction T n) ⋙
        T.leftMixedProductFunctor (m + 1) n) ⋙
        mirabolicRankCast T (show (m + 1) + n = m + n + 1 by omega) := rfl

end MirabolicProductRestriction
end Langlands.AllFieldBZ.Derivative
