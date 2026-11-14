import Langlands.AllFieldBZ.Representation.Derivative.GeneralLinearDerivativeExactnessProof
import Langlands.AllFieldBZ.Representation.Derivative.LeibnizRestrictionCompat
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductRestriction
import Langlands.Representation.Derivative.LeibnizRestrictionExact

/-!
# All-field port of `Langlands.Representation.Derivative.LeibnizRestrictionExact`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.LeibnizRestrictionExact` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding GeneralLinearDerivativeExactnessStatement GeneralLinearDerivativeLeibnizFiltrationStatement HasNonzeroDerivative IsHomogeneous MirabolicProductRestrictionStatement RightMixedProductDerivativeFiltrationStatement generalLinearDerivative generalLinearDerivativeExactness generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_mapsShortExact generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCastDerivativeIso generalLinearRankCastRestrictionIso generalLinearRankCast_mapsShortExact generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_toRep generalLinearRankCast_trans generalLinearRepRankCast generalLinearRestriction generalLinearRestrictionDerivativeIso generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap generalLinearRestriction_mapsShortExact hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative leibnizPiece leibnizPiece_obj leibnizPositivePieceIso leibnizPositiveSmoothPieceIso leibnizRestrictedProductSourceIso leibnizRestrictionDerivativeExact leibnizRestrictionDerivativeQuotient leibnizRestrictionDerivativeSubobject leibnizRestrictionSubobjectSourceIso leibnizSource level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_mapsShortExact mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicProductRestriction mirabolicRankCast mirabolicRankCastDerivativeIso mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_mapsShortExact phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero rightMixedDerivativePiece rightMixedDerivativeSource
universe uF uV

variable {F : LocalFieldPackage.{uF}}

open Langlands.Derivative.MirabolicProductRestriction hiding core determinantNorm_mirabolic exists_exact_comp_mirabolicRankCast exists_exact_restrictedCompactInduction factors generalLinearRankCast_comp_restriction inducingFunctor leviHalfModulus_eq_leftLeviCharacter leviHalfModulus_eq_rightLeviCharacter leviInducingFunctor leviModulus_shape midEquiv midEquiv_naturality midFunctor mirabolicRankCast_comp mirabolicRankCast_eq_pullback pair_hT quotEquiv quotEquiv_naturality quotFunctor quot_hE restrictedProduct restrictedProduct_eq restrictionQuotient restrictionQuotient_eq restrictionSubobject restrictionSubobject_eq subEquiv subEquiv_naturality subFunctor sub_hE tensorEquiv topologicalRing
open Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction
private theorem _root_.Langlands.Derivative.order_mapsShortExact (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N d : ℕ) (hd : 0 < d ∧ d ≤ N + 1) :
    letI := T.topology
    Mirabolic.MapsShortExactIntertwiners
      (mirabolicDerivativeOfOrder.{uF, uV} T ψ N d hd) := by
  let _ := T.topology
  have hcast : ∀ {a b : ℕ} (h : a = b),
      Mirabolic.MapsShortExactIntertwiners (mirabolicRankCast.{uF, uV} T h) := by
    intro a b h
    subst b
    exact LevelCalculus.mapsShortExact_id
  exact LevelCalculus.mapsShortExact_comp (hcast _)
    (mirabolicDerivative_mapsShortExact F T ψ (N + 1 - d) (d - 1))

/-- The actual right-mixed derivative source restricted on the first input,
with the common total output rank. -/
def leibnizRestrictionDerivativeSubobject (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n d : ℕ) (hd : 0 < d ∧ d ≤ (m + 1) + (n + 1)) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)) ⥤
      Rep.{max uF uV} ℂ (GeneralLinear (((m + 1) + (n + 1)) - d) F.Carrier) :=
  letI := T.topology
  (generalLinearRestriction T m).prod
      (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier))) ⋙
    rightMixedDerivativeSource T ψ (n + 1) m d (by omega) ⋙
      generalLinearRepRankCast (F := F)
        (show ((n + 1) + m) + 1 - d = ((m + 1) + (n + 1)) - d by omega)

/-- The actual restriction quotient followed by the actual derivative,
smooth output-rank transport and forgetting. -/
def leibnizRestrictionDerivativeQuotient (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n d : ℕ) (hd : 0 < d ∧ d ≤ (m + 1) + (n + 1)) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)) ⥤
      Rep.{max uF uV} ℂ (GeneralLinear (((m + 1) + (n + 1)) - d) F.Carrier) :=
  letI := T.topology
  Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictionQuotient T m n ⋙
    mirabolicDerivativeOfOrder T ψ (m + n + 1) d (by omega) ⋙
      generalLinearRankCast T
        (show (m + n + 1) + 1 - d = ((m + 1) + (n + 1)) - d by omega) ⋙
      SmoothRep.toRep

/-- An unconditional natural short exact sequence with middle term the literal
Leibniz source, obtained by differentiating the actual restriction sequence. -/
theorem leibnizRestrictionDerivativeExact (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n d : ℕ) (hd : 0 < d ∧ d ≤ (m + 1) + (n + 1)) :
    letI := T.topology
    ∃ (i : leibnizRestrictionDerivativeSubobject.{uF, uV} T ψ m n d hd ⟶
        leibnizSource T ψ (m + 1) (n + 1) d hd.2)
      (q : leibnizSource.{uF, uV} T ψ (m + 1) (n + 1) d hd.2 ⟶
        leibnizRestrictionDerivativeQuotient T ψ m n d hd),
      ∀ X, Function.Injective (i.app X).hom ∧
        LinearMap.range (i.app X).hom.toLinearMap =
          LinearMap.ker (q.app X).hom.toLinearMap ∧
        Function.Surjective (q.app X).hom := by
  let _ := T.topology
  let J := mirabolicDerivativeOfOrder.{uF, max uF uV} T ψ (m + n + 1) d
      (by omega) ⋙
    generalLinearRankCast T
      (show (m + n + 1) + 1 - d = ((m + 1) + (n + 1)) - d by omega)
  have hJ : Mirabolic.MapsShortExactIntertwiners J :=
    LevelCalculus.mapsShortExact_comp (order_mapsShortExact T ψ _ _ _)
      (generalLinearRankCast_mapsShortExact F T _)
  let eL : Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictionSubobject.{uF, uV} T m n ⋙ J ⋙ SmoothRep.toRep ≅
      leibnizRestrictionDerivativeSubobject T ψ m n d hd :=
    eqToIso (by simp only [J, Functor.assoc, generalLinearRankCast_toRep]) ≪≫
      leibnizRestrictionSubobjectSourceIso T ψ m n d hd
  let eM : Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictedProduct.{uF, uV} T m n ⋙ J ⋙ SmoothRep.toRep ≅
      leibnizSource T ψ (m + 1) (n + 1) d hd.2 :=
    eqToIso (by simp only [J, Functor.assoc, generalLinearRankCast_toRep]) ≪≫
      leibnizRestrictedProductSourceIso T ψ m n d hd
  obtain ⟨i, q, h⟩ := mirabolicProductRestriction.{uF, uV} F T m n
  let iD := Functor.whiskerRight i (J ⋙ SmoothRep.toRep)
  let qD := Functor.whiskerRight q (J ⋙ SmoothRep.toRep)
  refine ⟨eL.inv ≫ iD ≫ eM.hom, eM.inv ≫ qD, fun X => ?_⟩
  have hX := hJ _ _ _ (i.app X) (q.app X) (h X).1 (h X).2.2 (h X).2.1
  exact exact_of_linearEquiv
    (Representation.equivOfIso (eL.app X).symm).toLinearEquiv
    (Representation.equivOfIso (eM.app X)).toLinearEquiv
    (LinearEquiv.refl ℂ _)
    (iD.app X).hom.toLinearMap (qD.app X).hom.toLinearMap
    hX.1 hX.2.1 hX.2.2

end Langlands.AllFieldBZ.Derivative
