import Langlands.Representation.Derivative.LeibnizRestrictionCompat
import Langlands.Representation.Derivative.MirabolicProductRestriction
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof

/-! The actual differentiated restriction sequence used by the Leibniz proof. -/

noncomputable section
open CategoryTheory

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

open MirabolicProductRestriction

private theorem order_mapsShortExact (T : F.TopologicalData)
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
  restrictionQuotient T m n ⋙
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
  let eL : restrictionSubobject.{uF, uV} T m n ⋙ J ⋙ SmoothRep.toRep ≅
      leibnizRestrictionDerivativeSubobject T ψ m n d hd :=
    eqToIso (by simp only [J, Functor.assoc, generalLinearRankCast_toRep]) ≪≫
      leibnizRestrictionSubobjectSourceIso T ψ m n d hd
  let eM : restrictedProduct.{uF, uV} T m n ⋙ J ⋙ SmoothRep.toRep ≅
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

end Langlands.Derivative
