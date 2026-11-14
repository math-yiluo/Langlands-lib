import Langlands.Geometry.Building.QuasiSplitIndivisibleDerivativeLiftsStatement
import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceProof
import Langlands.Geometry.Building.IntegerOmegaApartmentUniqueness
import Langlands.Geometry.Building.IntegerCentralizerRepresentative

/-! # Reduction of arbitrary compatible lifts to one actual apartment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace IntegerValuation

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {D E : KPApartmentData i (order v)} {C C' : CentralizerDatum i}

/-- The full derivative-lift property is the same for any two compatible
classes, even with distinct representatives of the actual centralizer. -/
theorem IsOmegaCompatible.hasIndivisibleDerivativeLifts_iff
    (hD : IsOmegaCompatible v D C) (hE : IsOmegaCompatible v E C')
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) :
    AffineRootSystem.HasIndivisibleDerivativeLifts D.affineRoots ↔
      AffineRootSystem.HasIndivisibleDerivativeLifts E.affineRoots := by
  have hDE : D = E :=
    hD.eq_of_isMaximalSplitTorus hE.changeCentralizer hG hi
  subst E
  rfl

end IntegerValuation

/-- Existence of one actual compatible quasi-split apartment with full
indivisible derivative lifts. The apartment and centralizer are constructed,
rather than added to the field and group hypotheses. -/
def QuasiSplitIndivisibleApartmentExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (v : Valuation k (WithZero (Multiplicative ℤ))),
    Function.Surjective v →
    HenselianLocalRing v.valuationSubring →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
      IsQuasiSplit G →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k)))
        (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
        letI := mono_of_isMaximalSplitTorus hi
        ∃ (D : KPApartmentData i (IntegerValuation.order v))
          (C : CentralizerDatum i),
          IntegerValuation.IsOmegaCompatible v D C ∧
            AffineRootSystem.HasIndivisibleDerivativeLifts D.affineRoots

/-- A single actual compatible lift construction suffices for the target
quantifying over every compatible apartment and centralizer. -/
theorem quasiSplitIndivisibleDerivativeLifts_of_existence
    (h : QuasiSplitIndivisibleApartmentExistenceStatement.{u}) :
    QuasiSplitIndivisibleDerivativeLiftsStatement.{u} := by
  intro k _ v hv hh G _ hG S i hi
  let := mono_of_isMaximalSplitTorus hi
  intro D C hD
  obtain ⟨E, C', hE, hlift⟩ := h k v hv hh G hG S i hi
  exact (hD.hasIndivisibleDerivativeLifts_iff hE hG.isConnectedReductive hi).mpr hlift

/-- Published quasi-split apartment existence makes the existential
construction condition equivalent to the full arbitrary-apartment target. -/
theorem quasiSplitIndivisibleDerivativeLifts_iff_existence :
    QuasiSplitIndivisibleDerivativeLiftsStatement.{u} ↔
      QuasiSplitIndivisibleApartmentExistenceStatement.{u} := by
  refine ⟨?_, quasiSplitIndivisibleDerivativeLifts_of_existence⟩
  intro h k _ v hv hh G _ hG S i hi
  let := mono_of_isMaximalSplitTorus hi
  obtain ⟨D, C, hD⟩ := quasiSplitIntegerApartmentExistence k v hv hh G hG S i hi
  exact ⟨D, C, hD, h k v hv hh G hG S i hi D C hD⟩

end Langlands.Geometry.Building
