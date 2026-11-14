import Langlands.Geometry.Building.QuasiSplitIntegerBoundedApartmentExistenceStatement
import Langlands.Geometry.Building.IntegerCentralizerRepresentative
import Langlands.Geometry.Building.IntegerOmegaApartmentUniqueness
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction
import Langlands.Geometry.Building.UnramifiedOneStabilizerBoundedness

/-! # Reducing unramified root boundedness to bounded quasi-split apartments -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

private instance rootBoundedReductionAffine {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- Bounded apartment existence transfers to every supplied full V 6-compatible
class of the same maximal split torus. -/
theorem IntegerValuationBuildingData.isAlgebraicallyBounded_filtration_of_quasiSplit
    (h : QuasiSplitIntegerBoundedApartmentExistenceStatement.{u})
    {k : Type u} [Field k] [ValuativeRel k]
    {v : Valuation k (WithZero (Multiplicative ℤ))} [Valuation.Compatible v]
    (hv : Function.Surjective v) (hH : HenselianLocalRing v.valuationSubring)
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsQuasiSplit G) (B : IntegerValuationBuildingData v G)
    (x : B.Apartment) (a : characterLattice B.S) (ha : a ∈ relativeRoots B.i) :
    IsAlgebraicallyBounded k G.X (B.filtration x a 0 : Set (rationalPoints G)) := by
  obtain ⟨D, C, hD, hbounded⟩ := h k v hv hH G hG B.S B.i B.isMaximalSplitTorus
  have heq : B.apartment = D :=
    B.isOmegaCompatible.eq_of_isMaximalSplitTorus hD.changeCentralizer
      B.isConnectedReductive B.isMaximalSplitTorus
  have hbounded' : ∀ (y : B.apartment.Apartment) a, a ∈ relativeRoots B.i →
      IsAlgebraicallyBounded k G.X
        (B.apartment.filtration y a 0 : Set (rationalPoints G)) := by
    rw [heq]
    exact hbounded
  exact hbounded' x a ha

/-- The two structural inputs suffice for the exact supplied-data unramified
depth-zero root boundedness target. Both inputs remain explicit here. -/
def UnramifiedZeroRootFiltrationBoundedReductionStatement : Prop :=
  HenselianDiscreteQuasiSplitStatement.{u} →
    QuasiSplitIntegerBoundedApartmentExistenceStatement.{u} →
      MaximalUnramified.ZeroRootFiltrationBoundedStatement.{u}

/-- Specialize to the actual inertia fixed field and its prescribed valuative
relation, then identify the supplied class using full V 6 uniqueness. -/
theorem unramifiedZeroRootFiltrationBounded_of_henselianDiscrete_of_boundedApartment :
    UnramifiedZeroRootFiltrationBoundedReductionStatement.{u} := by
  intro hqs hbounded F _ _ _ _ G _ B x a ha
  let : ValuativeRel (inertiaFixedField F) :=
    ValuativeRel.ofValuation (fixedFieldValued F).v
  let : Valuation.Compatible (MaximalUnramified.valuation F) :=
    ⟨fun x y => (MaximalUnramified.valuation_isEquiv F x y).symm⟩
  have hG : IsQuasiSplit G :=
    unramifiedQuasiSplit_of_henselianDiscrete hqs F G B.isConnectedReductive
  exact B.isAlgebraicallyBounded_filtration_of_quasiSplit hbounded
    (MaximalUnramified.valuation_surjective F)
    (MaximalUnramified.valuationSubring_isHenselian F) hG x a ha

end Langlands.Geometry.Building
