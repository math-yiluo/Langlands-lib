import Langlands.AbelianScheme.Basic
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

/-! # Néron models with their generic identification -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- An actual commutative Néron model of the given abelian variety over a discrete
valuation ring, with an isomorphism identifying its generic fibre. -/
structure NeronModel (V K : Type u) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (B : AbelianScheme (Spec (CommRingCat.of K))) where
  group : CommGroupScheme (Spec (CommRingCat.of V))
  property : NeronModelInfra.NeronModelPropertyBundle V K group.X.hom
  genericIso : B.toCommGroupScheme ≅
    (CommGroupScheme.baseChange (NeronModelInfra.specGenericFibreInclusion V K)).obj group

/-- The geometric closed point of the spectrum of a local ring, using the algebraic
closure of its residue field. -/
abbrev geometricSpecialPoint (V : Type u) [CommRing V] [IsLocalRing V] :
    Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField V))) ⟶
      Spec (CommRingCat.of V) :=
  Spec.algebraMap (IsLocalRing.ResidueField V)
    (AlgebraicClosure (IsLocalRing.ResidueField V)) ≫
    Spec.algebraMap V (IsLocalRing.ResidueField V)

namespace NeronModel

variable {V K : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]
  {B : AbelianScheme (Spec (CommRingCat.of K))} (N : NeronModel V K B)

/-- The actual group-scheme pullback to the geometric closed point. -/
abbrev geometricSpecialFibre :
    CommGroupScheme (Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField V)))) :=
  (CommGroupScheme.baseChange (geometricSpecialPoint V)).obj N.group

/-- A proper Néron model with geometrically connected fibres is an abelian scheme
with its existing group law. -/
def toAbelianScheme (hproper : IsProper N.group.X.hom)
    (hconn : GeometricallyConnected N.group.X.hom) : AbelianScheme (Spec (CommRingCat.of V)) where
  toCommGroupScheme := N.group
  smooth := N.property.smooth
  proper := hproper
  geometricallyConnected := hconn

/-- The original generic identification is an isomorphism of abelian schemes
when the model is an abelian scheme. -/
def toAbelianSchemeGenericIso (hproper : IsProper N.group.X.hom)
    (hconn : GeometricallyConnected N.group.X.hom) :
    B ≅ (baseChange (NeronModelInfra.specGenericFibreInclusion V K)).obj
      (N.toAbelianScheme hproper hconn) where
  hom := N.genericIso.hom
  inv := N.genericIso.inv
  hom_inv_id := N.genericIso.hom_inv_id
  inv_hom_id := N.genericIso.inv_hom_id

end NeronModel
end Langlands.AbelianScheme
