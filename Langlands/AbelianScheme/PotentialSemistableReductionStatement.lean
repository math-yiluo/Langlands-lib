import Langlands.AbelianScheme.NeronModel
import Langlands.GroupScheme.RelativeIdentityComponent
import Langlands.GroupScheme.Torus.KernelCocharacters

/-! # Potential semistable reduction over a discrete valuation ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Langlands.GroupScheme

namespace Langlands.AbelianScheme

/-- A local extension of discrete valuation rings with the indicated finite
extension of fraction fields. -/
structure FiniteDvrExtension (V K : Type u) [CommRing V] [Field K] [Algebra V K] where
  ring : Type u
  [commRing : CommRing ring]
  [domain : IsDomain ring]
  [dvr : IsDiscreteValuationRing ring]
  [ringAlgebra : Algebra V ring]
  localHom : IsLocalHom (algebraMap V ring)
  fractionField : Type u
  [field : Field fractionField]
  [fractionAlgebra : Algebra ring fractionField]
  [isFractionRing : IsFractionRing ring fractionField]
  [fieldAlgebra : Algebra K fractionField]
  finite : Module.Finite K fractionField
  mapsCommute : (algebraMap ring fractionField).comp (algebraMap V ring) =
    (algebraMap K fractionField).comp (algebraMap V K)

attribute [instance] FiniteDvrExtension.commRing FiniteDvrExtension.domain FiniteDvrExtension.dvr
  FiniteDvrExtension.ringAlgebra FiniteDvrExtension.field FiniteDvrExtension.fractionAlgebra
  FiniteDvrExtension.isFractionRing FiniteDvrExtension.fieldAlgebra

/-- An extension of an abelian variety by a split torus. The torus is the actual
scheme-theoretic kernel of the surjective smooth quotient map. -/
structure SplitSemiabelianPresentation {k : Type u} [Field k]
    (G : CommGroupScheme (Spec (CommRingCat.of k))) where
  torusRank : ℕ
  quotient : AbelianScheme (Spec (CommRingCat.of k))
  quotientMap : G ⟶ quotient.toCommGroupScheme
  smooth : Smooth (CommGroupScheme.hom quotientMap)
  surjective : Surjective (CommGroupScheme.hom quotientMap)
  torusIso : splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift.{u} (Fin torusRank)) ≅
    CommGroupScheme.kernel quotientMap

/-- The geometric special identity component of the actual Néron model is
an extension of an abelian variety by a split torus. -/
def NeronModel.HasGeometricSemiabelianReduction {V K : Type u} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    {B : AbelianScheme (Spec (CommRingCat.of K))} (N : NeronModel V K B) : Prop :=
  ∃ (J : CommGroupScheme (Spec (CommRingCat.of
        (AlgebraicClosure (IsLocalRing.ResidueField V))))) (i : J ⟶ N.geometricSpecialFibre),
    IsRelativeIdentityComponent N.geometricSpecialFibre.toGrp (CommGroupScheme.groupHom i) ∧
      Nonempty (SplitSemiabelianPresentation J)

/-- After a finite extension of the fraction field and a local extension of
DVRs, the actual base-changed abelian variety has a Néron model with semiabelian
geometric special identity component. -/
def PotentialSemistableReductionStatement : Prop :=
  ∀ (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (B : AbelianScheme (Spec (CommRingCat.of K))),
    ∃ (E : FiniteDvrExtension V K)
      (N : NeronModel E.ring E.fractionField
        ((baseChange (Spec.algebraMap K E.fractionField)).obj B)),
      N.HasGeometricSemiabelianReduction

end Langlands.AbelianScheme
