import Langlands.AlgebraicGeometry.Picard.MumfordBundle
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Extension of self-product line bundles over a discrete valuation ring -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- Every line bundle on the generic self-product of an abelian scheme over a
discrete valuation ring extends to its total self-product. This defines the
proposition; it does not prove it. -/
def DiscreteValuationRingSelfProductLineBundleExtensionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (A : AbelianScheme (Spec (CommRingCat.of R))),
    let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
    let B := (baseChange b).obj A
    let π := pullback.fst A.X.hom b
    let q := pullback.map B.X.hom B.X.hom A.X.hom A.X.hom
      π π b pullback.condition.symm pullback.condition.symm
    ∀ (D : LineBundle (mumfordProduct B).left),
      ∃ E : LineBundle (mumfordProduct A).left,
        Nonempty (((LineBundle.pullback q).obj E).obj ≅ D.obj)

end Langlands.AbelianScheme
