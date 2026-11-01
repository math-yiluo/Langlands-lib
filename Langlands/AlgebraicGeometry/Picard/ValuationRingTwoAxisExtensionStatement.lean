import Langlands.AlgebraicGeometry.Picard.MumfordBundle
import Mathlib.RingTheory.Valuation.ValuationRing

/-! # Extension of two-axis-trivial bundles over a valuation ring -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- A line bundle on the generic self-product of an abelian scheme over a valuation
domain, trivial on both unit axes, extends to the total self-product up to an actual
module-sheaf isomorphism. This defines the proposition; it does not prove it. -/
def ValuationRingTwoAxisExtensionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (A : AbelianScheme (Spec (CommRingCat.of R))),
    let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
    let B := (baseChange b).obj A
    let π := pullback.fst A.X.hom b
    let q := pullback.map B.X.hom B.X.hom A.X.hom A.X.hom
      π π b pullback.condition.symm pullback.condition.symm
    ∀ (D : LineBundle (mumfordProduct B).left),
      Nonempty ((Scheme.Modules.pullback (mumfordSection B)).obj D.obj ≅
        structureSheaf B.X.left) →
      Nonempty ((Scheme.Modules.pullback
        (pullback.lift (B.X.hom ≫ unitSection B) (𝟙 B.X.left)
          (by simp [Category.assoc, unitSection_comp]))).obj D.obj ≅
        structureSheaf B.X.left) →
      ∃ E : LineBundle (mumfordProduct A).left,
        Nonempty (((LineBundle.pullback q).obj E).obj ≅ D.obj)

end Langlands.AbelianScheme
