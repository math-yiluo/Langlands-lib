import Langlands.AlgebraicGeometry.Picard.SquareSecondProjectionSupportStatement
import Langlands.AlgebraicGeometry.Picard.SquareSecondFibre
import Langlands.AlgebraicGeometry.Modules.RationalPointComplement
import Langlands.AlgebraicGeometry.Modules.RationalFibreVanishing
import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsProof

/-! # Finite support of higher direct images on the second abelian-square projection -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules

/-- The exact finite-support proposition for the second abelian-square projection. -/
theorem squareSecondProjectionSupport : SquareSecondProjectionSupportStatement.{u} := by
  intro K _ _ A Q F hF hQ
  let U := rationalPointComplement A.X.hom F hF
  have hU : ∀ y : Spec (CommRingCat.of K) ⟶ U.toScheme,
      y ≫ U.ι ≫ A.X.hom = 𝟙 (Spec (CommRingCat.of K)) → ∀ n : ℕ,
        IsZero
          ((DerivedSections.relativeCohomology
            (pullback.snd (pullback.snd A.X.hom A.X.hom) (y ≫ U.ι)) n).obj
            ((Scheme.Modules.pullback
              (pullback.fst (pullback.snd A.X.hom A.X.hom) (y ≫ U.ι))).obj Q.obj)) := by
    intro y hy n
    let x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X :=
      Over.homMk (y ≫ U.ι) (by simpa only [Over.mk_hom, Category.assoc] using hy)
    have hx : x ∉ F := by
      apply (mem_rationalPointComplement_iff A.X.hom F hF x).mp
      change (y (IsLocalRing.closedPoint K)).val ∈ U
      exact (y (IsLocalRing.closedPoint K)).property
    exact (hQ x hx n).of_iso
      (squareSecondFibreCohomologyIso A.X.hom x.left x.w Q.obj n)
  intro n
  exact hasFiniteClosedSupport_of_isZero_rationalPointComplement A.X.hom F hF _
    (DerivedSections.isZero_pullback_higherDirectImage_of_rationalFibres
      universalPerfectSections K A.X.hom (pullback.snd A.X.hom A.X.hom) Q U hU n)

end Langlands.AbelianScheme
