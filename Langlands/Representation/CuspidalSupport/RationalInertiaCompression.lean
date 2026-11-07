import Langlands.Representation.CuspidalSupport.RationalInertiaSmoothCoproducts
import Langlands.Representation.Category.GeneratorCompression

/-! # Compact compression on images of actual rational inertia blocks -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.LinearAlgebra.StableEndomorphism
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV uH uW

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

variable {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
  (T : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G) ⥤
    SmoothRep.{0, uH, uW} ℂ H)
  (K : OpenSubgroup H) (hK : IsCompact (K : Set H)) (g : H)

/-- A single stable compression power on the image of every object of the
actual lifted inertia block. -/
def RationalInertiaImageStablePower (b : ℕ) : Prop :=
  ∀ A : RationalInertiaBlock G (rationalInertiaBaseLift G π),
    Stable (Jacquet.compressedAction
      (T.obj A.obj).representation (T.obj A.obj).isSmooth K hK g ^ b)

/-- The actual norm-kernel generator transfers the same compression exponent
to every object of its actual inertia block through a right-exact functor
preserving the required coproducts. -/
theorem rationalInertiaImageStablePower_of_normKernel
    [T.Additive] [PreservesFiniteColimits T]
    (hcop : ∀ I : Type (max uF uV), PreservesColimitsOfShape (Discrete I) T)
    (hP : IsRationalNormKernelSmallProgenerator G π) (b : ℕ)
    (hstable : Stable (Jacquet.compressedAction
      (T.obj (rationalNormKernelCompactInduction G π)).representation
      (T.obj (rationalNormKernelCompactInduction G π)).isSmooth K hK g ^ b)) :
    RationalInertiaImageStablePower G π T K hK g b := by
  obtain ⟨hmem, _, hfaith, hblockcop, _⟩ := hP
  let : HasCoproducts.{max uF uV}
      (RationalInertiaBlock G (rationalInertiaBaseLift G π)) := hblockcop
  let P : RationalInertiaBlock G (rationalInertiaBaseLift G π) :=
    ⟨rationalNormKernelCompactInduction G π, hmem⟩
  let S := (rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)).ι ⋙ T
  have hScop (I : Type (max uF uV)) :
      PreservesColimitsOfShape (Discrete I) S := by
    let := hcop I
    exact comp_preservesColimitsOfShape _ _
  exact SmoothRep.functorCompressionStablePower_of_generator
    S K hK g hScop P hfaith b hstable

/-- Eventual compression stability on the actual generator image yields one
positive stationary threshold before all objects of its actual inertia block. -/
theorem rationalInertiaImageStationary_of_normKernel
    [T.Additive] [PreservesFiniteColimits T]
    (hcop : ∀ I : Type (max uF uV), PreservesColimitsOfShape (Discrete I) T)
    (hP : IsRationalNormKernelSmallProgenerator G π)
    (hstable : EventuallyStable (Jacquet.compressedAction
      (T.obj (rationalNormKernelCompactInduction G π)).representation
      (T.obj (rationalNormKernelCompactInduction G π)).isSmooth K hK g)) :
    ∃ b : ℕ, 0 < b ∧
      ∀ A : RationalInertiaBlock G (rationalInertiaBaseLift G π),
        Jacquet.CompactCompressionStationaryFrom
          (T.obj A.obj).representation (T.obj A.obj).isSmooth K hK g b := by
  obtain ⟨b, hb, hpower⟩ := hstable
  refine ⟨b, hb, fun A => ?_⟩
  exact Jacquet.compactCompressionStationaryFrom_of_stablePower
    (T.obj A.obj).representation (T.obj A.obj).isSmooth K hK g hb
    (rationalInertiaImageStablePower_of_normKernel
      G π T K hK g hcop hP b hpower A)

end Langlands.CuspidalSupport
