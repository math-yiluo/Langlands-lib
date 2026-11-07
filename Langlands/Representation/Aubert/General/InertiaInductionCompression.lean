import Langlands.Representation.CuspidalSupport.RationalInertiaCompression
import Langlands.Representation.Aubert.General.InductionColimits

/-! # Compact compression on normalized inductions of actual inertia blocks -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.LinearAlgebra.StableEndomorphism
open scoped CategoryTheory.MonObj

universe uF uV uG uH

namespace Langlands.SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

/-- Smooth pullback retains addition on the actual linear maps. -/
instance pullbackFunctor_additive (e : H ≃ₜ* G) :
    (pullbackFunctor.{uG, uH, uV} e).Additive where
  map_add {_ _} _ _ := by
    apply ObjectProperty.hom_ext
    ext v
    rfl

/-- Smooth pullback retains the underlying exact rows and surjections, hence
preserves finite colimits without any representation finiteness condition. -/
instance pullbackFunctor_preservesFiniteColimits (e : H ≃ₜ* G) :
    PreservesFiniteColimits (pullbackFunctor.{uG, uH, uV} e) := by
  apply ((Functor.preservesFiniteColimits_tfae (pullbackFunctor e)).out 1 4).mp
  intro S hS
  have hmodule := hS.exact.map
    (toRep ⋙ forget₂ (Rep.{uV} ℂ G) (ModuleCat.{uV} ℂ))
  refine ⟨?_, (epi_iff_surjective _).mpr
    ((epi_iff_surjective S.g).mp hS.epi_g)⟩
  apply (toRep ⋙ forget₂ (Rep.{uV} ℂ H) (ModuleCat.{uV} ℂ)).reflects_exact_of_faithful
  exact hmodule

end Langlands.SmoothRep

namespace Langlands.Aubert.General

open CuspidalSupport

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (L : GroupScheme (Spec (CommRingCat.of F))) [IsAffine L.X.left]
  [LocallyOfFiniteType L.X.hom]

local instance inertiaInductionCompressionRationalPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints L) :=
  rationalPointTopology F L.X

local instance inertiaInductionCompressionRationalPointTopologicalGroup :
    IsTopologicalGroup (GroupScheme.rationalPoints L) :=
  rationalPoint_isTopologicalGroup F L

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (e : M ≃ₜ* GroupScheme.rationalPoints L)

/-- Actual normalized induction after same-carrier transport from the rational
points of the supplied Levi scheme to its actual topological Levi subgroup. -/
def rationalInertiaInductionFunctor :
    SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints L) ⥤
      SmoothRep.{0, uG, max uG (max uF uV)} ℂ G :=
  SmoothRep.pullbackFunctor e ⋙ normalizedInductionFunctor h hU

instance rationalInertiaInductionFunctor_additive :
    (rationalInertiaInductionFunctor.{uF, uV, uG} L h hU e).Additive := by
  dsimp only [rationalInertiaInductionFunctor]
  infer_instance

variable (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints L))
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)

/-- On every induced object from the actual lifted inertia block, the
generator image's stable power works with precisely the same exponent. -/
theorem rationalInertiaInduction_stablePower_of_normKernel [T2Space G]
    (hcof : CompactOpenCofinal G) (hP : IsClosed (P : Set G))
    (hproj : Continuous h.projection) [CompactSpace (Induction.LeftQuotient P)]
    (hgen : IsRationalNormKernelSmallProgenerator L π) (b : ℕ)
    (hstable : Stable (Jacquet.compressedAction
      ((rationalInertiaInductionFunctor L h hU e).obj
        (rationalNormKernelCompactInduction L π)).representation
      ((rationalInertiaInductionFunctor L h hU e).obj
        (rationalNormKernelCompactInduction L π)).isSmooth K hK g ^ b)) :
    RationalInertiaImageStablePower L π
      (rationalInertiaInductionFunctor L h hU e) K hK g b := by
  let := normalizedInductionFunctor_preservesFiniteColimits.{uG, max uF uV}
    h hU hcof hP hproj
  have : PreservesFiniteColimits (rationalInertiaInductionFunctor L h hU e) := by
    dsimp only [rationalInertiaInductionFunctor]
    infer_instance
  have hcop (I : Type (max uF uV)) : PreservesColimitsOfShape (Discrete I)
      (rationalInertiaInductionFunctor L h hU e) := by
    classical
    have : PreservesColimitsOfShape (Discrete I)
        (normalizedInductionFunctor.{uG, max uF uV} h hU) :=
      normalizedInductionFunctor_preservesCoproducts.{uG, max uF uV, 0} h hU
    dsimp only [rationalInertiaInductionFunctor]
    exact comp_preservesColimitsOfShape _ _
  exact rationalInertiaImageStablePower_of_normKernel
    L π (rationalInertiaInductionFunctor L h hU e) K hK g hcop hgen b hstable

/-- One positive stationary threshold precedes all objects in the actual
inertia block when the normalized induction of its actual generator is
eventually stable. -/
theorem rationalInertiaInduction_stationary_of_normKernel [T2Space G]
    (hcof : CompactOpenCofinal G) (hP : IsClosed (P : Set G))
    (hproj : Continuous h.projection) [CompactSpace (Induction.LeftQuotient P)]
    (hgen : IsRationalNormKernelSmallProgenerator L π)
    (hstable : EventuallyStable (Jacquet.compressedAction
      ((rationalInertiaInductionFunctor L h hU e).obj
        (rationalNormKernelCompactInduction L π)).representation
      ((rationalInertiaInductionFunctor L h hU e).obj
        (rationalNormKernelCompactInduction L π)).isSmooth K hK g)) :
    ∃ b : ℕ, 0 < b ∧
      ∀ A : RationalInertiaBlock L (rationalInertiaBaseLift L π),
        Jacquet.CompactCompressionStationaryFrom
          ((rationalInertiaInductionFunctor L h hU e).obj A.obj).representation
          ((rationalInertiaInductionFunctor L h hU e).obj A.obj).isSmooth K hK g b := by
  obtain ⟨b, hb, hpower⟩ := hstable
  refine ⟨b, hb, fun A => ?_⟩
  exact Jacquet.compactCompressionStationaryFrom_of_stablePower
    _ _ K hK g hb
    (rationalInertiaInduction_stablePower_of_normKernel
      L h hU e π K hK g hcof hP hproj hgen b hpower A)

end Langlands.Aubert.General
