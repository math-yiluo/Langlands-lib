import Langlands.Geometry.EtaleGaloisTower
import Langlands.Cohomology.DivisibleSystem.ContinuousLimit

/-! # Continuous Galois actions on inverse limits of Galois-tower étale cohomology -/

noncomputable section

namespace Langlands.Geometry.EtaleGaloisTower

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Cohomology

universe u wS wR

variable {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
variable (R : Type u) [CommRing R]
variable [∀ x : FiniteGaloisIntermediateField K L × SingleObj (L ≃ₐ[K] L),
  HasDerivedCategory.{wS} (EtaleDerivedSections.ModuleSheaf
    ((EtaleCanonicalDeckTower.schemeDiagram (galoisTower (L := L) f)).obj x).unop R)]
variable [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- For an inverse system of coefficient sheaves on `X`, the inverse system of colimit
cohomology representations over the finite Galois tower. -/
def galoisAdicSystem (q : ℕ) :
    (ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) ⥤
      (ℕᵒᵖ ⥤ Action (ModuleCat.{u} R) (L ≃ₐ[K] L)) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (EtaleCanonicalDeckTower.colimitCohomologyFunctor.{u, u, u, u, wS, wR} R
      (galoisTower (L := L) f) q)

/-- Every level of the inverse system is a smooth Galois representation. -/
theorem isSmooth_galoisAdicSystem (q : ℕ) (F : ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R)
    (m : ℕᵒᵖ) :
    IsSmooth ((Rep.ActionToRep R (L ≃ₐ[K] L)).obj
      (((galoisAdicSystem.{u, wS, wR} L f R q).obj F).obj m)).ρ :=
  EtaleCanonicalDeckTower.isSmooth_colimitCohomology R (galoisTower f)
    (isLevelwiseSmooth_galoisTower f) q (F.obj m)

/-- The inverse limit over `m` of the colimit cohomology, with the inverse limit topology of
the discrete levels. -/
abbrev GaloisAdicSpace (q : ℕ) (F : ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) : Type u :=
  ContinuousLimit.ConeSpace (limit.cone ((galoisAdicSystem.{u, wS, wR} L f R q).obj F))

/-- The Galois action on the inverse limit is jointly continuous for the Krull topology. -/
theorem continuous_galoisAdicAction (q : ℕ) (F : ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) :
    Continuous fun p : (L ≃ₐ[K] L) × GaloisAdicSpace.{u, wS, wR} L f R q F =>
      ContinuousLimit.act (limit.cone ((galoisAdicSystem.{u, wS, wR} L f R q).obj F)) p.1 p.2 :=
  ContinuousLimit.continuous_action _ (isSmooth_galoisAdicSystem L f R q F)

/-- The inverse limit is Hausdorff. -/
instance (q : ℕ) (F : ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) :
    T2Space (GaloisAdicSpace.{u, wS, wR} L f R q F) :=
  ContinuousLimit.t2Space_of_isLimit (limit.isLimit _)

/-- The Galois representation on the inverse limit by continuous linear maps. -/
abbrev galoisAdicContRepresentation (q : ℕ) (F : ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) :
    ContRepresentation R (L ≃ₐ[K] L) (GaloisAdicSpace.{u, wS, wR} L f R q F) :=
  ContinuousLimit.contRepresentation _

/-- For a topological coefficient ring acting continuously, the inverse limit with its jointly
continuous Galois action. -/
def galoisAdicContAction [TopologicalSpace R] (q : ℕ)
    (F : ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R)
    [ContinuousSMul R (GaloisAdicSpace.{u, wS, wR} L f R q F)] :
    ContAction (TopModuleCat.{u} R) (L ≃ₐ[K] L) :=
  ContinuousLimit.contAction (limit.cone ((galoisAdicSystem.{u, wS, wR} L f R q).obj F))
    (isSmooth_galoisAdicSystem L f R q F)

/-- For a discrete coefficient ring, the inverse limit as a functor to topological
representations. -/
def galoisAdicTopRepFunctor [TopologicalSpace R] [DiscreteTopology R] (q : ℕ) :
    (ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) ⥤ TopRep.{u} R (L ≃ₐ[K] L) :=
  galoisAdicSystem.{u, wS, wR} L f R q ⋙
    ContinuousLimit.limitTopRepFunctor R (L ≃ₐ[K] L) ℕᵒᵖ

end Langlands.Geometry.EtaleGaloisTower
