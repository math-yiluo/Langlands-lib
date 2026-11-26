import Langlands.AbelianScheme.Tate.AbelianPrimeAdic
import Langlands.Cohomology.DivisibleSystem.EtaleAdicCohomology
import Langlands.Geometry.EtaleDerivedGlobalPullback
import Langlands.Geometry.EtaleInverseImageConstant
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Degree-one étale cohomology and the dual of the Tate module

Milne, *Abelian Varieties*, §15, Theorem 15.1(a). The comparison uses
the ordinary inverse limit of the finite-coefficient étale cohomology
and is natural under actual homomorphisms of abelian varieties.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Geometry

universe wS wR

set_option autoImplicit false

namespace Langlands.Cohomology.AbelianFirstEtale

variable (p : ℕ) [Fact p.Prime]

private abbrev reductions : ℕᵒᵖ ⥤ ModuleCat ℤ_[p] :=
  (Langlands.Coefficients.AdicSystem.functor (Ideal.span {(p : ℤ_[p])})).obj
    (ModuleCat.of ℤ_[p] ℤ_[p])

/-- The degree-one adic étale cohomology with constant `ℤ_p` coefficients. -/
def firstAdicCohomology (X : Scheme) : ModuleCat ℤ_[p] :=
  limit (reductions p ⋙ EtaleDerivedSections.constantCohomology X ℤ_[p] 1)

private def constantCohomologyPullback {X Y : Scheme} (f : Y ⟶ X)
    [HasDerivedCategory.{wS} (EtaleDerivedSections.ModuleSheaf X ℤ_[p])]
    [HasDerivedCategory.{wS} (EtaleDerivedSections.ModuleSheaf Y ℤ_[p])]
    [HasDerivedCategory.{wR} (ModuleCat ℤ_[p])] :
    EtaleDerivedSections.constantCohomology X ℤ_[p] 1 ⟶
      EtaleDerivedSections.constantCohomology Y ℤ_[p] 1 :=
  Functor.whiskerLeft _ (EtaleDerivedGlobalPullback.cohomologyPullback f ℤ_[p] 1) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (EtaleInverseImage.inverseImageConstantIso f ℤ_[p]).hom _

/-- Pullback on actual degree-one adic étale cohomology, applying the
constant-coefficient pullback at every reduction. -/
def firstAdicCohomologyPullback {X Y : Scheme} (f : Y ⟶ X)
    [HasDerivedCategory.{wS} (EtaleDerivedSections.ModuleSheaf X ℤ_[p])]
    [HasDerivedCategory.{wS} (EtaleDerivedSections.ModuleSheaf Y ℤ_[p])]
    [HasDerivedCategory.{wR} (ModuleCat ℤ_[p])] :
    firstAdicCohomology p X ⟶ firstAdicCohomology p Y :=
  limMap (Functor.whiskerLeft (reductions p) (constantCohomologyPullback p f))

open Langlands.AbelianScheme.Tate.PrimeAdic

variable (K : Type) [Field K] [IsAlgClosed K]

local notation "S" => Spec (CommRingCat.of K)

/-- Degree-one adic étale cohomology over an algebraically closed field
is naturally the `ℤ_p`-linear dual of the actual Tate module. -/
def AbelianFirstEtaleCohomologyStatement
    [∀ A : Langlands.AbelianScheme (Spec (CommRingCat.of K)),
      HasDerivedCategory.{wS} (EtaleDerivedSections.ModuleSheaf A.X.left ℤ_[p])]
    [HasDerivedCategory.{wR} (ModuleCat ℤ_[p])] : Prop :=
  (p : K) ≠ 0 →
  ∃ Φ : ∀ A : Langlands.AbelianScheme S, firstAdicCohomology p A.X.left ≃ₗ[ℤ_[p]]
      Module.Dual ℤ_[p] (Integral A (Over.mk (𝟙 S)) p),
    ∀ {A B : Langlands.AbelianScheme S} (f : A ⟶ B) (x : firstAdicCohomology p B.X.left),
      Φ A (firstAdicCohomologyPullback p (Langlands.AbelianScheme.groupHom f).hom.hom.left x) =
        (Φ B x).comp (map (Over.mk (𝟙 S)) p f)

end Langlands.Cohomology.AbelianFirstEtale
