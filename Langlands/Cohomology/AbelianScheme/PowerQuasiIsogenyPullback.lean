import Langlands.AbelianScheme.RationalIntegralComparison
import Langlands.Shimura.PEL.AbelianPowerGaloisOperators

/-! # Pullback by a rational isomorphism on the degree-one part of an abelian power -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Geometry EtaleDerivedSections EtaleGaloisAction
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe wS wR

namespace Langlands.Cohomology.AbelianPower

open Langlands.AbelianScheme

variable {S T : Scheme.{0}} {B : AbelianScheme S} {C : AbelianScheme T}
variable (b : S ⟶ T)

/-- Apply the given integral map on each factor and project from the base change
of the target to the target itself. -/
def powerMapOver (a : B ⟶ (Langlands.AbelianScheme.baseChange b).obj C) (m : ℕ) :
    (Over.map b).obj (relativePower B m) ⟶ relativePower C m :=
  let projection : (Over.map b).obj ((Langlands.AbelianScheme.baseChange b).obj C).X ⟶ C.X :=
    Over.homMk (pullback.fst C.X.hom b) pullback.condition
  relativePowerLift C m fun i => (Over.map b).map
    (relativePowerProjection B m i ≫ (groupHom a).hom.hom) ≫ projection

variable {F : Type} [Field F] {s : S ⟶ Spec (CommRingCat.of F)}
  {t : T ⟶ Spec (CommRingCat.of F)} (h : b ≫ t = s)
  (m p : ℕ) [Fact p.Prime] {Λ : Type} [Field Λ] (j : ℚ_[p] →+* Λ)
variable [HasDerivedCategory.{wS} (ModuleSheaf
  (EtaleGaloisAction.baseChange F (AlgebraicClosure F) (overField B s m).hom) ℤ_[p])]
variable [HasDerivedCategory.{wS} (ModuleSheaf
  (EtaleGaloisAction.baseChange F (AlgebraicClosure F) (overField C t m).hom) ℤ_[p])]
variable [HasDerivedCategory.{wR} (ModuleCat ℤ_[p])]

/-- Pull back using an integral map representing a multiple of the rational
isomorphism, with the scalar correction for degree one in each factor. -/
def quasiIsogenyPullback
    (e : Langlands.Rationalization.of B ≅
      Langlands.Rationalization.of ((Langlands.AbelianScheme.baseChange b).obj C)) (q : ℕ) :
    (cohomologyAction C t m p j q).V →ₗ[Λ] (cohomologyAction B s m p j q).V :=
  let a := rationalIsoIntegralData e
  let u := powerMapOver b a.hom m
  let v : overField B s m ⟶ overField C t m := Over.homMk u.left (by
    change u.left ≫ (relativePower C m).hom ≫ t = (relativePower B m).hom ≫ s
    rw [← Category.assoc, u.w]
    change ((relativePower B m).hom ≫ b) ≫ t = _
    rw [Category.assoc, h])
  (((a.homDenom : Λ) ^ m)⁻¹) •
    ((ModuleCat.extendScalars j).map (HodgeTate.ellAdicEtalePullback p v q)).hom

end Langlands.Cohomology.AbelianPower
