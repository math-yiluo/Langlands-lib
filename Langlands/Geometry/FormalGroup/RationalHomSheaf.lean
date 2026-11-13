import Langlands.Geometry.FormalGroup.AlgebraHomFunctor
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Sites.ConcreteSheafification

/-! # Integral and rational formal Hom on Spec R -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]

/-- The actual structure presheaf of Spec R, retaining its structural R-algebras. -/
def coefficientStructurePresheaf (R : Type v) [CommRing R] :
    (Opens (PrimeSpectrum R))ᵒᵖ ⥤ CommAlgCat.{v} R where
  obj U := CommAlgCat.of R ((AlgebraicGeometry.Spec.structureSheaf R).obj.obj U)
  map i := { hom' := {
    __ := ((AlgebraicGeometry.Spec.structureSheaf R).obj.map i).hom
    commutes' _ := rfl } }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Actual O-linear formal Hom over the ring of sections of each open set. -/
def integralHomPresheaf (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) :
    TopCat.Presheaf (ModuleCat.{v} O) (PrimeSpectrum.Top R) :=
  coefficientStructurePresheaf R ⋙ algebraHomFunctor M N

/-- The associated integral Hom sheaf when the scalar and base universes agree. -/
def integralHomSheaf {O' : Type v} [CommRing O'] [Algebra O' R]
    (M : ModuleLaw O' R σ) (N : ModuleLaw O' R τ) :
    TopCat.Sheaf (ModuleCat.{v} O') (PrimeSpectrum.Top R) :=
  (presheafToSheaf (Opens.grothendieckTopology (PrimeSpectrum.Top R))
    (ModuleCat.{v} O')).obj (integralHomPresheaf M N)

variable (F : Type v) [Field F] [Algebra O F]

/-- On each open set, rationalize the actual module of integral formal maps. -/
def rationalHomPresheaf (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) :
    TopCat.Presheaf (ModuleCat.{v} F) (PrimeSpectrum.Top R) :=
  coefficientStructurePresheaf R ⋙ rationalHomFunctor F M N

/-- The Zariski sheaf of rational formal Hom, obtained by genuine sheafification. -/
def rationalHomSheaf (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) :
    TopCat.Sheaf (ModuleCat.{v} F) (PrimeSpectrum.Top R) :=
  (presheafToSheaf (Opens.grothendieckTopology (PrimeSpectrum.Top R))
    (ModuleCat.{v} F)).obj (rationalHomPresheaf F M N)

/-- Rational morphism sections on an arbitrary open subset of Spec R. -/
abbrev RationalSection (M : ModuleLaw O R σ) (N : ModuleLaw O R τ)
    (U : Opens (PrimeSpectrum R)) :=
  (rationalHomSheaf F M N).obj.obj (op U)

variable {F}
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

/-- Send an actual rational formal map on an open set to its sheaf section. -/
def RationalSection.ofRational (U : Opens (PrimeSpectrum R)) :
    (rationalHomPresheaf F M N).obj (op U) →ₗ[F] RationalSection F M N U :=
  ((CategoryTheory.toSheafify (Opens.grothendieckTopology (PrimeSpectrum.Top R))
    (rationalHomPresheaf F M N)).app (op U)).hom

/-- Restrict a rational formal morphism section along an open inclusion. -/
def RationalSection.restrict {U V : Opens (PrimeSpectrum R)} (i : V ⟶ U) :
    RationalSection F M N U →ₗ[F] RationalSection F M N V :=
  ((rationalHomSheaf F M N).obj.map i.op).hom

@[simp]
theorem RationalSection.restrict_id (U : Opens (PrimeSpectrum R))
    (f : RationalSection F M N U) : restrict (𝟙 U) f = f := by
  exact congrArg (fun k => k.hom f) ((rationalHomSheaf F M N).obj.map_id (op U))

@[simp]
theorem RationalSection.restrict_comp {U V W : Opens (PrimeSpectrum R)}
    (i : V ⟶ U) (j : W ⟶ V) (f : RationalSection F M N U) :
    restrict (j ≫ i) f = restrict j (restrict i f) := by
  exact congrArg (fun k => k.hom f) ((rationalHomSheaf F M N).obj.map_comp i.op j.op)

/-- The sheafification map commutes with actual coefficient restriction. -/
theorem RationalSection.restrict_ofRational {U V : Opens (PrimeSpectrum R)}
    (i : V ⟶ U) (f : (rationalHomPresheaf F M N).obj (op U)) :
    restrict i (ofRational U f) =
      ofRational V ((rationalHomPresheaf F M N).map i.op f) := by
  exact (congrArg (fun k => k.hom f)
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology (PrimeSpectrum.Top R))
      (rationalHomPresheaf F M N)).naturality i.op)).symm

/-- The image of a global tensor Hom in the actual rational Hom sheaf. -/
def RationalSection.ofGlobal (f : RationalHom F M N) : RationalSection F M N ⊤ :=
  ofRational ⊤ (RationalHom.map
    (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op ⊤))) f)

end Langlands.FormalGroup.ModuleLaw
