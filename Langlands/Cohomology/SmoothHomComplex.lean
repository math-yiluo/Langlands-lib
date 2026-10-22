import Langlands.Cohomology.LinearHomComplex
import Langlands.Representation.Category.Basic
import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Hom complexes in the actual smooth representation category

The terms consist of equivariant linear maps between the specified smooth
representations. No Ext object or resolution is supplied as a data field.
-/

noncomputable section

namespace Langlands.Cohomology.SmoothHomComplex

open CategoryTheory Opposite

universe uR uG uV

variable (R : Type uR) [CommRing R]
variable (G : Type uG) [Group G] [TopologicalSpace G]

/-- The actual bifunctor on complexes of the published smooth representations. -/
def bifunctor :
    (CochainComplex (Langlands.SmoothRep.{uR, uG, uV} R G) ℤ)ᵒᵖ ⥤
      CochainComplex (Langlands.SmoothRep.{uR, uG, uV} R G) ℤ ⥤
        CochainComplex (ModuleCat.{uV} R) ℤ :=
  LinearHomComplex.bifunctor R

/-- Graded cohomology of Hom between two specified smooth representation complexes. -/
def cohomology (P : CochainComplex (Langlands.SmoothRep.{uR, uG, uV} R G) ℤ)
    (n : ℤ) :
    CochainComplex (Langlands.SmoothRep.{uR, uG, uV} R G) ℤ ⥤ ModuleCat.{uV} R :=
  LinearHomComplex.cohomology R P n

/-- Equivariant linear maps from a fixed actual smooth representation. -/
def homFunctor (V : Langlands.SmoothRep.{uR, uG, uV} R G) :
    Langlands.SmoothRep.{uR, uG, uV} R G ⥤ ModuleCat.{uV} R :=
  (linearCoyoneda R (Langlands.SmoothRep.{uR, uG, uV} R G)).obj (op V)

instance (V : Langlands.SmoothRep.{uR, uG, uV} R G) :
    (homFunctor R G V).Additive :=
  inferInstanceAs ((linearCoyoneda R (Langlands.SmoothRep.{uR, uG, uV} R G)).obj
    (op V)).Additive

/-- Apply equivariant Hom to every term and differential of the given complex. -/
def fromRepresentation (V : Langlands.SmoothRep.{uR, uG, uV} R G) :
    CochainComplex (Langlands.SmoothRep.{uR, uG, uV} R G) ℤ ⥤
      CochainComplex (ModuleCat.{uV} R) ℤ :=
  (homFunctor R G V).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The component differential is postcomposition with the actual differential. -/
theorem fromRepresentation_d_apply
    (V : Langlands.SmoothRep.{uR, uG, uV} R G)
    (Q : CochainComplex (Langlands.SmoothRep.{uR, uG, uV} R G) ℤ)
    (n m : ℤ) (f : V ⟶ Q.X n) :
    (((fromRepresentation R G V).obj Q).d n m) f = f ≫ Q.d n m := rfl

/-- Changing the source representation gives a natural chain map by precomposition. -/
def precomposeRepresentation
    {V W : Langlands.SmoothRep.{uR, uG, uV} R G} (f : V ⟶ W) :
    fromRepresentation R G W ⟶ fromRepresentation R G V :=
  NatTrans.mapHomologicalComplex
    ((linearCoyoneda R (Langlands.SmoothRep.{uR, uG, uV} R G)).map f.op)
    (ComplexShape.up ℤ)

/-- The cohomology of termwise Hom, with no injectivity assumption on the input. -/
def fromRepresentationCohomology
    (V : Langlands.SmoothRep.{uR, uG, uV} R G) (n : ℤ) :
    CochainComplex (Langlands.SmoothRep.{uR, uG, uV} R G) ℤ ⥤ ModuleCat.{uV} R :=
  fromRepresentation R G V ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{uV} R) (ComplexShape.up ℤ) n

end Langlands.Cohomology.SmoothHomComplex
