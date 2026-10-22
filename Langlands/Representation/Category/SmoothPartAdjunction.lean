import Langlands.Representation.Category.Abelian
import Langlands.Representation.Smooth.SmoothPart.Definitions
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.RepresentationTheory.Rep.Iso

/-!
# The smooth-part functor and injective smooth representations

The smooth part of an algebraic representation is right adjoint to the inclusion
of smooth representations. Since the inclusion preserves and reflects
monomorphisms, injective algebraic representations have injective smooth parts,
and the smooth category has enough injectives.
-/

noncomputable section

namespace Langlands

open CategoryTheory CategoryTheory.Limits

universe u uR uG uV

namespace SmoothRep

section Functor

variable (R : Type uR) (G : Type uG) [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The smooth part of an algebraic representation, as an object of the published
smooth category. -/
abbrev smoothPartObj (A : Rep.{uV} R G) : SmoothRep.{uR, uG, uV} R G :=
  SmoothRep.of (smoothPart A.ρ) (isSmooth_smoothPart A.ρ)

/-- Restriction of intertwiners to smooth vectors is a functor. -/
def smoothPartFunctor : Rep.{uV} R G ⥤ SmoothRep.{uR, uG, uV} R G where
  obj A := smoothPartObj R G A
  map f := ofHom (smoothMap f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem smoothPartFunctor_map_apply {A B : Rep.{uV} R G} (f : A ⟶ B)
    (v : smoothVectors A.ρ) :
    (hom ((smoothPartFunctor R G).map f) v).val = f.hom v.val := rfl

/-- The inclusion of smooth representations is left adjoint to the smooth part:
an intertwiner from a smooth representation lands in the smooth vectors. -/
def toRepSmoothPartAdjunction :
    (toRep : SmoothRep.{uR, uG, uV} R G ⥤ Rep.{uV} R G) ⊣ smoothPartFunctor R G :=
  Adjunction.mkOfHomEquiv
    { homEquiv A B :=
        { toFun f := ofHom (smoothLift A.isSmooth f.hom)
          invFun g := Rep.ofHom ((smoothInclusion B.ρ).comp (hom g))
          left_inv _ := rfl
          right_inv _ := rfl }
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

@[simp]
theorem toRepSmoothPartAdjunction_homEquiv_apply {A : SmoothRep.{uR, uG, uV} R G}
    {B : Rep.{uV} R G} (f : toRep.obj A ⟶ B) (v : A) :
    (hom ((toRepSmoothPartAdjunction R G).homEquiv A B f) v).val = f.hom v := rfl

/-- The counit is the inclusion of the smooth vectors. -/
theorem toRepSmoothPartAdjunction_counit_app_apply (B : Rep.{uV} R G)
    (v : smoothVectors B.ρ) :
    ((toRepSmoothPartAdjunction R G).counit.app B).hom v = v.val := rfl

/-- The smooth part of an injective algebraic representation is injective in the
smooth category. -/
theorem injective_smoothPart (B : Rep.{uV} R G) [Injective B] :
    Injective ((smoothPartFunctor R G).obj B) :=
  (toRepSmoothPartAdjunction R G).map_injective B inferInstance

end Functor

section EnoughInjectives

variable (R : Type u) (G : Type u) [CommRing R] [Group G]

/-- Mathlib's algebraic representations have enough injectives, through the
equivalence with modules over the group algebra. -/
instance rep_enoughInjectives : EnoughInjectives (Rep.{u} R G) :=
  EnoughInjectives.of_equivalence (Rep.equivalenceModuleMonoidAlgebra (k := R) (G := G)).functor

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The smooth representation category has enough injectives. -/
instance enoughInjectives : EnoughInjectives (SmoothRep.{u, u, u} R G) :=
  EnoughInjectives.of_adjunction (toRepSmoothPartAdjunction R G)

end EnoughInjectives

end SmoothRep

end Langlands
