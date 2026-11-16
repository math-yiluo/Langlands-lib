import Langlands.Cohomology.SiteCech.FreeSections
import Langlands.Cohomology.SiteCech.FiniteCechAcyclic
import Langlands.Sheaf.Equivariant.TwistedGlobalSections

/-! # Higher-derived sections from finite augmented test systems -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Sheaf.Equivariant.TwistedOver
open ZeroObject

universe w a b

variable {C : Type w} [Category.{w} C]
variable (J : GrothendieckTopology C)
variable (R : Type w) [CommRing R] [HasSheafify J (ModuleCat.{w} R)]

/-- Linear Hom from a free representable module sheaf is naturally the
sections functor on its representing object. -/
def freeRepresentableSectionsIso (U : C) :
    (linearCoyoneda R (Sheaf J (ModuleCat.{w} R))).obj
        (op ((freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj U))) ≅
      sheafSectionsModule J R U :=
  NatIso.ofComponents
    (fun F => (freeRepresentableHomLinearEquiv J R U F).toModuleIso)
    (by
      intro F F' g
      ext f
      rfl)

variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]

/-- The representing natural isomorphism induces natural isomorphisms in
every right-derived degree. -/
def freeRepresentableSectionsDerivedIso (U : C) (q : ℕ) :
    ((linearCoyoneda R (Sheaf J (ModuleCat.{w} R))).obj
        (op ((freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj U)))).rightDerived q ≅
      sectionsDerived J R U q where
  hom := NatTrans.rightDerived (freeRepresentableSectionsIso J R U).hom q
  inv := NatTrans.rightDerived (freeRepresentableSectionsIso J R U).inv q
  hom_inv_id := by
    dsimp only [sectionsDerived]
    rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    dsimp only [sectionsDerived]
    rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id, NatTrans.rightDerived_id]

variable {ι : Type a} (U : ι → C)
variable (K : FiniteCechSystem.{w + 1, w, a, b}
  (fun i => (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj (U i))))

/-- Positive Hom exactness for a finite test system of free representable
module sheaves implies actual higher-derived sections vanishing. -/
theorem FiniteCechSystem.isZero_sectionsDerived_of_homAcyclic
    (F : Sheaf J (ModuleCat.{w} R)) (hF : K.HomAcyclic R F) (i : ι) (n : ℕ) :
    IsZero ((sectionsDerived J R (U i) (n + 1)).obj F) :=
  (K.derivedHomAcyclic_of_homAcyclic R F hF i n).of_iso
    ((freeRepresentableSectionsDerivedIso J R (U i) (n + 1)).app F).symm

/-- The corresponding positive-degree sheaf cohomology module is
isomorphic to the zero module. -/
def FiniteCechSystem.sectionsDerivedZeroIso
    (F : Sheaf J (ModuleCat.{w} R)) (hF : K.HomAcyclic R F) (i : ι) (n : ℕ) :
    ((sectionsDerived J R (U i) (n + 1)).obj F) ≅ 0 :=
  (K.isZero_sectionsDerived_of_homAcyclic J R U F hF i n).isoZero

end Langlands.Cohomology.SiteCech
