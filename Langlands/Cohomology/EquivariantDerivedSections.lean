import Langlands.Cohomology.EquivariantSections
import Langlands.Sheaf.Equivariant.Abelian
import Langlands.Sheaf.Equivariant.Limits
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.RepresentationTheory.Invariants

/-!
# Derived equivariant sections

The global and compact section representations of equivariant module sheaves
are left exact. Their right derived functors, computed with injective
resolutions in the abelian category of equivariant sheaves, take values in
representations of the acting group.
-/

noncomputable section

namespace Langlands.Cohomology.EquivariantDerivedSections

open CategoryTheory CategoryTheory.Limits Opposite Langlands.Sheaf.Equivariant

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- The module underlying the global section representation is evaluation on
the whole space. -/
def sectionRepresentationForgetIso :
    sectionRepresentation R G X ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R) ≅
      evaluation G X (ModuleCat.{u} R) ActionOpens.top :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Global sections are left exact as a representation-valued functor. -/
instance sectionRepresentation_preservesFiniteLimits :
    PreservesFiniteLimits (sectionRepresentation R G X) := by
  have : PreservesFiniteLimits
      (sectionRepresentation R G X ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R)) :=
    preservesFiniteLimits_of_natIso (sectionRepresentationForgetIso R G X).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))

/-- The module underlying the compact section representation is the ordinary
compact-section module of the underlying sheaf. -/
def compactSectionsForgetIso :
    CompactSections.functor R G X ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R) ≅
      toSheaf G X (ModuleCat.{u} R) ⋙
        Langlands.Sheaf.CompactSupport.functor (X := TopCat.of X) (R := R) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Compact sections are left exact as a representation-valued functor. -/
instance compactSections_preservesFiniteLimits :
    PreservesFiniteLimits (CompactSections.functor R G X) := by
  have : PreservesFiniteLimits
      (CompactSections.functor R G X ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R)) :=
    preservesFiniteLimits_of_natIso (compactSectionsForgetIso R G X).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))

/-- Degree `q` derived equivariant global sections. -/
def globalDerived (q : ℕ) : TopologicalSheaf G X (ModuleCat.{u} R) ⥤ Rep.{u} R G :=
  (sectionRepresentation R G X).rightDerived q

/-- Degree `q` derived equivariant compactly supported sections. -/
def compactDerived (q : ℕ) : TopologicalSheaf G X (ModuleCat.{u} R) ⥤ Rep.{u} R G :=
  (CompactSections.functor R G X).rightDerived q

/-- Forgetting support induces natural intertwiners of derived functors. -/
def forgetSupport (q : ℕ) : compactDerived R G X q ⟶ globalDerived R G X q :=
  NatTrans.rightDerived (CompactSections.inclusion R G X) q

/-- In degree zero, derived global sections are global sections. -/
def globalDerivedZeroIso : globalDerived R G X 0 ≅ sectionRepresentation R G X :=
  (sectionRepresentation R G X).rightDerivedZeroIsoSelf

/-- In degree zero, derived compact sections are compact sections. -/
def compactDerivedZeroIso : compactDerived R G X 0 ≅ CompactSections.functor R G X :=
  (CompactSections.functor R G X).rightDerivedZeroIsoSelf

/-- Derived global sections are the homology of global sections of any
injective resolution. -/
def globalDerivedIso {F : TopologicalSheaf G X (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (q : ℕ) :
    (globalDerived R G X q).obj F ≅
      (EquivariantSections.globalHomology R G X (ComplexShape.up ℕ) q).obj I.cocomplex :=
  I.isoRightDerivedObj (sectionRepresentation R G X) q

/-- Derived compact sections are the homology of compact sections of any
injective resolution. -/
def compactDerivedIso {F : TopologicalSheaf G X (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (q : ℕ) :
    (compactDerived R G X q).obj F ≅
      (EquivariantSections.compactHomology R G X (ComplexShape.up ℕ) q).obj I.cocomplex :=
  I.isoRightDerivedObj (CompactSections.functor R G X) q

/-- Derived global sections vanish in positive degrees on injective sheaves. -/
theorem isZero_globalDerived_succ_of_injective (F : TopologicalSheaf G X (ModuleCat.{u} R))
    [Injective F] (q : ℕ) : IsZero ((globalDerived R G X (q + 1)).obj F) :=
  (sectionRepresentation R G X).isZero_rightDerived_obj_injective_succ q F

/-- Derived compact sections vanish in positive degrees on injective sheaves. -/
theorem isZero_compactDerived_succ_of_injective (F : TopologicalSheaf G X (ModuleCat.{u} R))
    [Injective F] (q : ℕ) : IsZero ((compactDerived R G X (q + 1)).obj F) :=
  (CompactSections.functor R G X).isZero_rightDerived_obj_injective_succ q F

/-- Invariant global sections: global sections fixed by every group element. -/
def invariantGlobalSections :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  sectionRepresentation R G X ⋙ Rep.invariantsFunctor R G

/-- Invariant compact sections: compactly supported global sections fixed by
every group element. -/
def invariantCompactSections :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  CompactSections.functor R G X ⋙ Rep.invariantsFunctor R G

instance : (invariantGlobalSections R G X).Additive :=
  inferInstanceAs (sectionRepresentation R G X ⋙ Rep.invariantsFunctor R G).Additive

instance : (invariantCompactSections R G X).Additive :=
  inferInstanceAs (CompactSections.functor R G X ⋙ Rep.invariantsFunctor R G).Additive

/-- Invariant global sections are left exact. -/
instance invariantGlobalSections_preservesFiniteLimits :
    PreservesFiniteLimits (invariantGlobalSections R G X) := by
  have := (Rep.invariantsAdjunction R G).rightAdjoint_preservesLimits
  exact inferInstanceAs
    (PreservesFiniteLimits (sectionRepresentation R G X ⋙ Rep.invariantsFunctor R G))

/-- Invariant compact sections are left exact. -/
instance invariantCompactSections_preservesFiniteLimits :
    PreservesFiniteLimits (invariantCompactSections R G X) := by
  have := (Rep.invariantsAdjunction R G).rightAdjoint_preservesLimits
  exact inferInstanceAs
    (PreservesFiniteLimits (CompactSections.functor R G X ⋙ Rep.invariantsFunctor R G))

/-- Degree `q` derived invariant global sections. -/
def invariantGlobalDerived (q : ℕ) :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  (invariantGlobalSections R G X).rightDerived q

/-- Degree `q` derived invariant compact sections. -/
def invariantCompactDerived (q : ℕ) :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  (invariantCompactSections R G X).rightDerived q

/-- In degree zero, derived invariant global sections are invariant global sections. -/
def invariantGlobalDerivedZeroIso :
    invariantGlobalDerived R G X 0 ≅ invariantGlobalSections R G X :=
  (invariantGlobalSections R G X).rightDerivedZeroIsoSelf

/-- In degree zero, derived invariant compact sections are invariant compact sections. -/
def invariantCompactDerivedZeroIso :
    invariantCompactDerived R G X 0 ≅ invariantCompactSections R G X :=
  (invariantCompactSections R G X).rightDerivedZeroIsoSelf

/-- Derived invariant compact sections are the homology of invariant compact
sections of any injective resolution. -/
def invariantCompactDerivedIso {F : TopologicalSheaf G X (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (q : ℕ) :
    (invariantCompactDerived R G X q).obj F ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).obj
        (((invariantCompactSections R G X).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) :=
  I.isoRightDerivedObj (invariantCompactSections R G X) q

/-- Diagrams of equivariant sheaves give diagrams of derived compact-section
representations. -/
def compactDerivedDiagram (J : Type*) [Category J] (q : ℕ) :
    (J ⥤ TopologicalSheaf G X (ModuleCat.{u} R)) ⥤ (J ⥤ Rep.{u} R G) :=
  (Functor.whiskeringRight J _ _).obj (compactDerived R G X q)

end Langlands.Cohomology.EquivariantDerivedSections
