import Langlands.Sheaf.Equivariant.SmoothSheafCompactSections
import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Compactly supported cohomology of smooth equivariant sheaves

Compact sections of smooth equivariant module sheaves form a left exact functor
to smooth representations. Its right derived functors, computed with injective
resolutions in the abelian category of smooth equivariant sheaves, are smooth
representations. The right derived functors of invariant compact sections on
the same category are modules.
-/

noncomputable section

namespace Langlands.Cohomology.SmoothSheafCohomology

open CategoryTheory CategoryTheory.Limits Langlands.Sheaf.Equivariant

universe u

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable [HasStableNeighbourhoods G X]

/-- Degree `q` derived compact sections of smooth equivariant module sheaves,
as smooth representations. -/
def compactDerived (q : ℕ) :
    SmoothTopologicalSheaf R G X ⥤ Langlands.SmoothRep.{u, u, u} R G :=
  (smoothSheafCompactSections R G X).rightDerived q

/-- In degree zero, derived compact sections are compact sections. -/
def compactDerivedZeroIso : compactDerived R G X 0 ≅ smoothSheafCompactSections R G X :=
  (smoothSheafCompactSections R G X).rightDerivedZeroIsoSelf

/-- Derived compact sections are the homology of compact sections of any
injective resolution in the smooth category. -/
def compactDerivedIso {F : SmoothTopologicalSheaf R G X} (I : InjectiveResolution F) (q : ℕ) :
    (compactDerived R G X q).obj F ≅
      (HomologicalComplex.homologyFunctor (Langlands.SmoothRep.{u, u, u} R G)
        (ComplexShape.up ℕ) q).obj
        (((smoothSheafCompactSections R G X).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) :=
  I.isoRightDerivedObj (smoothSheafCompactSections R G X) q

/-- Derived compact sections vanish in positive degrees on injective smooth
sheaves. -/
theorem isZero_compactDerived_succ_of_injective (F : SmoothTopologicalSheaf R G X)
    [Injective F] (q : ℕ) : IsZero ((compactDerived R G X (q + 1)).obj F) :=
  (smoothSheafCompactSections R G X).isZero_rightDerived_obj_injective_succ q F

/-- Invariant compact sections of smooth equivariant module sheaves:
compactly supported global sections fixed by every group element. -/
def invariantCompactSections : SmoothTopologicalSheaf R G X ⥤ ModuleCat.{u} R :=
  Langlands.Sheaf.Equivariant.smoothInclusion R G X ⋙
    EquivariantDerivedSections.invariantCompactSections R G X

instance invariantCompactSections_additive : (invariantCompactSections R G X).Additive :=
  inferInstanceAs (Langlands.Sheaf.Equivariant.smoothInclusion R G X ⋙
    EquivariantDerivedSections.invariantCompactSections R G X).Additive

/-- Invariant compact sections of smooth sheaves are left exact. -/
instance invariantCompactSections_preservesFiniteLimits :
    PreservesFiniteLimits (invariantCompactSections R G X) :=
  inferInstanceAs (PreservesFiniteLimits (Langlands.Sheaf.Equivariant.smoothInclusion R G X ⋙
    EquivariantDerivedSections.invariantCompactSections R G X))

/-- Degree `q` derived invariant compact sections of smooth equivariant module
sheaves. -/
def invariantCompactDerived (q : ℕ) : SmoothTopologicalSheaf R G X ⥤ ModuleCat.{u} R :=
  (invariantCompactSections R G X).rightDerived q

/-- In degree zero, derived invariant compact sections are invariant compact
sections. -/
def invariantCompactDerivedZeroIso :
    invariantCompactDerived R G X 0 ≅ invariantCompactSections R G X :=
  (invariantCompactSections R G X).rightDerivedZeroIsoSelf

/-- Derived invariant compact sections are the homology of invariant compact
sections of any injective resolution in the smooth category. -/
def invariantCompactDerivedIso {F : SmoothTopologicalSheaf R G X}
    (I : InjectiveResolution F) (q : ℕ) :
    (invariantCompactDerived R G X q).obj F ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).obj
        (((invariantCompactSections R G X).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) :=
  I.isoRightDerivedObj (invariantCompactSections R G X) q

/-- Derived invariant compact sections vanish in positive degrees on injective
smooth sheaves. -/
theorem isZero_invariantCompactDerived_succ_of_injective (F : SmoothTopologicalSheaf R G X)
    [Injective F] (q : ℕ) : IsZero ((invariantCompactDerived R G X (q + 1)).obj F) :=
  (invariantCompactSections R G X).isZero_rightDerived_obj_injective_succ q F

end Langlands.Cohomology.SmoothSheafCohomology
