import Langlands.Cohomology.DerivedPlus
import Langlands.Cohomology.SmoothSheafCohomology

/-!
# Derived compact section complexes of smooth equivariant sheaves

The derived compactly supported section complex of a smooth equivariant module
sheaf, as an object of the bounded below derived category of smooth
representations, together with the derived complex of invariant compact
sections. Their cohomology in each degree `q ≥ 0` is the corresponding derived
functor of `SmoothSheafCohomology`, and it vanishes in negative degrees.
-/

noncomputable section

namespace Langlands.Cohomology.SmoothSheafDerivedComplex

open CategoryTheory Langlands.Sheaf.Equivariant

universe w w' w'' u

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable [HasStableNeighbourhoods G X]
variable [HasDerivedCategory.{w} (SmoothTopologicalSheaf R G X)]

section Smooth

variable [HasDerivedCategory.{w'} (Langlands.SmoothRep.{u, u, u} R G)]

/-- The derived compact section complex of smooth sheaves, in the bounded
below derived category of smooth representations. -/
def compactComplex :
    SmoothTopologicalSheaf R G X ⥤ DerivedCategory.Plus (Langlands.SmoothRep.{u, u, u} R G) :=
  DerivedPlus.derivedComplex (smoothSheafCompactSections R G X)

/-- Cohomology of the derived compact section complex in degree `q` is
`SmoothSheafCohomology.compactDerived R G X q`. -/
def compactComplexHomologyIso (F : SmoothTopologicalSheaf R G X) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) q).obj
        ((compactComplex R G X).obj F) ≅
      (SmoothSheafCohomology.compactDerived R G X q).obj F :=
  DerivedPlus.homologyIso (smoothSheafCompactSections R G X) (injectiveResolution F) q

theorem isZero_compactComplex_homology (F : SmoothTopologicalSheaf R G X) {n : ℤ}
    (hn : n < 0) :
    Limits.IsZero ((DerivedCategory.Plus.homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) n).obj
      ((compactComplex R G X).obj F)) :=
  DerivedPlus.isZero_homology_of_neg (smoothSheafCompactSections R G X) F hn

end Smooth

section Invariants

variable [HasDerivedCategory.{w''} (ModuleCat.{u} R)]

/-- The derived complex of invariant compact sections of smooth sheaves. -/
def invariantCompactComplex :
    SmoothTopologicalSheaf R G X ⥤ DerivedCategory.Plus (ModuleCat.{u} R) :=
  DerivedPlus.derivedComplex (SmoothSheafCohomology.invariantCompactSections R G X)

/-- Cohomology of the derived invariant compact section complex in degree `q`
is `SmoothSheafCohomology.invariantCompactDerived R G X q`. -/
def invariantCompactComplexHomologyIso (F : SmoothTopologicalSheaf R G X) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).obj
        ((invariantCompactComplex R G X).obj F) ≅
      (SmoothSheafCohomology.invariantCompactDerived R G X q).obj F :=
  DerivedPlus.homologyIso (SmoothSheafCohomology.invariantCompactSections R G X)
    (injectiveResolution F) q

theorem isZero_invariantCompactComplex_homology (F : SmoothTopologicalSheaf R G X) {n : ℤ}
    (hn : n < 0) :
    Limits.IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).obj
      ((invariantCompactComplex R G X).obj F)) :=
  DerivedPlus.isZero_homology_of_neg (SmoothSheafCohomology.invariantCompactSections R G X) F hn

end Invariants

end Langlands.Cohomology.SmoothSheafDerivedComplex
