import Langlands.Cohomology.DerivedPlus
import Langlands.Cohomology.EquivariantDerivedSections

/-!
# Derived section complexes of equivariant sheaves

The derived global and compactly supported section complexes of an equivariant
module sheaf, as objects of the bounded below derived category of
representations, together with the derived complexes of invariant sections.
Their cohomology in each degree `q ≥ 0` is the corresponding derived functor,
and it vanishes in negative degrees.
-/

noncomputable section

namespace Langlands.Cohomology.EquivariantDerivedComplex

open CategoryTheory Langlands.Sheaf.Equivariant

universe w w' w'' u

variable (R : Type u) [CommRing R] (G : Type u) [Group G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable [HasDerivedCategory.{w} (TopologicalSheaf G X (ModuleCat.{u} R))]

section Representations

variable [HasDerivedCategory.{w'} (Rep.{u} R G)]

/-- The derived global section complex, in the bounded below derived category
of representations. -/
def globalComplex : TopologicalSheaf G X (ModuleCat.{u} R) ⥤ DerivedCategory.Plus (Rep.{u} R G) :=
  DerivedPlus.derivedComplex (sectionRepresentation R G X)

/-- The derived compactly supported section complex, in the bounded below
derived category of representations. -/
def compactComplex : TopologicalSheaf G X (ModuleCat.{u} R) ⥤ DerivedCategory.Plus (Rep.{u} R G) :=
  DerivedPlus.derivedComplex (CompactSections.functor R G X)

/-- Cohomology of the derived global section complex in degree `q` is
`globalDerived R G X q`. -/
def globalComplexHomologyIso (F : TopologicalSheaf G X (ModuleCat.{u} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (Rep.{u} R G) q).obj ((globalComplex R G X).obj F) ≅
      (EquivariantDerivedSections.globalDerived R G X q).obj F :=
  DerivedPlus.homologyIso (sectionRepresentation R G X) (injectiveResolution F) q

/-- Cohomology of the derived compact section complex in degree `q` is
`compactDerived R G X q`. -/
def compactComplexHomologyIso (F : TopologicalSheaf G X (ModuleCat.{u} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (Rep.{u} R G) q).obj ((compactComplex R G X).obj F) ≅
      (EquivariantDerivedSections.compactDerived R G X q).obj F :=
  DerivedPlus.homologyIso (CompactSections.functor R G X) (injectiveResolution F) q

theorem isZero_globalComplex_homology (F : TopologicalSheaf G X (ModuleCat.{u} R)) {n : ℤ}
    (hn : n < 0) :
    Limits.IsZero ((DerivedCategory.Plus.homologyFunctor (Rep.{u} R G) n).obj
      ((globalComplex R G X).obj F)) :=
  DerivedPlus.isZero_homology_of_neg (sectionRepresentation R G X) F hn

theorem isZero_compactComplex_homology (F : TopologicalSheaf G X (ModuleCat.{u} R)) {n : ℤ}
    (hn : n < 0) :
    Limits.IsZero ((DerivedCategory.Plus.homologyFunctor (Rep.{u} R G) n).obj
      ((compactComplex R G X).obj F)) :=
  DerivedPlus.isZero_homology_of_neg (CompactSections.functor R G X) F hn

end Representations

section Invariants

variable [HasDerivedCategory.{w''} (ModuleCat.{u} R)]

/-- The derived complex of invariant global sections. -/
def invariantGlobalComplex :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤ DerivedCategory.Plus (ModuleCat.{u} R) :=
  DerivedPlus.derivedComplex (EquivariantDerivedSections.invariantGlobalSections R G X)

/-- The derived complex of invariant compactly supported sections. -/
def invariantCompactComplex :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤ DerivedCategory.Plus (ModuleCat.{u} R) :=
  DerivedPlus.derivedComplex (EquivariantDerivedSections.invariantCompactSections R G X)

/-- Cohomology of the derived invariant global section complex in degree `q`
is `invariantGlobalDerived R G X q`. -/
def invariantGlobalComplexHomologyIso (F : TopologicalSheaf G X (ModuleCat.{u} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).obj
        ((invariantGlobalComplex R G X).obj F) ≅
      (EquivariantDerivedSections.invariantGlobalDerived R G X q).obj F :=
  DerivedPlus.homologyIso (EquivariantDerivedSections.invariantGlobalSections R G X)
    (injectiveResolution F) q

/-- Cohomology of the derived invariant compact section complex in degree `q`
is `invariantCompactDerived R G X q`. -/
def invariantCompactComplexHomologyIso (F : TopologicalSheaf G X (ModuleCat.{u} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).obj
        ((invariantCompactComplex R G X).obj F) ≅
      (EquivariantDerivedSections.invariantCompactDerived R G X q).obj F :=
  DerivedPlus.homologyIso (EquivariantDerivedSections.invariantCompactSections R G X)
    (injectiveResolution F) q

end Invariants

end Langlands.Cohomology.EquivariantDerivedComplex
