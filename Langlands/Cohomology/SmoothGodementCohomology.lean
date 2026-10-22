import Langlands.Sheaf.Equivariant.Godement.Smooth
import Langlands.Cohomology.SmoothSheafCohomology
import Langlands.Cohomology.EquivariantGodementCohomology

/-!
# Compactly supported cohomology through the smooth Godement complex

Compact sections of the smooth equivariant Godement complex of a smooth
equivariant module sheaf form a cochain complex of smooth representations, and
invariant compact sections form a cochain complex of modules. Their homology is
the smooth Godement-route compactly supported cohomology. In degree zero it
recovers the compact sections and the invariant compact sections, because the
smooth Godement coaugmentation is monic and both section functors are left
exact.
-/

noncomputable section

namespace Langlands.Cohomology.SmoothGodementCohomology

open CategoryTheory CategoryTheory.Limits Langlands.Sheaf.Equivariant

universe u

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable [HasStableNeighbourhoods G X]

/-- Compact sections of the smooth Godement complex, as a cochain complex of
smooth representations. -/
def smoothGodementCompactComplex :
    SmoothTopologicalSheaf R G X ⥤ CochainComplex (Langlands.SmoothRep.{u, u, u} R G) ℕ :=
  Godement.smoothComplexFunctor R G X ⋙
    (smoothSheafCompactSections R G X).mapHomologicalComplex (ComplexShape.up ℕ)

/-- Forgetting smoothness of the terms gives compact sections of the smooth
Godement complex, viewed in the ambient equivariant sheaf category, as a
complex of representations. -/
def smoothGodementCompactComplexToRepIso :
    smoothGodementCompactComplex R G X ⋙
        (Langlands.SmoothRep.toRep (R := R) (G := G)).mapHomologicalComplex (ComplexShape.up ℕ) ≅
      Godement.smoothComplexFunctor R G X ⋙
        (Langlands.Sheaf.Equivariant.smoothInclusion R G X ⋙
          CompactSections.functor R G X).mapHomologicalComplex
          (ComplexShape.up ℕ) :=
  Functor.isoWhiskerLeft (Godement.smoothComplexFunctor R G X)
    (Functor.mapHomologicalComplexCompIso (smoothSheafCompactSectionsToRepIso R G X)
      (ComplexShape.up ℕ))

/-- Degree `q` compactly supported smooth Godement cohomology, as a smooth
representation. -/
def smoothGodementCompactCohomology (q : ℕ) :
    SmoothTopologicalSheaf R G X ⥤ Langlands.SmoothRep.{u, u, u} R G :=
  smoothGodementCompactComplex R G X ⋙
    HomologicalComplex.homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q

/-- In degree zero, compactly supported smooth Godement cohomology is the
smooth representation of compact sections. -/
def smoothGodementCompactCohomologyZeroIso :
    smoothGodementCompactCohomology R G X 0 ≅ smoothSheafCompactSections R G X :=
  EquivariantGodementCohomology.homologyZeroIso (Godement.smoothZeroFunctor R G X)
    (Godement.smoothCoaugmentation R G X) (smoothSheafCompactSections R G X)

/-- Invariant compact sections of the smooth Godement complex, as a cochain
complex of modules. -/
def smoothGodementInvariantCompactComplex :
    SmoothTopologicalSheaf R G X ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  Godement.smoothComplexFunctor R G X ⋙
    (SmoothSheafCohomology.invariantCompactSections R G X).mapHomologicalComplex
      (ComplexShape.up ℕ)

/-- Degree `q` invariant compactly supported smooth Godement cohomology. -/
def smoothGodementInvariantCompactCohomology (q : ℕ) :
    SmoothTopologicalSheaf R G X ⥤ ModuleCat.{u} R :=
  smoothGodementInvariantCompactComplex R G X ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q

/-- In degree zero, invariant compactly supported smooth Godement cohomology is
the module of invariant compact sections. -/
def smoothGodementInvariantCompactCohomologyZeroIso :
    smoothGodementInvariantCompactCohomology R G X 0 ≅
      SmoothSheafCohomology.invariantCompactSections R G X :=
  EquivariantGodementCohomology.homologyZeroIso (Godement.smoothZeroFunctor R G X)
    (Godement.smoothCoaugmentation R G X) (SmoothSheafCohomology.invariantCompactSections R G X)

end Langlands.Cohomology.SmoothGodementCohomology
