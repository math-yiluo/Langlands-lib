import Langlands.Cohomology.EquivariantGodementCohomology
import Langlands.Sheaf.Equivariant.Smooth

/-!
# Smoothness of compactly supported cohomology of smooth equivariant sheaves

For a topological group acting on a space and a smooth equivariant module sheaf
(every section is, near every point, fixed by an open subgroup stabilizing a
neighbourhood), these statements say that the group acts smoothly on
compactly supported sections and, on a locally compact Hausdorff space, on
every compactly supported Godement cohomology module. This is the
ordinary-topology analogue of the discreteness assertion in Berkovich,
*Étale equivariant sheaves on p-adic analytic spaces*, Corollary 1.5.2(i).
-/

namespace Langlands.Cohomology.SmoothCompactCohomology

open CategoryTheory Langlands.Sheaf.Equivariant

universe u

/-- Degree zero: every compactly supported global section of a smooth
equivariant module sheaf is fixed by an open subgroup. -/
def CompactSectionsSmoothStatement (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X] : Prop :=
  ∀ F : TopologicalSheaf G X (ModuleCat.{u} R), IsSmoothSheaf R G X F →
    Langlands.IsSmooth ((CompactSections.functor R G X).obj F).ρ

/-- Every degree: on a locally compact Hausdorff space, the compactly supported
Godement cohomology of a smooth equivariant module sheaf is a smooth
representation. -/
def CompactCohomologySmoothStatement (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MulAction G X] [ContinuousConstSMul G X] : Prop :=
  ∀ F : TopologicalSheaf G X (ModuleCat.{u} R), IsSmoothSheaf R G X F →
    ∀ q : ℕ, Langlands.IsSmooth
      ((EquivariantGodementCohomology.compactCohomology R G X q).obj F).ρ

/-- The two smoothness statements together. -/
def SmoothCompactCohomologyStatements (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MulAction G X] [ContinuousConstSMul G X] : Prop :=
  CompactSectionsSmoothStatement R G X ∧ CompactCohomologySmoothStatement R G X

end Langlands.Cohomology.SmoothCompactCohomology
