import Langlands.Cohomology.SmoothSheafCohomology
import Langlands.Cohomology.EquivariantGodementCohomology

/-!
# Derived compact sections of smooth sheaves and Godement compact cohomology

For a topological group acting on a locally compact Hausdorff space with
neighbourhoods stable under open subgroups, these statements compare two
compactly supported cohomologies of a smooth equivariant module sheaf: the
right derived functors of compact sections in the abelian category of smooth
equivariant sheaves, and compactly supported Godement cohomology. Injective
smooth sheaves are acyclic for the latter, and the two agree in every degree
by natural isomorphisms of representations that are the canonical
identifications in degree zero. This is the ordinary-topology analogue of the
isomorphisms `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` in Berkovich, *Étale
equivariant sheaves on p-adic analytic spaces*, Corollary 1.5.2(i).
-/

namespace Langlands.Cohomology.SmoothCompactComparison

open CategoryTheory CategoryTheory.Limits Langlands.Sheaf.Equivariant

universe u

/-- Injective objects of the category of smooth equivariant module sheaves have
no compactly supported Godement cohomology in positive degrees. -/
def SmoothInjectiveCompactAcyclicStatement (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MulAction G X] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] : Prop :=
  ∀ I : SmoothTopologicalSheaf R G X, Injective I → ∀ q : ℕ,
    IsZero ((EquivariantGodementCohomology.compactCohomology R G X (q + 1)).obj
      ((Langlands.Sheaf.Equivariant.smoothInclusion R G X).obj I))

/-- In every degree, the derived compact sections of smooth equivariant module
sheaves, as representations, are naturally isomorphic to compactly supported
Godement cohomology; in degree zero the isomorphism is the composite of the
published identifications of both sides with compact sections. -/
def SmoothCompactDerivedComparisonStatement (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MulAction G X] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] : Prop :=
  ∃ e : ∀ q : ℕ,
      SmoothSheafCohomology.compactDerived R G X q ⋙ Langlands.SmoothRep.toRep ≅
        Langlands.Sheaf.Equivariant.smoothInclusion R G X ⋙
          EquivariantGodementCohomology.compactCohomology R G X q,
    (e 0).hom =
      Functor.whiskerRight (SmoothSheafCohomology.compactDerivedZeroIso R G X).hom
          Langlands.SmoothRep.toRep ≫
        (Langlands.Sheaf.Equivariant.smoothSheafCompactSectionsToRepIso R G X).hom ≫
          Functor.whiskerLeft (Langlands.Sheaf.Equivariant.smoothInclusion R G X)
            (EquivariantGodementCohomology.compactCohomologyZeroIso R G X).inv

/-- The acyclicity and comparison statements together. -/
def SmoothCompactComparisonStatements (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MulAction G X] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] : Prop :=
  SmoothInjectiveCompactAcyclicStatement R G X ∧ SmoothCompactDerivedComparisonStatement R G X

end Langlands.Cohomology.SmoothCompactComparison
