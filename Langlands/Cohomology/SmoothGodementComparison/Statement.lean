import Langlands.Cohomology.SmoothGodementCohomology
import Langlands.Sheaf.Godement.ExactnessStatement

/-!
# Smooth Godement compact cohomology computes derived compact sections

Worker 61's compactly supported smooth Godement cohomology of a smooth
equivariant module sheaf is the homology of compact sections of its smooth
Godement complex. These proposition definitions compare it with the right
derived functors of compact sections in the abelian category of smooth
equivariant sheaves. The comparison map is the one induced by a lift of the
smooth Godement complex to an injective resolution, compatible with the
augmentations. On a locally compact Hausdorff space it is an isomorphism in
every degree, and these isomorphisms form a natural isomorphism of functors to
smooth representations; in degree zero the comparison map is the composite of
the published identifications of both sides with compact sections. This is the
ordinary-topology analogue of the use of the smooth Godement resolutions of
Harris 1999, Lemma 2.2, p.304, and of Berkovich's Corollary 1.5.2(i).
Invertibility and naturality are conclusions; none is supplied as data.
-/

noncomputable section

namespace Langlands.Cohomology.SmoothGodementComparison

open CategoryTheory CategoryTheory.Limits Langlands.Sheaf.Equivariant

universe u

/-- The degree-`q` comparison map from compactly supported smooth Godement
cohomology to derived compact sections induced by a map `φ` from the smooth
Godement complex to an injective resolution `I`: the map of homology of
compact sections, followed by the inverse of the published identification
`compactDerivedIso` of the derived functor with the homology of compact
sections of `I`. -/
def comparisonMap (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
    [HasStableNeighbourhoods G X] {F : SmoothTopologicalSheaf R G X}
    (I : InjectiveResolution F) (φ : Godement.smoothComplex R G X F ⟶ I.cocomplex)
    (q : ℕ) :
    (SmoothGodementCohomology.smoothGodementCompactCohomology R G X q).obj F ⟶
      (SmoothSheafCohomology.compactDerived R G X q).obj F :=
  ((smoothSheafCompactSections R G X).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q).map φ ≫
    (SmoothSheafCohomology.compactDerivedIso R G X I q).inv

/-- In degree zero, the comparison map induced by an augmentation-compatible
lift is the composite of the identifications of both sides with compact
sections. -/
def SmoothGodementComparisonZeroStatement (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
    [HasStableNeighbourhoods G X] : Prop :=
  ∀ (F : SmoothTopologicalSheaf R G X) (I : InjectiveResolution F)
    (φ : Godement.smoothComplex R G X F ⟶ I.cocomplex),
    CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
        (Godement.smoothCoaugmentation R G X) F ≫ φ = I.ι →
    comparisonMap R G X I φ 0 =
      (SmoothGodementCohomology.smoothGodementCompactCohomologyZeroIso R G X).hom.app F ≫
        (SmoothSheafCohomology.compactDerivedZeroIso R G X).inv.app F

/-- On a locally compact Hausdorff space, the comparison map induced by an
augmentation-compatible lift is an isomorphism in every degree. -/
def SmoothGodementComparisonIsIsoStatement (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MulAction G X] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] : Prop :=
  ∀ (F : SmoothTopologicalSheaf R G X) (I : InjectiveResolution F)
    (φ : Godement.smoothComplex R G X F ⟶ I.cocomplex),
    CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
        (Godement.smoothCoaugmentation R G X) F ≫ φ = I.ι →
    ∀ q : ℕ, IsIso (comparisonMap R G X I φ q)

/-- On a locally compact Hausdorff space, there are natural isomorphisms from
compactly supported smooth Godement cohomology to derived compact sections
whose components are the comparison maps of all augmentation-compatible lifts
to all injective resolutions. -/
def SmoothGodementComparisonNaturalStatement (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MulAction G X] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] : Prop :=
  ∃ e : ∀ q : ℕ,
      SmoothGodementCohomology.smoothGodementCompactCohomology R G X q ≅
        SmoothSheafCohomology.compactDerived R G X q,
    ∀ (F : SmoothTopologicalSheaf R G X) (I : InjectiveResolution F)
      (φ : Godement.smoothComplex R G X F ⟶ I.cocomplex),
      CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
          (Godement.smoothCoaugmentation R G X) F ≫ φ = I.ι →
      ∀ q : ℕ, (e q).hom.app F = comparisonMap R G X I φ q

/-- The degree-zero, invertibility and naturality statements together. No
component is assumed to define the conjunction. -/
def SmoothGodementComparisonStatements (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MulAction G X] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] : Prop :=
  SmoothGodementComparisonZeroStatement R G X ∧
    SmoothGodementComparisonIsIsoStatement R G X ∧
    SmoothGodementComparisonNaturalStatement R G X

end Langlands.Cohomology.SmoothGodementComparison
