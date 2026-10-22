import Langlands.Cohomology.TopologicalDerivedSections
import Langlands.Geometry.EtaleGodement
import Langlands.Geometry.EtaleDerivedSections
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.Points

/-!
# Flasque Godement resolutions and cohomology with supports

These proposition definitions concern the published Godement, compact-support
and derived-section constructions. Flasqueness, acyclicity and the comparison
isomorphisms are conclusions; none is supplied as data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.Flasque

universe u

/-- The standard points of the open-set site, one for each point of the space. -/
abbrev spacePoints (X : TopCat.{u}) :
    X → GrothendieckTopology.Point.{u} (Opens.grothendieckTopology X) :=
  fun x => Opens.pointGrothendieckTopology x

/-- The Godement complex of a module sheaf, built from all points of the space. -/
abbrev godementComplex (X : TopCat.{u}) (R : Type u) [CommRing R]
    (F : TopCat.Sheaf (ModuleCat.{u} R) X) :
    CochainComplex (TopCat.Sheaf (ModuleCat.{u} R) X) ℕ :=
  Sheaf.Godement.complex (spacePoints X) (ModuleCat.{u} R) F

end Langlands.Cohomology.Flasque

namespace Langlands.Cohomology

universe u

open Flasque

/-- Every term of the Godement complex of a module sheaf is flasque. -/
def GodementTermFlasqueStatement : Prop :=
  ∀ (X : TopCat.{u}) (R : Type u) [CommRing R]
    (F : TopCat.Sheaf (ModuleCat.{u} R) X) (n : ℕ),
    ((godementComplex X R F).X n).IsFlasque

/-- If the first two terms of a short exact sequence are flasque, so is the third,
and ordinary and compactly supported sections stay short exact. -/
def FlasqueShortExactStatement : Prop :=
  ∀ (X : TopCat.{u}) (R : Type u) [CommRing R]
    (S : ShortComplex (TopCat.Sheaf (ModuleCat.{u} R) X)),
    S.ShortExact → S.X₁.IsFlasque → S.X₂.IsFlasque →
      S.X₃.IsFlasque ∧
      (S.map (Sheaf.CompactSupport.globalSections (X := X) (R := R))).ShortExact ∧
      (S.map (Sheaf.CompactSupport.functor (X := X) (R := R))).ShortExact

/-- Injective module sheaves are flasque. -/
def InjectiveSheafFlasqueStatement : Prop :=
  ∀ (X : TopCat.{u}) (R : Type u) [CommRing R]
    (I : TopCat.Sheaf (ModuleCat.{u} R) X), Injective I → I.IsFlasque

/-- Flasque module sheaves have no higher ordinary or compactly supported cohomology. -/
def FlasqueAcyclicityStatement : Prop :=
  ∀ (X : TopCat.{u}) (R : Type u) [CommRing R]
    (F : TopCat.Sheaf (ModuleCat.{u} R) X), F.IsFlasque →
    ∀ q : ℕ,
      IsZero ((TopologicalDerivedSections.ordinaryCohomology X R (q + 1)).obj F) ∧
      IsZero ((TopologicalDerivedSections.compactCohomology X R (q + 1)).obj F)

/-- The Godement complex computes ordinary and compactly supported cohomology.
The augmentation chain map is pinned by its degree-zero component. -/
def GodementComputesCohomologyStatement : Prop :=
  ∀ (X : TopCat.{u}) (R : Type u) [CommRing R]
    (F : TopCat.Sheaf (ModuleCat.{u} R) X)
    (ε : (CochainComplex.single₀ (TopCat.Sheaf (ModuleCat.{u} R) X)).obj F ⟶
      godementComplex X R F),
    ε.f 0 = Sheaf.Godement.augmentation (spacePoints X) (ModuleCat.{u} R) F →
    ∀ (I : InjectiveResolution F) (φ : godementComplex X R F ⟶ I.cocomplex),
      ε ≫ φ = I.ι →
      ∀ n : ℕ,
        IsIso
          (((Sheaf.CompactSupport.globalSections (X := X) (R := R)).mapHomologicalComplex _ ⋙
              HomologicalComplex.homologyFunctor _ _ n).map φ ≫
            (I.isoRightDerivedObj (Sheaf.CompactSupport.globalSections (X := X) (R := R)) n).inv) ∧
        IsIso
          (((Sheaf.CompactSupport.functor (X := X) (R := R)).mapHomologicalComplex _ ⋙
              HomologicalComplex.homologyFunctor _ _ n).map φ ≫
            (I.isoRightDerivedObj (Sheaf.CompactSupport.functor (X := X) (R := R)) n).inv)

/-- On a compact space, forgetting compact support is an isomorphism in every degree. -/
def CompactSpaceSupportComparisonStatement : Prop :=
  ∀ (X : TopCat.{u}) [CompactSpace X] (R : Type u) [CommRing R] (n : ℕ),
    IsIso (TopologicalDerivedSections.forgetSupport X R n)

/-- Every term of the geometric-point Godement complex on the small etale site
has no higher etale cohomology. -/
def EtaleGodementTermAcyclicStatement : Prop :=
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (R : Type u) [CommRing R]
    (F : Geometry.EtaleGodement.EtaleSheaf X R) (n q : ℕ),
    IsZero ((Geometry.EtaleDerivedSections.cohomology X R (q + 1)).obj
      ((Geometry.EtaleGodement.complex X R F).X n))

/-- The geometric-point Godement complex computes small-etale cohomology. -/
def EtaleGodementComputesCohomologyStatement : Prop :=
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (R : Type u) [CommRing R]
    (F : Geometry.EtaleGodement.EtaleSheaf X R)
    (ε : (CochainComplex.single₀ (Geometry.EtaleGodement.EtaleSheaf X R)).obj F ⟶
      Geometry.EtaleGodement.complex X R F),
    ε.f 0 = (Geometry.EtaleGodement.coaugmentation X R).app F →
    ∀ (I : InjectiveResolution F)
      (φ : Geometry.EtaleGodement.complex X R F ⟶ I.cocomplex),
      ε ≫ φ = I.ι →
      ∀ n : ℕ,
        IsIso
          (((Geometry.EtaleDerivedSections.sections X R).mapHomologicalComplex _ ⋙
              HomologicalComplex.homologyFunctor _ _ n).map φ ≫
            (I.isoRightDerivedObj (Geometry.EtaleDerivedSections.sections X R) n).inv)

/-- The flasque, Godement and support-comparison family.
No component is assumed to define the conjunction. -/
def FlasqueGodementCohomologyStatements : Prop :=
  GodementTermFlasqueStatement.{u} ∧
  FlasqueShortExactStatement.{u} ∧
  InjectiveSheafFlasqueStatement.{u} ∧
  FlasqueAcyclicityStatement.{u} ∧
  GodementComputesCohomologyStatement.{u} ∧
  CompactSpaceSupportComparisonStatement.{u} ∧
  EtaleGodementTermAcyclicStatement.{u} ∧
  EtaleGodementComputesCohomologyStatement.{u}

end Langlands.Cohomology
