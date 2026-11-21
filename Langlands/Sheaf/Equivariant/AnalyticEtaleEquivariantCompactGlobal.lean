import Langlands.Sheaf.Equivariant.AnalyticEtaleCompactGlobal
import Langlands.Sheaf.Equivariant.AnalyticEtaleGlobalComplex

/-!
# Compact and ordinary equivariant étale sections on compact bases

When the underlying space is compact and every point comes from an `L`-valued
point, the support condition imposes no restriction. The identification is
made on the actual section representations, then on their smooth parts,
invariants, and right derived functors in the model category of `G`-sheaves.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Cohomology Langlands.Sheaf.Equivariant.TwistedOver

namespace Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Forgetting compact support is equivariant for the actual section actions. -/
def etaleCompactSectionsRepInclusion :
    etaleCompactSectionsRep L ρ h R ⟶ sheafGlobalSectionsRep (etaleTopology X) R (ρ := ρ) where
  app F := Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((etaleCompactSectionsInclusion L h R).app ((TwistedOver.restriction ρ (etaleTopology X)
      (ModuleCat.{max u (v + 1) uL} R)).obj F)).hom (fun _ _ => rfl))
  naturality _ _ _ := by
    ext
    rfl

/-- The equivariant inclusion is invertible under the same hypotheses as the
inclusion of underlying modules. -/
theorem isIso_etaleCompactSectionsRepInclusion_of_compactSpace
    [CompactSpace (localizedSpaceFunctor.obj X)] (hX : Function.Surjective (pointProjection L X)) :
    IsIso (etaleCompactSectionsRepInclusion L ρ h R) := by
  have := isIso_etaleCompactSectionsInclusion_of_compactSpace L h R hX
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  apply (ConcreteCategory.isIso_iff_bijective _).2
  exact (ConcreteCategory.isIso_iff_bijective ((etaleCompactSectionsInclusion L h R).app
    ((TwistedOver.restriction ρ (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)).obj F))).1 inferInstance

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace (localizedSpaceFunctor.obj X)] (hX : Function.Surjective (pointProjection L X))

/-- Compactly supported and ordinary smooth sections agree on compact `|X|`. -/
def etaleGSheafCompactSectionsIsoOfCompactSpace :
    etaleGSheafCompactSections L ρ h R ≅ etaleGSheafSections.{u, v, uL} ρ R :=
  haveI := isIso_etaleCompactSectionsRepInclusion_of_compactSpace L ρ h R hX
  Functor.isoWhiskerLeft ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)
    (Functor.isoWhiskerRight (asIso (etaleCompactSectionsRepInclusion L ρ h R))
      (SmoothRep.smoothPartFunctor R G))

/-- The same identification for invariant sections. -/
def etaleGSheafInvariantCompactSectionsIsoOfCompactSpace :
    etaleGSheafInvariantCompactSections L ρ h R ≅ etaleGSheafInvariantSections.{u, v, uL} ρ R :=
  Functor.isoWhiskerRight (etaleGSheafCompactSectionsIsoOfCompactSpace L ρ h R hX)
    (smoothInvariantsFunctor.{max u (v + 1) uL, z, max u (v + 1) uL} R G)

variable [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- Derive a natural isomorphism of additive functors. -/
private def rightDerivedIso {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [EnoughInjectives C] {F F' : C ⥤ D} [F.Additive] [F'.Additive]
    (e : F ≅ F') (q : ℕ) : F.rightDerived q ≅ F'.rightDerived q where
  hom := NatTrans.rightDerived e.hom q
  inv := NatTrans.rightDerived e.inv q
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

/-- All degrees of derived smooth sections, still in smooth representations. -/
def etaleGSheafCompactCohomologyIsoOfCompactSpace (q : ℕ) :
    etaleGSheafCompactCohomology L ρ h R q ≅ etaleGSheafCohomology.{u, v, uL} ρ R q :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  rightDerivedIso (etaleGSheafCompactSectionsIsoOfCompactSpace L ρ h R hX) q

/-- All degrees of derived invariant sections. -/
def etaleGSheafInvariantCompactCohomologyIsoOfCompactSpace (q : ℕ) :
    etaleGSheafInvariantCompactCohomology L ρ h R q ≅ etaleGSheafInvariantCohomology.{u, v, uL} ρ R q :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  rightDerivedIso (etaleGSheafInvariantCompactSectionsIsoOfCompactSpace L ρ h R hX) q

universe w

variable [HasDerivedCategory.{w} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]

/-- The two bounded-below complexes are isomorphic at each sheaf, by the
compact-support inclusion on a single injective resolution. -/
def etaleGSheafCompactComplexIsoOfCompactSpace
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    (etaleGSheafCompactComplex L ρ h R).obj F ≅ (etaleGSheafComplex.{u, v, uL} ρ R).obj F := by
  letI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  letI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  let I := injectiveResolution F
  let Fc := etaleGSheafCompactSections L ρ h R
  let Fo := etaleGSheafSections.{u, v, uL} ρ R
  let e : Fc ≅ Fo := etaleGSheafCompactSectionsIsoOfCompactSpace L ρ h R hX
  let eI : (Fc.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex ≅
      (Fo.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex :=
    HomologicalComplex.Hom.isoOfComponents (fun i => e.app (I.cochainComplex.X i))
      (fun i j _ => (e.hom.naturality (I.cochainComplex.d i j)).symm)
  let eIPlus : Fc.mapCochainComplexPlus.obj (DerivedPlus.resolutionPlus I) ≅
      Fo.mapCochainComplexPlus.obj (DerivedPlus.resolutionPlus I) :=
    (CochainComplex.Plus.fullyFaithfulι _).preimageIso eI
  exact DerivedPlus.derivedComplexIso Fc I ≪≫ DerivedCategory.Plus.Q.mapIso eIPlus ≪≫
    (DerivedPlus.derivedComplexIso Fo I).symm

end Langlands.Sheaf.Equivariant.Analytic
