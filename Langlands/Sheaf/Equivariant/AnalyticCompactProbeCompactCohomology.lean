import Langlands.Geometry.Analytic.CompactProbeQuasiEtalePoints
import Langlands.Sheaf.Equivariant.AnalyticCompactProbeGlobalCohomology

/-! # Compactly supported cohomology for the compact-probe quasi-étale topology -/

noncomputable section

universe u v uL z w₁ w₂

namespace Langlands.Sheaf.Equivariant.Analytic

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver Langlands.Sheaf.PointSupport
open Langlands.Cohomology.DiscreteSheafDerivedComplex

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
  [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}

local instance : TopologicalSpace ((localizedFieldPointFunctor L).obj X) := pointTopology L X

/-- The compact-support condition on the field-valued points is compactness of the
closure of their support image in the Hausdorff space `|X|`, when the field realizes
all underlying points. -/
theorem compactProbe_isCompactlySupported_iff [T2Space (localizedSpaceFunctor.obj X)]
    (hL : Function.Surjective (pointProjection L X)) {R : Type (max u (v + 1) uL)} [CommRing R]
    {F : (QuasiEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R} {U : QuasiEtaleSite X}
    (s : F.obj (op U)) :
    IsCompactlySupported (QuasiEtaleSite.compactProbeGeometricPoint L) F s ↔
      IsCompact (closure (pointProjection L X ''
        support (QuasiEtaleSite.compactProbeGeometricPoint L) F s)) := by
  refine (exists_isCompact_superset_iff_of_surjective L hL _).trans ?_
  exact ⟨fun ⟨C, hC, hs⟩ => hC.of_isClosed_subset isClosed_closure (closure_minimal hs hC.isClosed),
    fun hc => ⟨_, hc, subset_closure⟩⟩

section Ordinary

variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Compactly supported sections of ordinary module sheaves on the compact-probe site. -/
abbrev compactProbeQuasiEtaleCompactSections :
    Sheaf (compactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      ModuleCat.{max u (v + 1) uL} R :=
  sheafCompactSections (compactProbeQuasiEtaleTopology X)
    (QuasiEtaleSite.compactProbeGeometricPoint L) R (quasiEtaleSelf X)

/-- Compactly supported sections include into the ordinary global sections functor. -/
def compactProbeQuasiEtaleCompactInclusion :
    compactProbeQuasiEtaleCompactSections L R (X := X) ⟶
      compactProbeQuasiEtaleSections.{u, v, uL} X R :=
  Functor.whiskerLeft (sheafToPresheaf (compactProbeQuasiEtaleTopology X) _)
    (compactSectionsι (QuasiEtaleSite.compactProbeGeometricPoint L) R (quasiEtaleSelf X))

/-- On compact `|X|` all ordinary global sections have compact support when the field
realizes every point of `|X|`. -/
def compactProbeQuasiEtaleCompactSectionsIso [CompactSpace (localizedSpaceFunctor.obj X)]
    (hL : Function.Surjective (pointProjection L X)) :
    compactProbeQuasiEtaleCompactSections L R (X := X) ≅ compactProbeQuasiEtaleSections.{u, v, uL} X R := by
  haveI : IsIso (compactProbeQuasiEtaleCompactInclusion L R (X := X)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro F
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨Subtype.val_injective, fun s => ⟨⟨s, ?_⟩, rfl⟩⟩
    exact (exists_isCompact_superset_iff_of_surjective L hL _).2
      ⟨Set.univ, isCompact_univ, Set.subset_univ _⟩
  exact asIso (compactProbeQuasiEtaleCompactInclusion L R (X := X))

/-- Ordinary compactly supported cohomology for the compact-probe site. -/
def compactProbeQuasiEtaleCompactCohomology (q : ℕ) :
    Sheaf (compactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      ModuleCat.{max u (v + 1) uL} R :=
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := compactProbeQuasiEtale_hasSheafify.{u, v, uL} X R
  haveI := compactProbeQuasiEtale_enoughInjectives.{u, v, uL} X R
  compactDerived (compactProbeQuasiEtaleTopology X) (QuasiEtaleSite.compactProbeGeometricPoint L)
    R (quasiEtaleSelf X) q

variable [HasDerivedCategory.{w₁} (ModuleCat.{max u (v + 1) uL} R)]

/-- The bounded below derived complex of ordinary compactly supported sections. -/
def compactProbeQuasiEtaleCompactComplex :
    Sheaf (compactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      DerivedCategory.Plus (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := compactProbeQuasiEtale_hasSheafify.{u, v, uL} X R
  haveI := compactProbeQuasiEtale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard
    (Sheaf (compactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  sheafCompactComplex (compactProbeQuasiEtaleTopology X) (QuasiEtaleSite.compactProbeGeometricPoint L)
    R (quasiEtaleSelf X)

/-- Degreewise ordinary cohomology of the derived compactly supported complex. -/
def compactProbeQuasiEtaleCompactComplexHomologyIso
    (F : Sheaf (compactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) q).obj
        ((compactProbeQuasiEtaleCompactComplex L R).obj F) ≅
      (compactProbeQuasiEtaleCompactCohomology L R q).obj F :=
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := compactProbeQuasiEtale_hasSheafify.{u, v, uL} X R
  haveI := compactProbeQuasiEtale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard
    (Sheaf (compactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  sheafCompactComplexHomologyIso (compactProbeQuasiEtaleTopology X)
    (QuasiEtaleSite.compactProbeGeometricPoint L) R (quasiEtaleSelf X) F q

end Ordinary

section Equivariant

variable {G : Type z} [Group G] (ρ : G →* Aut X)

/-- Translation by `G` identifies the corresponding fibre functors. -/
def compactProbeGeometricPointEquivariance :
    letI := EtaleSite.pointAction L ρ
    PointEquivariance (J := compactProbeQuasiEtaleTopology X) ρ
      (QuasiEtaleSite.compactProbeGeometricPoint L) :=
  OverSite.pointEquivariance quasiEtale L ρ (compactProbeQuasiEtaleTopology X)
    (QuasiEtaleSite.compactProbePointAxioms L)

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Smooth compactly supported sections of a compact-probe `G`-sheaf. -/
def compactProbeQuasiEtaleGSheafCompactSections :
    CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  discreteCompactSections (compactProbeQuasiEtaleTopology X) R (compactLiftSystem ρ)
    (compactProbeGeometricPointEquivariance L ρ)

variable [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedCompactProbeQuasiEtaleTopology ρ)]

/-- Equivariant compactly supported cohomology with its smooth `G`-action. -/
def compactProbeQuasiEtaleGSheafCompactCohomology (q : ℕ) :
    CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := compactProbeQuasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  discreteCompactDerived (compactProbeQuasiEtaleTopology X) R (compactLiftSystem ρ)
    (compactProbeGeometricPointEquivariance L ρ) q

/-- Comparison with the ordinary compactly supported cohomology of the restriction. -/
def compactProbeQuasiEtaleCompactComparison (q : ℕ) :
    compactProbeQuasiEtaleGSheafCompactCohomology L ρ R q ⋙ smoothForget R G ⟶
      compactProbeQuasiEtaleGSheafRestriction.{u, v, uL} ρ R ⋙
        compactProbeQuasiEtaleCompactCohomology L R q :=
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := compactProbeQuasiEtale_hasSheafify.{u, v, uL} X R
  haveI := compactProbeQuasiEtale_enoughInjectives.{u, v, uL} X R
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  haveI := Cohomology.DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL}
    ρ R
  compactComparison (compactProbeQuasiEtaleTopology X) R (compactLiftSystem ρ)
    (compactProbeGeometricPointEquivariance L ρ) q

variable [HasDerivedCategory.{w₂} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]

/-- The equivariant compactly supported complex in the bounded below derived category
of smooth representations. -/
def compactProbeQuasiEtaleGSheafCompactComplex :
    CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      DerivedCategory.Plus (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) :=
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard
    (CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  compactComplex (compactProbeQuasiEtaleTopology X) R (compactLiftSystem ρ)
    (compactProbeGeometricPointEquivariance L ρ)

/-- Degreewise smooth cohomology of the equivariant compactly supported complex. -/
def compactProbeQuasiEtaleGSheafCompactComplexHomologyIso
    (F : CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) q).obj
        ((compactProbeQuasiEtaleGSheafCompactComplex L ρ R).obj F) ≅
      (compactProbeQuasiEtaleGSheafCompactCohomology L ρ R q).obj F :=
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard
    (CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  compactComplexHomologyIso (compactProbeQuasiEtaleTopology X) R (compactLiftSystem ρ)
    (compactProbeGeometricPointEquivariance L ρ) F q

end Equivariant

end Langlands.Sheaf.Equivariant.Analytic
