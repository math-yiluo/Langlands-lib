import Langlands.Cohomology.DivisibleSystem.TwistedExact
import Langlands.Sheaf.Equivariant.AnalyticEtaleComparison

/-!
# Harris's divisible systems for étale `G`-sheaves on analytic spaces

Let `G` act on an analytic space `X`. This module specializes the constructions of
`DivisibleSystem.TwistedExact` to Berkovich's étale `G`-sheaves, the locally discrete sheaves
`EtaleGSheaf` on the twisted étale site, with an arbitrary family `points` of points of the
étale site of `X` for the Godement resolutions and the compactly supported cohomology
`H^q_c(X{G}, -)` of `AnalyticEtaleCompactCohomology` (supports in the `L`-valued points). The
constructions are Harris's Lemma 2.2, Lemma 2.2 bis, (2.3), (2.6), (2.7) and Lemma 2.8 for an
arbitrary `ℓ`-divisible system of étale `G`-sheaves of modules.

The exactness of the Godement functor, the joint faithfulness of the fibre functors at the
points of the family, the acyclicity of Godement sheaves, the bound `D`, the admissible
refinements of the distinguished lift system and the point axioms are hypotheses.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] [TopologicalSpace G]
variable (ρ : G →* Aut X) (R : Type (max u (v + 1) uL)) [CommRing R]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- The inclusion of étale `G`-sheaves of modules into module sheaves on the twisted étale
site is left adjoint to the locally discrete part. -/
abbrev etaleGSheafAdjunction :
    (distinguishedLiftSystem ρ).smoothSheafInclusion (ModuleCat.{max u (v + 1) uL} R)
        (twistedEtaleTopology ρ) ⊣
      LocalActionSystem.smoothCoreflector (R := R) (distinguishedLiftSystem ρ)
        (twistedEtaleTopology ρ) :=
  LocalActionSystem.smoothAdjunction (R := R) (distinguishedLiftSystem ρ) (twistedEtaleTopology ρ)

end Langlands.Sheaf.Equivariant.Analytic

namespace Langlands.Cohomology.DivisibleSystem.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Systems

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- `ℓ`-divisible systems of étale `G`-sheaves of `R`-modules. -/
abbrev EtaleDivisibleSystem (ℓ : ℕ) : Type _ :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  DivisibleSystem (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) ℓ

/-- `ℓ`-divisible systems of complexes of étale `G`-sheaves of `R`-modules. -/
abbrev EtaleComplexDivisibleSystem (ℓ : ℕ) : Type _ :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  DivisibleSystem (CochainComplex (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) ℕ) ℓ

end Systems

section Godement

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable {I : Type (max u (v + 1) uL)}
  (points : I → (etaleTopology X).Point.{max u (v + 1) uL})
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- The degree-zero Godement functor on étale `G`-sheaves built from the family `points`: the
locally discrete part of the induction to the twisted site of the product of the skyscraper
sheaves at the points of the family. -/
abbrev etaleFamilyGodementFunctor :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  exactZeroFunctor.{max u (v + 1) uL} ρ (etaleTopology X) points R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)
    (LocalActionSystem.smoothCoreflector (R := R) (distinguishedLiftSystem ρ)
      (twistedEtaleTopology ρ))

/-- The coaugmentation `F ⟶ G⁰(F)` of the Godement functor of the family `points`. -/
abbrev etaleFamilyGodementCoaugmentation :
    𝟭 _ ⟶ etaleFamilyGodementFunctor.{u, v, uL} ρ points R :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  exactCoaugmentation.{max u (v + 1) uL} ρ (etaleTopology X) points R
    (etaleGSheafAdjunction.{u, v, uL} ρ R)

/-- If the fibre functors of the points of the family are jointly faithful, the
coaugmentation is a monomorphism. -/
theorem mono_etaleFamilyGodementCoaugmentation
    (hpoints : JointlyFaithful fun i => (points i).sheafFiber
      (A := ModuleCat.{max u (v + 1) uL} R))
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    Mono ((etaleFamilyGodementCoaugmentation.{u, v, uL} ρ points R).app F) :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  mono_exactCoaugmentation_of_jointlyFaithful.{max u (v + 1) uL} ρ (etaleTopology X) points R
    (etaleGSheafAdjunction.{u, v, uL} ρ R) hpoints F

end Godement

section Resolution

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable {I : Type (max u (v + 1) uL)}
  (points : I → (etaleTopology X).Point.{max u (v + 1) uL})
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
variable [PreservesFiniteLimits (etaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
  [PreservesFiniteColimits (etaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
variable {ℓ : ℕ} (T : EtaleDivisibleSystem.{u, v, uL} ρ R ℓ)
variable (hpoints : JointlyFaithful fun i => (points i).sheafFiber
  (A := ModuleCat.{max u (v + 1) uL} R))

/-- Harris's Lemma 2.2 for étale `G`-sheaves and the family `points`: the `ℓ`-divisible system
of the Godement resolutions `F^0 ⟶ F^1 ⟶ ⋯` of the levels of `T`. -/
def etaleFamilyGodementResolutionSystem : EtaleComplexDivisibleSystem.{u, v, uL} ρ R ℓ :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  exactGodementResolutionSystem.{max u (v + 1) uL} ρ (etaleTopology X) points R
    (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints

/-- Level `m` of the resolution system is the Godement complex of `T m`. -/
def etaleFamilyGodementResolutionSystemObjIso (m : ℕ) :
    haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    (etaleFamilyGodementResolutionSystem.{u, v, uL} ρ points R T hpoints).obj m ≅
      (exactComplexFunctor.{max u (v + 1) uL} ρ (etaleTopology X) points R
        (etaleGSheafAdjunction.{u, v, uL} ρ R)).obj (T.obj m) :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  exactGodementResolutionSystemObjIso.{max u (v + 1) uL} ρ (etaleTopology X) points R
    (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints m

/-- Every level of the resolution system is exact in positive degrees. -/
theorem etaleFamilyGodementResolutionSystem_obj_exactAt (m q : ℕ) :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    ((etaleFamilyGodementResolutionSystem.{u, v, uL} ρ points R T hpoints).obj m).ExactAt
      (q + 1) :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  exactGodementResolutionSystem_obj_exactAt.{max u (v + 1) uL} ρ (etaleTopology X) points R
    (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints m q

variable (D : ℕ)

/-- Harris's Lemma 2.2 bis for étale `G`-sheaves and the family `points`: the truncation
`G^• = τ_{≤ D+1}(F^•)` of the Godement resolution system. -/
def etaleFamilyGodementTruncatedResolutionSystem : EtaleComplexDivisibleSystem.{u, v, uL} ρ R ℓ :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  exactGodementTruncatedResolutionSystem.{max u (v + 1) uL} ρ (etaleTopology X) points R
    (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints D

/-- The inclusion `G^• ⟶ F^•` of the truncation into the Godement resolution system. -/
def etaleFamilyGodementTruncatedResolutionHom :
    etaleFamilyGodementTruncatedResolutionSystem.{u, v, uL} ρ points R T hpoints D ⟶
      etaleFamilyGodementResolutionSystem.{u, v, uL} ρ points R T hpoints :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  exactGodementTruncatedResolutionHom.{max u (v + 1) uL} ρ (etaleTopology X) points R
    (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints D

/-- At every level, the inclusion of the truncation is a quasi-isomorphism. -/
theorem quasiIso_etaleFamilyGodementTruncatedResolutionHom (m : ℕ) :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    QuasiIso ((etaleFamilyGodementTruncatedResolutionHom.{u, v, uL} ρ points R T hpoints
      D).tower.app (op m)) :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  quasiIso_exactGodementTruncatedResolutionHom.{max u (v + 1) uL} ρ (etaleTopology X) points R
    (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints D m

/-- Every level of the truncation is zero in degrees above `D + 1`. -/
theorem isZero_etaleFamilyGodementTruncatedResolutionSystem_obj_X (m : ℕ) {q : ℕ}
    (hq : D + 1 < q) :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    IsZero (((etaleFamilyGodementTruncatedResolutionSystem.{u, v, uL} ρ points R T hpoints
      D).obj m).X q) :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  isZero_exactGodementTruncatedResolutionSystem_obj_X.{max u (v + 1) uL} ρ (etaleTopology X)
    points R (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints D m hq

/-- The augmentation `T m ⟶ G^•_m`. -/
def etaleFamilyGodementTruncatedAugmentation (m : ℕ) :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    (CochainComplex.single₀ _).obj (T.obj m) ⟶
      (etaleFamilyGodementTruncatedResolutionSystem.{u, v, uL} ρ points R T hpoints D).obj m :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  exactGodementTruncatedAugmentation.{max u (v + 1) uL} ρ (etaleTopology X) points R
    (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints D m

/-- Each level of the truncation is a finite-length resolution of the level of `T`. -/
theorem quasiIso_etaleFamilyGodementTruncatedAugmentation (m : ℕ) :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    QuasiIso (etaleFamilyGodementTruncatedAugmentation.{u, v, uL} ρ points R T hpoints D m) :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  quasiIso_exactGodementTruncatedAugmentation.{max u (v + 1) uL} ρ (etaleTopology X) points R
    (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints D m

end Resolution

section Compact

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable {I : Type (max u (v + 1) uL)}
  (points : I → (etaleTopology X).Point.{max u (v + 1) uL})
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
variable [PreservesFiniteLimits (etaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
  [PreservesFiniteColimits (etaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable {ℓ : ℕ} (T : EtaleDivisibleSystem.{u, v, uL} ρ R ℓ)
variable (hpoints : JointlyFaithful fun i => (points i).sheafFiber
  (A := ModuleCat.{max u (v + 1) uL} R))
variable (D : ℕ)
variable (hF : ∀ (M : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (r : ℕ),
    IsZero ((etaleGSheafCompactCohomology L ρ h R (r + 1)).obj
      ((etaleFamilyGodementFunctor.{u, v, uL} ρ points R).obj M)))
  (hT : ∀ m n : ℕ, D < n →
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    IsZero ((etaleGSheafCompactCohomology L ρ h R n).obj (T.obj m)))

include hF hT in
/-- Every term of every level of the truncation is acyclic for `Γ_{c,X{G}}`. -/
theorem isZero_etaleGSheafCompactCohomology_familyTruncatedResolutionSystem_obj_X
    (m i r : ℕ) :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    IsZero ((etaleGSheafCompactCohomology L ρ h R (r + 1)).obj
      (((etaleFamilyGodementTruncatedResolutionSystem.{u, v, uL} ρ points R T hpoints D).obj m).X i)) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  isZero_exactCompactDerived_truncatedResolutionSystem_obj_X.{max u (v + 1) uL} ρ (etaleTopology X)
    points R (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints D (EtaleSite.pointEquivariance L ρ h) hF hT m
    i r

/-- Harris's `ℓ`-divisible system of finite-length complexes `Γ_{c,X{G}}(G^•_m)` of smooth
representations of `G`, for the Godement resolutions of the family `points`. -/
def etaleFamilyGodementTruncatedCompactSectionsSystem :
    DivisibleSystem
      (CochainComplex (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) ℕ) ℓ :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  exactGodementTruncatedCompactSectionsSystem.{max u (v + 1) uL} ρ (etaleTopology X) points R (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints D (EtaleSite.pointEquivariance L ρ h) hF hT

/-- Level `m` of the section system is the complex of compactly supported sections of
`G^•_m`. -/
theorem etaleFamilyGodementTruncatedCompactSectionsSystem_obj (m : ℕ) :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    (etaleFamilyGodementTruncatedCompactSectionsSystem.{u, v, uL} ρ points R L h T hpoints D hF
      hT).obj m =
      ((etaleGSheafCompactSections L ρ h R).mapHomologicalComplex _).obj
        ((etaleFamilyGodementTruncatedResolutionSystem.{u, v, uL} ρ points R T hpoints D).obj m) :=
  rfl

/-- Harris (2.3) for étale `G`-sheaves and the family `points`: the cohomology of level
`m` of the compact section complexes is `H^n_c(X{G}, T m)`. -/
def etaleFamilyGodementTruncatedCompactHomologyIso (m n : ℕ) :
    ((etaleFamilyGodementTruncatedCompactSectionsSystem.{u, v, uL} ρ points R L h T hpoints D hF
      hT).obj m).homology n ≅
      haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
      (etaleGSheafCompactCohomology L ρ h R n).obj (T.obj m) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  exactGodementTruncatedCompactHomologyIso.{max u (v + 1) uL} ρ (etaleTopology X) points R (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints D (EtaleSite.pointEquivariance L ρ h) hF hT m n

end Compact

section InverseLimit

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type u} [Group G] (ρ : G →* Aut X)
variable {I : Type (max u (v + 1) uL)}
  (points : I → (etaleTopology X).Point.{max u (v + 1) uL})
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
variable [PreservesFiniteLimits (etaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
  [PreservesFiniteColimits (etaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable {ℓ : ℕ} (T : EtaleDivisibleSystem.{u, v, uL} ρ R ℓ)
variable (hpoints : JointlyFaithful fun i => (points i).sheafFiber
  (A := ModuleCat.{max u (v + 1) uL} R))
variable (D : ℕ)
variable (hF : ∀ (M : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (r : ℕ),
    IsZero ((etaleGSheafCompactCohomology L ρ h R (r + 1)).obj
      ((etaleFamilyGodementFunctor.{u, v, uL} ρ points R).obj M)))
  (hT : ∀ m n : ℕ, D < n →
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    IsZero ((etaleGSheafCompactCohomology L ρ h R n).obj (T.obj m)))
variable {ι : Type u} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H)
  [∀ i, (H i).Normal] [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)]
  [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (hm : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R (H i)).map
      (((etaleFamilyGodementTruncatedCompactSectionsSystem.{u, v, uL} ρ points R L h T hpoints D hF
        hT).projection hm).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), IsUnit (Nat.card (quotientProjection (hH hij)).ker : R))
  [IsFiltered ι]

/-- Harris's `C^•_m` for étale `G`-sheaves and the family `points`: the direct limit
over `i` of the inflated complexes built from the `H i`-invariants of `Γ_{c,X{G}}(G^•_m)`
(rows `q < D + 2`). -/
abbrev etaleFamilyGodementQuotientInvariantsLimit :
    DivisibleSystem (CochainComplex (Rep.{max u (v + 1) uL} R G) ℤ) ℓ :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  exactGodementQuotientInvariantsLimit.{max u (v + 1) uL, _, _, u} ρ
    (etaleTopology X) points R (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints D
    (EtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk

/-- Harris's comparison (2.6) `C^•_m ⟶ Γ_{c,X{G}}(G^•_m)` for étale `G`-sheaves and
the family `points`. -/
abbrev etaleFamilyGodementQuotientInvariantsLimitToRepExtend :
    etaleFamilyGodementQuotientInvariantsLimit.{u, v, uL} ρ points R L h T hpoints D hF hT H hH hK
        hk ⟶
      (etaleFamilyGodementTruncatedCompactSectionsSystem.{u, v, uL} ρ points R L h T hpoints D hF
        hT).toRepComplexes.extendSystem :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  exactGodementQuotientInvariantsLimitToRepExtend.{max u (v + 1) uL, _, _, u} ρ
    (etaleTopology X) points R (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints D
    (EtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk

/-- Harris (2.6) for étale `G`-sheaves and the family `points`: given
`ProPInvariantSubcomplexStatement`, if every `H i` is a normal pro-`p` subgroup, `p` is
invertible in `R` and every `H i` acts trivially on `H^q_c(X{G}, T m)` for every `q`, the
comparison is a quasi-isomorphism at level `m`. -/
theorem quasiIso_etaleFamilyGodementQuotientInvariantsLimitToRepExtend
    (hS : ProPInvariantSubcomplexStatement.{u, max u (v + 1) uL, max u (v + 1) uL}) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R)) (m : ℕ)
    (htriv : ∀ i q (g : H i),
      haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
      (SmoothRep.toRep.obj ((etaleGSheafCompactCohomology L ρ h R q).obj (T.obj m))).ρ g =
        LinearMap.id) :
    QuasiIso ((etaleFamilyGodementQuotientInvariantsLimitToRepExtend.{u, v, uL} ρ points R L h T hpoints
      D hF hT H hH hK hk).tower.app (op m)) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  quasiIso_exactGodementQuotientInvariantsLimitToRepExtend.{max u (v + 1) uL, _, _, u} ρ
    (etaleTopology X) points R (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints D
    (EtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk hS hP hR m htriv

/-- Harris (2.7) for étale `G`-sheaves and the family `points`: under the hypotheses of
`quasiIso_etaleFamilyGodementQuotientInvariantsLimitToRepExtend`, the cohomology of
`C^•_m` is `H^n_c(X{G}, T m)`. -/
def etaleFamilyGodementQuotientInvariantsLimitHomologyIso
    (hS : ProPInvariantSubcomplexStatement.{u, max u (v + 1) uL, max u (v + 1) uL}) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R)) (m : ℕ)
    (htriv : ∀ i q (g : H i),
      haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
      (SmoothRep.toRep.obj ((etaleGSheafCompactCohomology L ρ h R q).obj (T.obj m))).ρ g =
        LinearMap.id) (n : ℕ) :
    ((etaleFamilyGodementQuotientInvariantsLimit.{u, v, uL} ρ points R L h T hpoints D hF hT H hH hK
      hk).obj m).homology n ≅
      haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
      SmoothRep.toRep.obj ((etaleGSheafCompactCohomology L ρ h R n).obj (T.obj m)) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  exactGodementQuotientInvariantsLimitHomologyIso.{max u (v + 1) uL, _, _, u} ρ
    (etaleTopology X) points R (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints D
    (EtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk hS hP hR m htriv n

/-- Harris's `lim_m C^•_m` for étale `G`-sheaves and the family `points`. -/
abbrev etaleFamilyGodementQuotientInvariantsInverseLimit :
    CochainComplex (Rep.{max u (v + 1) uL} R G) ℤ :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  exactGodementQuotientInvariantsInverseLimit.{max u (v + 1) uL, _, _, u} ρ
    (etaleTopology X) points R (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints D
    (EtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk

/-- Harris's Lemma 2.8 for étale `G`-sheaves and the family `points`: given
`ProPInvariantSubcomplexStatement` and `FiniteCohomologyInverseLimitStatement`, if every `H i`
is a normal pro-`p` subgroup, `p` is invertible in `R`, and `H^q_c(X{G}, T m)` is finite with
trivial action of every `H i` for all `m` and `q`, then the degree-`n` cohomology of
`lim_m C^•_m` is the inverse limit over `m` of `H^n_c(X{G}, T m)`. -/
def etaleFamilyGodementQuotientInvariantsInverseLimitHomologyIso
    (hS : ProPInvariantSubcomplexStatement.{u, max u (v + 1) uL, max u (v + 1) uL})
    (hS' : FiniteCohomologyInverseLimitStatement.{max u (v + 1) uL, max u (v + 1) uL} R) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R))
    (htriv : ∀ m i q (g : H i),
      haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
      (SmoothRep.toRep.obj ((etaleGSheafCompactCohomology L ρ h R q).obj (T.obj m))).ρ g =
        LinearMap.id)
    (hfin : ∀ m q,
      haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
      Finite (SmoothRep.toRep.obj ((etaleGSheafCompactCohomology L ρ h R q).obj (T.obj m))))
    (n : ℕ) :
    (etaleFamilyGodementQuotientInvariantsInverseLimit.{u, v, uL} ρ points R L h T hpoints D hF hT H hH
      hK hk).homology n ≅
      haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
      limit (T.tower ⋙ etaleGSheafCompactCohomology L ρ h R n ⋙ SmoothRep.toRep) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  exactGodementQuotientInvariantsInverseLimitHomologyIso.{max u (v + 1) uL, _, _, u} ρ
    (etaleTopology X) points R (etaleGSheafAdjunction.{u, v, uL} ρ R) T hpoints D
    (EtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk hS hS' hP hR htriv hfin n

end InverseLimit

end Langlands.Cohomology.DivisibleSystem.Analytic
