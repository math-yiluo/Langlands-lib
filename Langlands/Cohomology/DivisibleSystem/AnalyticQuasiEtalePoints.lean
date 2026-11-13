import Langlands.Cohomology.DivisibleSystem.AnalyticQuasiEtaleConstant

/-!
# Harris's divisible systems on the quasi-étale site with an arbitrary family of points

The module `AnalyticQuasiEtale` builds the Godement resolutions of Harris's §2 on the
quasi-étale site of an analytic space `X` from the `L`-valued points of `X`. Its results
assume that the fibre functors at these points are jointly faithful on quasi-étale sheaves.
For nonzero coefficients that assumption fails on most spaces of positive dimension (see the
Markdown file of this module). This module builds the same constructions from an arbitrary
family `points : I → Point` of points of the quasi-étale site, and assumes joint
faithfulness for that family instead. The compactly supported cohomology `H^q_c(X{G}, -)`
is still that of `AnalyticQuasiEtaleCompactCohomology`, defined with the `L`-valued points.

The constructions are Harris's Lemma 2.2, Lemma 2.2 bis, (2.3), (2.6), (2.7) and Lemma 2.8
for an arbitrary `ℓ`-divisible system of quasi-étale `G`-sheaves, and Lemma 2.2,
Lemma 2.2 bis, (2.3) and Lemma 2.8 for the constant system `{R / ℓ ^ m R}`. With the family of
`L`-valued points, the Godement functor is the one of `AnalyticQuasiEtale`
(`quasiEtaleGodementFunctor_eq_family`).
-/

noncomputable section

namespace Langlands.Cohomology.DivisibleSystem.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Godement

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable {I : Type (max u (v + 1) uL)}
  (points : I → (quasiEtaleTopology X).Point.{max u (v + 1) uL})
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- The degree-zero Godement functor on quasi-étale `G`-sheaves built from the family
`points`: the discrete part of the induction to the twisted site of the product of the
skyscraper sheaves at the points of the family. -/
abbrev quasiEtaleFamilyGodementFunctor :
    QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  discreteZeroFunctor.{max u (v + 1) uL} ρ (quasiEtaleTopology X) (compactLiftSystem ρ) points R

/-- The coaugmentation `F ⟶ G⁰(F)` of the Godement functor of the family `points`. -/
abbrev quasiEtaleFamilyGodementCoaugmentation :
    𝟭 _ ⟶ quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  discreteCoaugmentation.{max u (v + 1) uL} ρ (quasiEtaleTopology X) (compactLiftSystem ρ) points R

/-- If the fibre functors of the points of the family are jointly faithful, the
coaugmentation is a monomorphism. -/
theorem mono_quasiEtaleFamilyGodementCoaugmentation
    (hpoints : JointlyFaithful fun i => (points i).sheafFiber
      (A := ModuleCat.{max u (v + 1) uL} R))
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    Mono ((quasiEtaleFamilyGodementCoaugmentation.{u, v, uL} ρ points R).app F) :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  mono_discreteCoaugmentation_of_jointlyFaithful.{max u (v + 1) uL} ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    points R hpoints F

/-- The Godement functor of `AnalyticQuasiEtale` is the Godement functor of the family of
`L`-valued points. -/
theorem quasiEtaleGodementFunctor_eq_family (L : Type uL) [NormedField L] [NormedAlgebra K L]
    (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x) :
    quasiEtaleGodementFunctor L ρ h R =
      quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ (quasiEtaleGodementPoints L h) R :=
  rfl

end Godement

section Resolution

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable {I : Type (max u (v + 1) uL)}
  (points : I → (quasiEtaleTopology X).Point.{max u (v + 1) uL})
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
variable [PreservesFiniteLimits (quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
  [PreservesFiniteColimits (quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
variable {ℓ : ℕ} (T : QuasiEtaleDivisibleSystem.{u, v, uL} ρ R ℓ)
variable (hpoints : JointlyFaithful fun i => (points i).sheafFiber
  (A := ModuleCat.{max u (v + 1) uL} R))

/-- Harris's Lemma 2.2 for quasi-étale `G`-sheaves and the family `points`: the
`ℓ`-divisible system of the Godement resolutions `F^0 ⟶ F^1 ⟶ ⋯` of the levels of `T`. -/
def quasiEtaleFamilyGodementResolutionSystem :
    QuasiEtaleComplexDivisibleSystem.{u, v, uL} ρ R ℓ :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteGodementResolutionSystem.{max u (v + 1) uL} ρ (quasiEtaleTopology X) (compactLiftSystem ρ) points R T
    hpoints

/-- Level `m` of the resolution system is the Godement complex of `T m`. -/
def quasiEtaleFamilyGodementResolutionSystemObjIso (m : ℕ) :
    haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    (quasiEtaleFamilyGodementResolutionSystem.{u, v, uL} ρ points R T hpoints).obj m ≅
      (discreteComplexFunctor.{max u (v + 1) uL} ρ (quasiEtaleTopology X) (compactLiftSystem ρ) points R).obj
        (T.obj m) :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteGodementResolutionSystemObjIso.{max u (v + 1) uL} ρ (quasiEtaleTopology X) (compactLiftSystem ρ) points R
    T hpoints m

/-- Every level of the resolution system is exact in positive degrees. -/
theorem quasiEtaleFamilyGodementResolutionSystem_obj_exactAt (m q : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    ((quasiEtaleFamilyGodementResolutionSystem.{u, v, uL} ρ points R T hpoints).obj m).ExactAt (q + 1) :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteGodementResolutionSystem_obj_exactAt.{max u (v + 1) uL} ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    points R T hpoints m q

variable (D : ℕ)

/-- Harris's Lemma 2.2 bis for quasi-étale `G`-sheaves and the family `points`: the
truncation `G^• = τ_{≤ D+1}(F^•)` of the Godement resolution system. -/
def quasiEtaleFamilyGodementTruncatedResolutionSystem :
    QuasiEtaleComplexDivisibleSystem.{u, v, uL} ρ R ℓ :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteGodementTruncatedResolutionSystem.{max u (v + 1) uL} ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    points R T hpoints D

/-- The inclusion `G^• ⟶ F^•` of the truncation into the Godement resolution system. -/
def quasiEtaleFamilyGodementTruncatedResolutionHom :
    quasiEtaleFamilyGodementTruncatedResolutionSystem.{u, v, uL} ρ points R T hpoints D ⟶
      quasiEtaleFamilyGodementResolutionSystem.{u, v, uL} ρ points R T hpoints :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteGodementTruncatedResolutionHom.{max u (v + 1) uL} ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    points R T hpoints D

/-- At every level, the inclusion of the truncation is a quasi-isomorphism. -/
theorem quasiIso_quasiEtaleFamilyGodementTruncatedResolutionHom (m : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    QuasiIso ((quasiEtaleFamilyGodementTruncatedResolutionHom.{u, v, uL} ρ points R T hpoints D).tower.app
      (op m)) :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  quasiIso_discreteGodementTruncatedResolutionHom.{max u (v + 1) uL} ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    points R T hpoints D m

/-- Every level of the truncation is zero in degrees above `D + 1`. -/
theorem isZero_quasiEtaleFamilyGodementTruncatedResolutionSystem_obj_X (m : ℕ) {q : ℕ}
    (hq : D + 1 < q) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    IsZero (((quasiEtaleFamilyGodementTruncatedResolutionSystem.{u, v, uL} ρ points R T hpoints D).obj
      m).X q) :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  isZero_discreteGodementTruncatedResolutionSystem_obj_X.{max u (v + 1) uL} ρ (quasiEtaleTopology X)
    (compactLiftSystem ρ) points R T hpoints D m hq

/-- The augmentation `T m ⟶ G^•_m`. -/
def quasiEtaleFamilyGodementTruncatedAugmentation (m : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    (CochainComplex.single₀ _).obj (T.obj m) ⟶
      (quasiEtaleFamilyGodementTruncatedResolutionSystem.{u, v, uL} ρ points R T hpoints D).obj m :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteGodementTruncatedAugmentation.{max u (v + 1) uL} ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    points R T hpoints D m

/-- Each level of the truncation is a finite-length resolution of the level of `T`. -/
theorem quasiIso_quasiEtaleFamilyGodementTruncatedAugmentation (m : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    QuasiIso (quasiEtaleFamilyGodementTruncatedAugmentation.{u, v, uL} ρ points R T hpoints D m) :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  quasiIso_discreteGodementTruncatedAugmentation.{max u (v + 1) uL} ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    points R T hpoints D m

end Resolution

section Compact

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable {I : Type (max u (v + 1) uL)}
  (points : I → (quasiEtaleTopology X).Point.{max u (v + 1) uL})
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
variable [PreservesFiniteLimits (quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
  [PreservesFiniteColimits (quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable {ℓ : ℕ} (T : QuasiEtaleDivisibleSystem.{u, v, uL} ρ R ℓ)
variable (hpoints : JointlyFaithful fun i => (points i).sheafFiber
  (A := ModuleCat.{max u (v + 1) uL} R))
variable (D : ℕ)
variable (hF : ∀ (M : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (r : ℕ),
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R (r + 1)).obj
      ((quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R).obj M)))
  (hT : ∀ m n : ℕ, D < n →
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R n).obj (T.obj m)))

include hF hT in
/-- Every term of every level of the truncation is acyclic for `Γ_{c,X{G}}`. -/
theorem isZero_quasiEtaleGSheafCompactCohomology_familyTruncatedResolutionSystem_obj_X
    (m i r : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R (r + 1)).obj
      (((quasiEtaleFamilyGodementTruncatedResolutionSystem.{u, v, uL} ρ points R T hpoints D).obj m).X i)) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  isZero_discreteCompactDerived_truncatedResolutionSystem_obj_X.{max u (v + 1) uL} ρ (quasiEtaleTopology X)
    (compactLiftSystem ρ) points R T hpoints D (QuasiEtaleSite.pointEquivariance L ρ h) hF hT m
    i r

/-- Harris's `ℓ`-divisible system of finite-length complexes `Γ_{c,X{G}}(G^•_m)` of smooth
representations of `G`, for the Godement resolutions of the family `points`. -/
def quasiEtaleFamilyGodementTruncatedCompactSectionsSystem :
    DivisibleSystem
      (CochainComplex (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) ℕ) ℓ :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  discreteGodementTruncatedCompactSectionsSystem.{max u (v + 1) uL} ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    points R T hpoints D (QuasiEtaleSite.pointEquivariance L ρ h) hF hT

/-- Level `m` of the section system is the complex of compactly supported sections of
`G^•_m`. -/
theorem quasiEtaleFamilyGodementTruncatedCompactSectionsSystem_obj (m : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    (quasiEtaleFamilyGodementTruncatedCompactSectionsSystem.{u, v, uL} ρ points R L h T hpoints D hF
      hT).obj m =
      ((quasiEtaleGSheafCompactSections L ρ h R).mapHomologicalComplex _).obj
        ((quasiEtaleFamilyGodementTruncatedResolutionSystem.{u, v, uL} ρ points R T hpoints D).obj m) :=
  rfl

/-- Harris (2.3) for quasi-étale `G`-sheaves and the family `points`: the cohomology of level
`m` of the compact section complexes is `H^n_c(X{G}, T m)`. -/
def quasiEtaleFamilyGodementTruncatedCompactHomologyIso (m n : ℕ) :
    ((quasiEtaleFamilyGodementTruncatedCompactSectionsSystem.{u, v, uL} ρ points R L h T hpoints D hF
      hT).obj m).homology n ≅
      haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
      (quasiEtaleGSheafCompactCohomology L ρ h R n).obj (T.obj m) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  discreteGodementTruncatedCompactHomologyIso.{max u (v + 1) uL} ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    points R T hpoints D (QuasiEtaleSite.pointEquivariance L ρ h) hF hT m n

end Compact

section InverseLimit

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type u} [Group G] (ρ : G →* Aut X)
variable {I : Type (max u (v + 1) uL)}
  (points : I → (quasiEtaleTopology X).Point.{max u (v + 1) uL})
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
variable [PreservesFiniteLimits (quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
  [PreservesFiniteColimits (quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable {ℓ : ℕ} (T : QuasiEtaleDivisibleSystem.{u, v, uL} ρ R ℓ)
variable (hpoints : JointlyFaithful fun i => (points i).sheafFiber
  (A := ModuleCat.{max u (v + 1) uL} R))
variable (D : ℕ)
variable (hF : ∀ (M : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (r : ℕ),
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R (r + 1)).obj
      ((quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R).obj M)))
  (hT : ∀ m n : ℕ, D < n →
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R n).obj (T.obj m)))
variable {ι : Type u} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H)
  [∀ i, (H i).Normal] [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)]
  [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (hm : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R (H i)).map
      (((quasiEtaleFamilyGodementTruncatedCompactSectionsSystem.{u, v, uL} ρ points R L h T hpoints D hF
        hT).projection hm).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), IsUnit (Nat.card (quotientProjection (hH hij)).ker : R))
  [IsFiltered ι]

/-- Harris's `C^•_m` for quasi-étale `G`-sheaves and the family `points`: the direct limit
over `i` of the inflated complexes built from the `H i`-invariants of `Γ_{c,X{G}}(G^•_m)`
(rows `q < D + 2`). -/
abbrev quasiEtaleFamilyGodementQuotientInvariantsLimit :
    DivisibleSystem (CochainComplex (Rep.{max u (v + 1) uL} R G) ℤ) ℓ :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  discreteGodementQuotientInvariantsLimit.{max u (v + 1) uL, _, _, u, _} ρ
    (quasiEtaleTopology X) (compactLiftSystem ρ) points R T hpoints D
    (QuasiEtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk

/-- Harris's comparison (2.6) `C^•_m ⟶ Γ_{c,X{G}}(G^•_m)` for quasi-étale `G`-sheaves and
the family `points`. -/
abbrev quasiEtaleFamilyGodementQuotientInvariantsLimitToRepExtend :
    quasiEtaleFamilyGodementQuotientInvariantsLimit.{u, v, uL} ρ points R L h T hpoints D hF hT H hH hK
        hk ⟶
      (quasiEtaleFamilyGodementTruncatedCompactSectionsSystem.{u, v, uL} ρ points R L h T hpoints D hF
        hT).toRepComplexes.extendSystem :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  discreteGodementQuotientInvariantsLimitToRepExtend.{max u (v + 1) uL, _, _, u, _} ρ
    (quasiEtaleTopology X) (compactLiftSystem ρ) points R T hpoints D
    (QuasiEtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk

/-- Harris (2.6) for quasi-étale `G`-sheaves and the family `points`: given
`ProPInvariantSubcomplexStatement`, if every `H i` is a normal pro-`p` subgroup, `p` is
invertible in `R` and every `H i` acts trivially on `H^q_c(X{G}, T m)` for every `q`, the
comparison is a quasi-isomorphism at level `m`. -/
theorem quasiIso_quasiEtaleFamilyGodementQuotientInvariantsLimitToRepExtend
    (hS : ProPInvariantSubcomplexStatement.{u, max u (v + 1) uL, max u (v + 1) uL}) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R)) (m : ℕ)
    (htriv : ∀ i q (g : H i),
      haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
      (SmoothRep.toRep.obj ((quasiEtaleGSheafCompactCohomology L ρ h R q).obj (T.obj m))).ρ g =
        LinearMap.id) :
    QuasiIso ((quasiEtaleFamilyGodementQuotientInvariantsLimitToRepExtend.{u, v, uL} ρ points R L h T hpoints
      D hF hT H hH hK hk).tower.app (op m)) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  quasiIso_discreteGodementQuotientInvariantsLimitToRepExtend.{max u (v + 1) uL, _, _, u, _} ρ
    (quasiEtaleTopology X) (compactLiftSystem ρ) points R T hpoints D
    (QuasiEtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk hS hP hR m htriv

/-- Harris (2.7) for quasi-étale `G`-sheaves and the family `points`: under the hypotheses of
`quasiIso_quasiEtaleFamilyGodementQuotientInvariantsLimitToRepExtend`, the cohomology of
`C^•_m` is `H^n_c(X{G}, T m)`. -/
def quasiEtaleFamilyGodementQuotientInvariantsLimitHomologyIso
    (hS : ProPInvariantSubcomplexStatement.{u, max u (v + 1) uL, max u (v + 1) uL}) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R)) (m : ℕ)
    (htriv : ∀ i q (g : H i),
      haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
      (SmoothRep.toRep.obj ((quasiEtaleGSheafCompactCohomology L ρ h R q).obj (T.obj m))).ρ g =
        LinearMap.id) (n : ℕ) :
    ((quasiEtaleFamilyGodementQuotientInvariantsLimit.{u, v, uL} ρ points R L h T hpoints D hF hT H hH hK
      hk).obj m).homology n ≅
      haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
      SmoothRep.toRep.obj ((quasiEtaleGSheafCompactCohomology L ρ h R n).obj (T.obj m)) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  discreteGodementQuotientInvariantsLimitHomologyIso.{max u (v + 1) uL, _, _, u, _} ρ
    (quasiEtaleTopology X) (compactLiftSystem ρ) points R T hpoints D
    (QuasiEtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk hS hP hR m htriv n

/-- Harris's `lim_m C^•_m` for quasi-étale `G`-sheaves and the family `points`. -/
abbrev quasiEtaleFamilyGodementQuotientInvariantsInverseLimit :
    CochainComplex (Rep.{max u (v + 1) uL} R G) ℤ :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  discreteGodementQuotientInvariantsInverseLimit.{max u (v + 1) uL, _, _, u, _} ρ
    (quasiEtaleTopology X) (compactLiftSystem ρ) points R T hpoints D
    (QuasiEtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk

/-- Harris's Lemma 2.8 for quasi-étale `G`-sheaves and the family `points`: given
`ProPInvariantSubcomplexStatement` and `FiniteCohomologyInverseLimitStatement`, if every `H i`
is a normal pro-`p` subgroup, `p` is invertible in `R`, and `H^q_c(X{G}, T m)` is finite with
trivial action of every `H i` for all `m` and `q`, then the degree-`n` cohomology of
`lim_m C^•_m` is the inverse limit over `m` of `H^n_c(X{G}, T m)`. -/
def quasiEtaleFamilyGodementQuotientInvariantsInverseLimitHomologyIso
    (hS : ProPInvariantSubcomplexStatement.{u, max u (v + 1) uL, max u (v + 1) uL})
    (hS' : FiniteCohomologyInverseLimitStatement.{max u (v + 1) uL, max u (v + 1) uL} R) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R))
    (htriv : ∀ m i q (g : H i),
      haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
      (SmoothRep.toRep.obj ((quasiEtaleGSheafCompactCohomology L ρ h R q).obj (T.obj m))).ρ g =
        LinearMap.id)
    (hfin : ∀ m q,
      haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
      Finite (SmoothRep.toRep.obj ((quasiEtaleGSheafCompactCohomology L ρ h R q).obj (T.obj m))))
    (n : ℕ) :
    (quasiEtaleFamilyGodementQuotientInvariantsInverseLimit.{u, v, uL} ρ points R L h T hpoints D hF hT H hH
      hK hk).homology n ≅
      haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
      limit (T.tower ⋙ quasiEtaleGSheafCompactCohomology L ρ h R n ⋙ SmoothRep.toRep) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  discreteGodementQuotientInvariantsInverseLimitHomologyIso.{max u (v + 1) uL, _, _, u, _} ρ
    (quasiEtaleTopology X) (compactLiftSystem ρ) points R T hpoints D
    (QuasiEtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk hS hS' hP hR htriv hfin n

end InverseLimit

section ConstantResolution

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable {I : Type (max u (v + 1) uL)}
  (points : I → (quasiEtaleTopology X).Point.{max u (v + 1) uL})
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
variable [PreservesFiniteLimits (quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
  [PreservesFiniteColimits (quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
variable (hpoints : JointlyFaithful fun i => (points i).sheafFiber
  (A := ModuleCat.{max u (v + 1) uL} R))

/-- Harris's Lemma 2.2 for the constant sheaves and the family `points`: the `ℓ`-divisible
system of the Godement resolutions of the constant quasi-étale `G`-sheaves `R / ℓ ^ m R`. -/
abbrev quasiEtaleConstantFamilyGodementResolutionSystem :
    QuasiEtaleComplexDivisibleSystem.{u, v, uL} ρ R ℓ :=
  quasiEtaleFamilyGodementResolutionSystem.{u, v, uL} ρ points R (quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ)
    hpoints

variable (D : ℕ)

/-- Harris's Lemma 2.2 bis for the constant sheaves and the family `points`: the truncation
`τ_{≤ D+1}` of the Godement resolution system of the constant system. -/
abbrev quasiEtaleConstantFamilyGodementTruncatedResolutionSystem :
    QuasiEtaleComplexDivisibleSystem.{u, v, uL} ρ R ℓ :=
  quasiEtaleFamilyGodementTruncatedResolutionSystem.{u, v, uL} ρ points R
    (quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D

/-- The augmentation `R / ℓ ^ m R ⟶ G^•_m` of level `m` of the truncated resolution system
of the constant system. -/
def quasiEtaleConstantFamilyGodementTruncatedAugmentation (m : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    (CochainComplex.single₀ _).obj
        ((quasiEtaleConstantSheaf.{u, v, uL} ρ R).obj
          (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))) ⟶
      (quasiEtaleConstantFamilyGodementTruncatedResolutionSystem.{u, v, uL} ρ points R hℓ hpoints D).obj m :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  (CochainComplex.single₀ _).map (quasiEtaleConstantSystemObjIso.{u, v, uL} ρ R hℓ m).inv ≫
    quasiEtaleFamilyGodementTruncatedAugmentation.{u, v, uL} ρ points R
      (quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D m

/-- Level `m` of the truncated resolution system is a finite-length resolution of the
constant quasi-étale `G`-sheaf `R / ℓ ^ m R`. -/
theorem quasiIso_quasiEtaleConstantFamilyGodementTruncatedAugmentation (m : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    QuasiIso (quasiEtaleConstantFamilyGodementTruncatedAugmentation.{u, v, uL} ρ points R hℓ hpoints D m) := by
  have := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  have := quasiIso_quasiEtaleFamilyGodementTruncatedAugmentation ρ points R
    (quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D m
  exact quasiIso_comp _ _

end ConstantResolution

section ConstantCompact

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable {I : Type (max u (v + 1) uL)}
  (points : I → (quasiEtaleTopology X).Point.{max u (v + 1) uL})
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
variable [PreservesFiniteLimits (quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
  [PreservesFiniteColimits (quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable (hpoints : JointlyFaithful fun i => (points i).sheafFiber
  (A := ModuleCat.{max u (v + 1) uL} R))
variable (D : ℕ)
variable (hF : ∀ (M : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (r : ℕ),
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R (r + 1)).obj
      ((quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R).obj M)))
  (hC : ∀ m n : ℕ, D < n →
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R n).obj
      ((quasiEtaleConstantSheaf.{u, v, uL} ρ R).obj
        (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})))))

/-- Harris's `ℓ`-divisible system of finite-length complexes `Γ_{c,X{G}}(G^•_m)` of smooth
representations of `G`, for the constant sheaves `R / ℓ ^ m R` and the family `points`. -/
abbrev quasiEtaleConstantFamilyCompactSectionsSystem :
    DivisibleSystem
      (CochainComplex (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) ℕ) ℓ :=
  quasiEtaleFamilyGodementTruncatedCompactSectionsSystem.{u, v, uL} ρ points R L h
    (quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D hF
    (isZero_quasiEtaleGSheafCompactCohomology_constantSystem_obj ρ R hℓ L h D hC)

/-- Harris (2.3) for the constant sheaves and the family `points`: the cohomology of level
`m` of the compact section complexes is `H^n_c(X{G}, R / ℓ ^ m R)`. -/
def quasiEtaleConstantFamilyCompactHomologyIso (m n : ℕ) :
    ((quasiEtaleConstantFamilyCompactSectionsSystem.{u, v, uL} ρ points R hℓ L h hpoints D hF hC).obj
      m).homology n ≅
      (quasiEtaleGSheafCompactCohomology L ρ h R n).obj
        ((quasiEtaleConstantSheaf.{u, v, uL} ρ R).obj
          (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))) :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  quasiEtaleFamilyGodementTruncatedCompactHomologyIso.{u, v, uL} ρ points R L h
      (quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D hF
      (isZero_quasiEtaleGSheafCompactCohomology_constantSystem_obj ρ R hℓ L h D hC) m n ≪≫
    (quasiEtaleGSheafCompactCohomology L ρ h R n).mapIso
      (quasiEtaleConstantSystemObjIso.{u, v, uL} ρ R hℓ m)

end ConstantCompact

section ConstantInverseLimit

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type u} [Group G] (ρ : G →* Aut X)
variable {I : Type (max u (v + 1) uL)}
  (points : I → (quasiEtaleTopology X).Point.{max u (v + 1) uL})
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
variable [PreservesFiniteLimits (quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
  [PreservesFiniteColimits (quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable (hpoints : JointlyFaithful fun i => (points i).sheafFiber
  (A := ModuleCat.{max u (v + 1) uL} R))
variable (D : ℕ)
variable (hF : ∀ (M : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (r : ℕ),
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R (r + 1)).obj
      ((quasiEtaleFamilyGodementFunctor.{u, v, uL} ρ points R).obj M)))
  (hC : ∀ m n : ℕ, D < n →
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R n).obj
      ((quasiEtaleConstantSheaf.{u, v, uL} ρ R).obj
        (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})))))
variable {ι : Type u} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H)
  [∀ i, (H i).Normal] [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)]
  [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (hm : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R (H i)).map
      (((quasiEtaleConstantFamilyCompactSectionsSystem.{u, v, uL} ρ points R hℓ L h hpoints D hF
        hC).projection hm).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), IsUnit (Nat.card (quotientProjection (hH hij)).ker : R))
  [IsFiltered ι]

/-- Harris's `lim_m C^•_m` for the constant sheaves `R / ℓ ^ m R` and the family `points`. -/
abbrev quasiEtaleConstantFamilyQuotientInvariantsInverseLimit :
    CochainComplex (Rep.{max u (v + 1) uL} R G) ℤ :=
  quasiEtaleFamilyGodementQuotientInvariantsInverseLimit.{u, v, uL} ρ points R L h
    (quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D hF
    (isZero_quasiEtaleGSheafCompactCohomology_constantSystem_obj ρ R hℓ L h D hC) H hH hK hk

set_option synthInstance.maxHeartbeats 60000 in
/-- Harris's Lemma 2.8 for the constant sheaves and the family `points`: under the hypotheses
of `quasiEtaleFamilyGodementQuotientInvariantsInverseLimitHomologyIso`, the degree-`n`
cohomology of `lim_m C^•_m` is the inverse limit over `m` of `H^n_c(X{G}, R / ℓ ^ m R)`
(level `m` of the constant system). -/
def quasiEtaleConstantFamilyQuotientInvariantsInverseLimitHomologyIso
    (hS : ProPInvariantSubcomplexStatement.{u, max u (v + 1) uL, max u (v + 1) uL})
    (hS' : FiniteCohomologyInverseLimitStatement.{max u (v + 1) uL, max u (v + 1) uL} R) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R))
    (htriv : ∀ m i q (g : H i),
      haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
      (SmoothRep.toRep.obj ((quasiEtaleGSheafCompactCohomology L ρ h R q).obj
        ((quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ).obj m))).ρ g = LinearMap.id)
    (hfin : ∀ m q,
      haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
      Finite (SmoothRep.toRep.obj ((quasiEtaleGSheafCompactCohomology L ρ h R q).obj
        ((quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ).obj m))))
    (n : ℕ) :
    (quasiEtaleConstantFamilyQuotientInvariantsInverseLimit.{u, v, uL} ρ points R hℓ L h hpoints D hF hC H
      hH hK hk).homology n ≅
      haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
      limit ((quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ).tower ⋙
        quasiEtaleGSheafCompactCohomology L ρ h R n ⋙ SmoothRep.toRep) :=
  quasiEtaleFamilyGodementQuotientInvariantsInverseLimitHomologyIso.{u, v, uL} ρ points R L h
    (quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D hF
    (isZero_quasiEtaleGSheafCompactCohomology_constantSystem_obj ρ R hℓ L h D hC) H hH hK hk hS
    hS' hP hR htriv hfin n

end ConstantInverseLimit

end Langlands.Cohomology.DivisibleSystem.Analytic
