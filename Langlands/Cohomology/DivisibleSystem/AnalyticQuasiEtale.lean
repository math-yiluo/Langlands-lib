import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCompactCohomology
import Langlands.Cohomology.DivisibleSystem.TwistedInverseLimit

/-!
# Harris's divisible systems on the quasi-étale site of an analytic space

Let `G` act on an analytic space `X`. This module specializes Harris's constructions of §2
(Lemma 2.2, Lemma 2.2 bis, (2.3), (2.6), (2.7) and Lemma 2.8), published for an arbitrary
twisted site in the `DivisibleSystem` series, to Berkovich's quasi-étale `G`-sheaves on `X`,
with the `L`-valued points of `X` as points of the quasi-étale site and the compactly
supported cohomology `H^q_c(X{G}, -)` of `AnalyticQuasiEtaleCompactCohomology`.

It proves that module presheaves on the quasi-étale site have pointwise right Kan extensions
to the twisted site, so the Godement functor is defined. Sheafification and enough injectives
come from `AnalyticQuasiEtaleCompactCohomology`. The remaining inputs stay hypotheses, as in
the twisted-site modules: exactness of the Godement functor, joint faithfulness of the fibre
functors at the `L`-valued points, finite equivariant refinements, the point axioms, the
acyclicity of Godement sheaves and the bound `D` on cohomological dimension.
-/

noncomputable section

namespace Langlands.Cohomology.DivisibleSystem.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Induction

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- If `G` is small at the universe `max u (v + 1) uL`, every module presheaf on the
quasi-étale site has a pointwise right Kan extension along the inclusion into the twisted
quasi-étale site: the indexing categories are essentially small. -/
theorem quasiEtale_hasPointwiseRightKanExtension [Small.{max u (v + 1) uL} G]
    (F : (QuasiEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R) :
    (ι (quasiEtale (K := K)) ρ).op.HasPointwiseRightKanExtension F := fun Y =>
  haveI := quasiEtaleSite_essentiallySmall_points.{u, v, uL} X
  haveI := twistedQuasiEtale_locallySmall_points.{u, v, uL} X ρ
  haveI := hasLimitsOfShape_of_essentiallySmall.{max u (v + 1) uL}
    (StructuredArrow Y (ι (quasiEtale (K := K)) ρ).op) (ModuleCat.{max u (v + 1) uL} R)
  inferInstance

end Induction

section Godement

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- The `L`-valued points of `X` as points of the quasi-étale site, indexed in the universe
of the coefficients. -/
abbrev quasiEtaleGodementPoints :
    ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X) →
      (quasiEtaleTopology X).Point.{max u (v + 1) uL} :=
  fun x => quasiEtalePoints L h x.down

/-- Joint faithfulness of the fibre functors of the `L`-valued points passes to the
reindexed family. -/
theorem jointlyFaithful_quasiEtaleGodementPoints
    (hpoints : JointlyFaithful fun x : (localizedFieldPointFunctor L).obj X =>
      (quasiEtalePoints L h x).sheafFiber (A := ModuleCat.{max u (v + 1) uL} R)) :
    JointlyFaithful fun x => (quasiEtaleGodementPoints L h x).sheafFiber
      (A := ModuleCat.{max u (v + 1) uL} R) :=
  ⟨fun hfg => hpoints.map_injective fun x => hfg ⟨x⟩⟩

/-- The degree-zero Godement functor on quasi-étale `G`-sheaves: the discrete part of the
induction to the twisted site of the product of the skyscraper sheaves at the `L`-valued
points. -/
abbrev quasiEtaleGodementFunctor :
    QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  discreteZeroFunctor ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    (quasiEtaleGodementPoints L h) R

/-- The coaugmentation `F ⟶ G⁰(F)` of the quasi-étale Godement functor. -/
abbrev quasiEtaleGodementCoaugmentation : 𝟭 _ ⟶ quasiEtaleGodementFunctor L ρ h R :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  discreteCoaugmentation ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    (quasiEtaleGodementPoints L h) R

/-- If the fibre functors of the `L`-valued points are jointly faithful, the coaugmentation
is a monomorphism. -/
theorem mono_quasiEtaleGodementCoaugmentation
    (hpoints : JointlyFaithful fun x : (localizedFieldPointFunctor L).obj X =>
      (quasiEtalePoints L h x).sheafFiber (A := ModuleCat.{max u (v + 1) uL} R))
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    Mono ((quasiEtaleGodementCoaugmentation L ρ h R).app F) :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  mono_discreteCoaugmentation_of_jointlyFaithful ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    (quasiEtaleGodementPoints L h) R (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) F

end Godement

section Resolution

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- Harris's `ℓ`-divisible systems (Harris 1999, (2.1)) of quasi-étale `G`-sheaves of
`R`-modules. The abelian structure uses the sheafification proved in
`AnalyticQuasiEtaleCompactCohomology`. -/
abbrev QuasiEtaleDivisibleSystem (ℓ : ℕ) : Type _ :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  DivisibleSystem (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) ℓ

/-- `ℓ`-divisible systems of complexes of quasi-étale `G`-sheaves of `R`-modules. -/
abbrev QuasiEtaleComplexDivisibleSystem (ℓ : ℕ) : Type _ :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  DivisibleSystem (CochainComplex (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) ℕ) ℓ

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable [PreservesFiniteLimits (quasiEtaleGodementFunctor L ρ h R)]
  [PreservesFiniteColimits (quasiEtaleGodementFunctor L ρ h R)]
variable {ℓ : ℕ} (T : QuasiEtaleDivisibleSystem.{u, v, uL} ρ R ℓ)
variable (hpoints : JointlyFaithful fun x : (localizedFieldPointFunctor L).obj X =>
  (quasiEtalePoints L h x).sheafFiber (A := ModuleCat.{max u (v + 1) uL} R))

/-- Harris's Lemma 2.2 for quasi-étale `G`-sheaves: the `ℓ`-divisible system of the
Godement resolutions `F^0 ⟶ F^1 ⟶ ⋯` of the levels of `T`, built from the `L`-valued
points of `X`. -/
def quasiEtaleGodementResolutionSystem : QuasiEtaleComplexDivisibleSystem.{u, v, uL} ρ R ℓ :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteGodementResolutionSystem ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    (quasiEtaleGodementPoints L h) R T (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints)

/-- Level `m` of the resolution system is the Godement complex of `T m`. -/
def quasiEtaleGodementResolutionSystemObjIso (m : ℕ) :
    haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    (quasiEtaleGodementResolutionSystem ρ R L h T hpoints).obj m ≅
      (discreteComplexFunctor ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
        (quasiEtaleGodementPoints L h) R).obj (T.obj m) :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteGodementResolutionSystemObjIso ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    (quasiEtaleGodementPoints L h) R T (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) m

/-- Every level of the resolution system is exact in positive degrees. -/
theorem quasiEtaleGodementResolutionSystem_obj_exactAt (m q : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    ((quasiEtaleGodementResolutionSystem ρ R L h T hpoints).obj m).ExactAt (q + 1) :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteGodementResolutionSystem_obj_exactAt ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    (quasiEtaleGodementPoints L h) R T (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) m q

variable (D : ℕ)

/-- Harris's Lemma 2.2 bis for quasi-étale `G`-sheaves: the truncation
`G^• = τ_{≤ D+1}(F^•)` of the Godement resolution system. -/
def quasiEtaleGodementTruncatedResolutionSystem :
    QuasiEtaleComplexDivisibleSystem.{u, v, uL} ρ R ℓ :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteGodementTruncatedResolutionSystem ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    (quasiEtaleGodementPoints L h) R T (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) D

/-- The inclusion `G^• ⟶ F^•` of the truncation into the Godement resolution system. -/
def quasiEtaleGodementTruncatedResolutionHom :
    quasiEtaleGodementTruncatedResolutionSystem ρ R L h T hpoints D ⟶
      quasiEtaleGodementResolutionSystem ρ R L h T hpoints :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteGodementTruncatedResolutionHom ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    (quasiEtaleGodementPoints L h) R T (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) D

/-- At every level, the inclusion of the truncation is a quasi-isomorphism. -/
theorem quasiIso_quasiEtaleGodementTruncatedResolutionHom (m : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    QuasiIso ((quasiEtaleGodementTruncatedResolutionHom ρ R L h T hpoints D).tower.app (op m)) :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  quasiIso_discreteGodementTruncatedResolutionHom ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    (quasiEtaleGodementPoints L h) R T (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) D m

/-- Every level of the truncation is zero in degrees above `D + 1`. -/
theorem isZero_quasiEtaleGodementTruncatedResolutionSystem_obj_X (m : ℕ) {q : ℕ}
    (hq : D + 1 < q) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    IsZero (((quasiEtaleGodementTruncatedResolutionSystem ρ R L h T hpoints D).obj m).X q) :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  isZero_discreteGodementTruncatedResolutionSystem_obj_X ρ
    (quasiEtaleTopology X) (compactLiftSystem ρ) (quasiEtaleGodementPoints L h) R T
    (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) D m hq

/-- The augmentation `T m ⟶ G^•_m`. -/
def quasiEtaleGodementTruncatedAugmentation (m : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    (CochainComplex.single₀ _).obj (T.obj m) ⟶
      (quasiEtaleGodementTruncatedResolutionSystem ρ R L h T hpoints D).obj m :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteGodementTruncatedAugmentation ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    (quasiEtaleGodementPoints L h) R T (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) D m

/-- Each level of the truncation is a finite-length resolution of the level of `T`. -/
theorem quasiIso_quasiEtaleGodementTruncatedAugmentation (m : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    QuasiIso (quasiEtaleGodementTruncatedAugmentation ρ R L h T hpoints D m) :=
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  quasiIso_discreteGodementTruncatedAugmentation ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    (quasiEtaleGodementPoints L h) R T (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) D m

end Resolution

section Compact

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable [PreservesFiniteLimits (quasiEtaleGodementFunctor L ρ h R)]
  [PreservesFiniteColimits (quasiEtaleGodementFunctor L ρ h R)]
variable {ℓ : ℕ} (T : QuasiEtaleDivisibleSystem.{u, v, uL} ρ R ℓ)
variable (hpoints : JointlyFaithful fun x : (localizedFieldPointFunctor L).obj X =>
  (quasiEtalePoints L h x).sheafFiber (A := ModuleCat.{max u (v + 1) uL} R))
variable (D : ℕ)
variable (hF : ∀ (M : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (r : ℕ),
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R (r + 1)).obj
      ((quasiEtaleGodementFunctor L ρ h R).obj M)))
  (hT : ∀ m n : ℕ, D < n →
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R n).obj (T.obj m)))

include hF hT in
/-- Every term of every level of the truncation is acyclic for `Γ_{c,X{G}}`. -/
theorem isZero_quasiEtaleGSheafCompactCohomology_truncatedResolutionSystem_obj_X (m i r : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R (r + 1)).obj
      (((quasiEtaleGodementTruncatedResolutionSystem ρ R L h T hpoints D).obj m).X i)) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  isZero_discreteCompactDerived_truncatedResolutionSystem_obj_X ρ (quasiEtaleTopology X)
    (compactLiftSystem ρ) (quasiEtaleGodementPoints L h) R T
    (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) D
    (QuasiEtaleSite.pointEquivariance L ρ h) hF hT m i r

/-- Harris's `ℓ`-divisible system of finite-length complexes `Γ_{c,X{G}}(G^•_m)` of smooth
representations of `G`, for quasi-étale `G`-sheaves. -/
def quasiEtaleGodementTruncatedCompactSectionsSystem :
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
  discreteGodementTruncatedCompactSectionsSystem ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    (quasiEtaleGodementPoints L h) R T (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) D
    (QuasiEtaleSite.pointEquivariance L ρ h) hF hT

/-- Level `m` of the section system is the complex of compactly supported sections of
`G^•_m`. -/
theorem quasiEtaleGodementTruncatedCompactSectionsSystem_obj (m : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    (quasiEtaleGodementTruncatedCompactSectionsSystem ρ R L h T hpoints D hF hT).obj m =
      ((quasiEtaleGSheafCompactSections L ρ h R).mapHomologicalComplex _).obj
        ((quasiEtaleGodementTruncatedResolutionSystem ρ R L h T hpoints D).obj m) :=
  rfl

/-- Harris (2.3) for quasi-étale `G`-sheaves: the cohomology of level `m` of the compact
section complexes is `H^n_c(X{G}, T m)`. -/
def quasiEtaleGodementTruncatedCompactHomologyIso (m n : ℕ) :
    ((quasiEtaleGodementTruncatedCompactSectionsSystem ρ R L h T hpoints D hF hT).obj
      m).homology n ≅
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
  discreteGodementTruncatedCompactHomologyIso ρ (quasiEtaleTopology X) (compactLiftSystem ρ)
    (quasiEtaleGodementPoints L h) R T (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) D
    (QuasiEtaleSite.pointEquivariance L ρ h) hF hT m n

/-- The cohomology of every level of the compact section complexes vanishes above
degree `D`. -/
theorem isZero_quasiEtaleGodementTruncatedCompactSectionsSystem_homology (m : ℕ) {n : ℕ}
    (hn : D < n) :
    IsZero (((quasiEtaleGodementTruncatedCompactSectionsSystem ρ R L h T hpoints D hF
      hT).obj m).homology n) :=
  (hT m n hn).of_iso (quasiEtaleGodementTruncatedCompactHomologyIso ρ R L h T hpoints D hF hT m n)

end Compact

section InverseLimit

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type u} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable [PreservesFiniteLimits (quasiEtaleGodementFunctor L ρ h R)]
  [PreservesFiniteColimits (quasiEtaleGodementFunctor L ρ h R)]
variable {ℓ : ℕ} (T : QuasiEtaleDivisibleSystem.{u, v, uL} ρ R ℓ)
variable (hpoints : JointlyFaithful fun x : (localizedFieldPointFunctor L).obj X =>
  (quasiEtalePoints L h x).sheafFiber (A := ModuleCat.{max u (v + 1) uL} R))
variable (D : ℕ)
variable (hF : ∀ (M : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (r : ℕ),
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R (r + 1)).obj
      ((quasiEtaleGodementFunctor L ρ h R).obj M)))
  (hT : ∀ m n : ℕ, D < n →
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R n).obj (T.obj m)))
variable {ι : Type u} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H)
  [∀ i, (H i).Normal] [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)]
  [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (hm : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R (H i)).map
      (((quasiEtaleGodementTruncatedCompactSectionsSystem ρ R L h T hpoints D hF hT).projection
        hm).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), IsUnit (Nat.card (quotientProjection (hH hij)).ker : R))
  [IsFiltered ι]

/-- Harris's `C^•_m` for quasi-étale `G`-sheaves: the direct limit over `i` of the inflated
complexes built from the `H i`-invariants of `Γ_{c,X{G}}(G^•_m)` (rows `q < D + 2`). -/
abbrev quasiEtaleGodementQuotientInvariantsLimit :
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
    (quasiEtaleTopology X) (compactLiftSystem ρ) (quasiEtaleGodementPoints L h) R T
    (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) D
    (QuasiEtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk

/-- Harris's comparison (2.6) `C^•_m ⟶ Γ_{c,X{G}}(G^•_m)` for quasi-étale `G`-sheaves. -/
abbrev quasiEtaleGodementQuotientInvariantsLimitToRepExtend :
    quasiEtaleGodementQuotientInvariantsLimit ρ R L h T hpoints D hF hT H hH hK hk ⟶
      (quasiEtaleGodementTruncatedCompactSectionsSystem ρ R L h T hpoints D hF
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
    (quasiEtaleTopology X) (compactLiftSystem ρ) (quasiEtaleGodementPoints L h) R T
    (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) D
    (QuasiEtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk

/-- Harris (2.6) for quasi-étale `G`-sheaves: given `ProPInvariantSubcomplexStatement`, if every
`H i` is a normal pro-`p` subgroup, `p` is invertible in `R` and every `H i` acts trivially on
`H^q_c(X{G}, T m)` for every `q`, the comparison is a quasi-isomorphism at level `m`. -/
theorem quasiIso_quasiEtaleGodementQuotientInvariantsLimitToRepExtend
    (hS : ProPInvariantSubcomplexStatement.{u, max u (v + 1) uL, max u (v + 1) uL}) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R)) (m : ℕ)
    (htriv : ∀ i q (g : H i),
      haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
      (SmoothRep.toRep.obj ((quasiEtaleGSheafCompactCohomology L ρ h R q).obj (T.obj m))).ρ g =
        LinearMap.id) :
    QuasiIso ((quasiEtaleGodementQuotientInvariantsLimitToRepExtend ρ R L h T hpoints D hF hT H hH
      hK hk).tower.app (op m)) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  quasiIso_discreteGodementQuotientInvariantsLimitToRepExtend.{max u (v + 1) uL, _, _, u, _} ρ
    (quasiEtaleTopology X) (compactLiftSystem ρ) (quasiEtaleGodementPoints L h) R T
    (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) D
    (QuasiEtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk hS hP hR m htriv

/-- Harris (2.7) for quasi-étale `G`-sheaves: under the hypotheses of
`quasiIso_quasiEtaleGodementQuotientInvariantsLimitToRepExtend`, the cohomology of `C^•_m` is
`H^n_c(X{G}, T m)`. -/
def quasiEtaleGodementQuotientInvariantsLimitHomologyIso
    (hS : ProPInvariantSubcomplexStatement.{u, max u (v + 1) uL, max u (v + 1) uL}) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R)) (m : ℕ)
    (htriv : ∀ i q (g : H i),
      haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
      (SmoothRep.toRep.obj ((quasiEtaleGSheafCompactCohomology L ρ h R q).obj (T.obj m))).ρ g =
        LinearMap.id) (n : ℕ) :
    ((quasiEtaleGodementQuotientInvariantsLimit ρ R L h T hpoints D hF hT H hH hK hk).obj
      m).homology n ≅
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
    (quasiEtaleTopology X) (compactLiftSystem ρ) (quasiEtaleGodementPoints L h) R T
    (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) D
    (QuasiEtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk hS hP hR m htriv n

/-- Harris's `lim_m C^•_m` for quasi-étale `G`-sheaves. -/
abbrev quasiEtaleGodementQuotientInvariantsInverseLimit :
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
    (quasiEtaleTopology X) (compactLiftSystem ρ) (quasiEtaleGodementPoints L h) R T
    (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) D
    (QuasiEtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk

/-- Harris's Lemma 2.8 for quasi-étale `G`-sheaves: given `ProPInvariantSubcomplexStatement` and
`FiniteCohomologyInverseLimitStatement`, if every `H i` is a normal pro-`p` subgroup, `p` is
invertible in `R`, and `H^q_c(X{G}, T m)` is finite with trivial action of every `H i` for all
`m` and `q`, then the degree-`n` cohomology of `lim_m C^•_m` is the inverse limit over `m` of
`H^n_c(X{G}, T m)`. -/
def quasiEtaleGodementQuotientInvariantsInverseLimitHomologyIso
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
    (quasiEtaleGodementQuotientInvariantsInverseLimit ρ R L h T hpoints D hF hT H hH hK
      hk).homology n ≅
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
    (quasiEtaleTopology X) (compactLiftSystem ρ) (quasiEtaleGodementPoints L h) R T
    (jointlyFaithful_quasiEtaleGodementPoints L h R hpoints) D
    (QuasiEtaleSite.pointEquivariance L ρ h) hF hT H hH hK hk hS hS' hP hR htriv hfin n

end InverseLimit

end Langlands.Cohomology.DivisibleSystem.Analytic
