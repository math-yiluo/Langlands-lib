import Langlands.Geometry.Analytic.CompactProbeQuasiEtalePoints
import Langlands.Sheaf.Equivariant.AnalyticCompactProbeQuasiEtale
import Langlands.Sheaf.Equivariant.TwistedDiscreteGodementExactness
import Langlands.Cohomology.DivisibleSystem.TwistedTruncation
import Langlands.Sheaf.Godement.ExactnessStatement

/-! # Discrete Godement cochains and coefficient systems for the compact-probe site -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.DivisibleSystem.Analytic

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v uL z w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : LocalizedCategory.{u, v, v} (K := K)}

section GeometricPoints

variable (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [IsAlgClosed L] [NormedAlgebra K L]

/-- The actual field-valued points, reindexed in the universe of the Godement coefficients. -/
abbrev compactProbeGodementGeometricPoints
    (x : ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X)) :
    (compactProbeQuasiEtaleTopology X).Point.{max u (v + 1) uL} :=
  QuasiEtaleSite.compactProbeGeometricPoint L x.down

end GeometricPoints

section Modules

variable {G : Type z} [Group G] [TopologicalSpace G] (ρ : G →* Aut X)
  (R : Type w) [CommRing R]

/-- Module-valued discrete sheaves for the compact-probe topology. -/
abbrev CompactProbeModuleGSheaf :=
  CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{w} R)

end Modules

variable {G : Type z} [Group G] [TopologicalSpace G] (ρ : G →* Aut X)
  (R : Type w) [CommRing R]
  [refinements : (compactLiftSystem ρ).HasFiniteEquivariantRefinements
    (twistedTopology ρ (compactProbeQuasiEtaleTopology X))]

local notation "J" => compactProbeQuasiEtaleTopology X
local notation "Lifts" => compactLiftSystem ρ

variable [ordinarySheafify : HasSheafify (compactProbeQuasiEtaleTopology X) (ModuleCat.{w} R)]
  [twistedSheafify : HasSheafify (twistedTopology ρ (compactProbeQuasiEtaleTopology X))
    (ModuleCat.{w} R)]
  [locallySmall : LocallySmall.{w} (QuasiEtaleSite X)]
  [pointwiseRan : ∀ F : (QuasiEtaleSite X)ᵒᵖ ⥤ ModuleCat.{w} R,
    (ι (quasiEtale (K := K)) ρ).op.HasPointwiseRightKanExtension F]
  {I : Type w} (points : I → (compactProbeQuasiEtaleTopology X).Point.{w})

local notation "Sh" => CompactProbeModuleGSheaf ρ R

include refinements pointwiseRan

/-- Degree-zero Godement on compact-probe `G`-sheaves, formed from actual site points. -/
abbrev compactProbeGodementFunctor (points : I → (compactProbeQuasiEtaleTopology X).Point.{w}) :
    Sh ⥤ Sh := by
  exact discreteZeroFunctor ρ J Lifts points R

/-- The natural map from a sheaf to its degree-zero Godement term. -/
abbrev compactProbeGodementCoaugmentation :
    𝟭 Sh ⟶ compactProbeGodementFunctor ρ R points :=
  discreteCoaugmentation ρ J Lifts points R

include ordinarySheafify twistedSheafify locallySmall in
/-- The degree-zero functor is exact on the actual compact-probe `G`-sheaf category. -/
theorem compactProbeGodementFunctor_preservesHomology :
    (compactProbeGodementFunctor ρ R points).PreservesHomology :=
  discreteZeroFunctor_preservesHomology ρ J Lifts points R

include twistedSheafify

/-- Godement cochains of compact-probe `G`-sheaves, formed by iterating cokernels. -/
def compactProbeGodementComplex (points : I → (compactProbeQuasiEtaleTopology X).Point.{w}) :
    Sh ⥤ CochainComplex Sh ℕ :=
  discreteComplexFunctor ρ J Lifts points R

/-- The augmentation as a natural map of complexes. -/
def compactProbeGodementAugmentation :
    CochainComplex.single₀ Sh ⟶ compactProbeGodementComplex ρ R points :=
  CokernelComplex.augmentationNat (compactProbeGodementFunctor ρ R points)
    (compactProbeGodementCoaugmentation ρ R points)

variable (hpoints : JointlyFaithful fun i =>
  (points i).sheafFiber (A := ModuleCat.{w} R))

omit ordinarySheafify twistedSheafify locallySmall in
include hpoints in
/-- Jointly faithful site fibers make the compact-probe coaugmentation monic. -/
theorem mono_compactProbeGodementCoaugmentation (F : Sh) :
    Mono ((compactProbeGodementCoaugmentation ρ R points).app F) :=
  mono_discreteCoaugmentation_of_jointlyFaithful ρ J Lifts points R hpoints F

variable {ℓ : ℕ} (S : DivisibleSystem (CompactProbeModuleGSheaf ρ R) ℓ)

include ordinarySheafify locallySmall

/-- The coefficient inverse system of compact-probe Godement resolutions. -/
def compactProbeGodementResolutionSystem : DivisibleSystem (CochainComplex Sh ℕ) ℓ :=
  discreteGodementResolutionSystem ρ J Lifts points R S hpoints

/-- The actual Godement complex at a given coefficient level. -/
def compactProbeGodementResolutionSystemObjIso (m : ℕ) :
    (compactProbeGodementResolutionSystem ρ R points hpoints S).obj m ≅
      (compactProbeGodementComplex ρ R points).obj (S.obj m) :=
  discreteGodementResolutionSystemObjIso ρ J Lifts points R S hpoints m

/-- The bounded truncation of the coefficient system in degree `D + 1`. -/
def compactProbeGodementTruncatedResolutionSystem (D : ℕ) :
    DivisibleSystem (CochainComplex Sh ℕ) ℓ :=
  discreteGodementTruncatedResolutionSystem ρ J Lifts points R S hpoints D

/-- The augmented truncation uses the original sheaf at this coefficient level. -/
def compactProbeGodementTruncatedAugmentation (D m : ℕ) :
    (CochainComplex.single₀ Sh).obj (S.obj m) ⟶
      (compactProbeGodementTruncatedResolutionSystem ρ R points hpoints S D).obj m :=
  discreteGodementTruncatedAugmentation ρ J Lifts points R S hpoints D m

/-- Each bounded augmented coefficient complex resolves the original sheaf. -/
theorem quasiIso_compactProbeGodementTruncatedAugmentation (D m : ℕ) :
    QuasiIso (compactProbeGodementTruncatedAugmentation ρ R points hpoints S D m) :=
  quasiIso_discreteGodementTruncatedAugmentation ρ J Lifts points R S hpoints D m

end Langlands.Cohomology.DivisibleSystem.Analytic
