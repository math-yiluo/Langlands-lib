import Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology
import Mathlib.FieldTheory.KrullTopology

/-!
# Galois smoothness of prime-to-`m` CM cohomology

Fix `m ≠ 0` and a level `K₀` at the places dividing `m`. The Library's
`cmPrimeToGaloisCohomologyFunctor` sends a sheaf `M` of `R`-modules on the small étale site of
`Spec F` to the colimit, over the prime-to-`m` levels `K'` with `e⁻¹ (K₀ × K')` sufficiently
small, of `H^d(X̄_{e⁻¹ (K₀ × K')}, M)`, where `X̄_U = X_U ×_{Spec F} Spec F̄` and `M` is pulled
back to `X̄_U`. This module states that the commuting action of `F̄ ≃ₐ[F] F̄` on that colimit is
smooth for the Krull topology: every class is fixed by an open subgroup. Harris (1999,
Proposition 4.10) works with this tower, with the level at the places dividing `m` fixed. The
truth argument uses SGA 4 VII Corollaire 5.8 at each level.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Cohomology.HarrisCMPrimeToGaloisSmooth

open NumberField _root_.Algebra Langlands.AbelianScheme Langlands.Shimura Langlands.Shimura.PEL
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Geometry
open Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
open Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})
  (q : CMRepresentabilityStatement D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D,
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj)
  (criterion : Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{0})
  (R : Type) [CommRing R]

local notation "Galois" => (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
local notation "primeToGaloisCohomologyFunctor" => cmPrimeToGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q

/-- For every `m ≠ 0`, every level `K₀` at the places dividing `m`, every degree `d` and every
sheaf `M` of `R`-modules on the small étale site of `Spec F`, every class in the Library's
colimit, over the prime-to-`m` levels `K'` with `e⁻¹ (K₀ × K')` sufficiently small, of
`H^d(X_{e⁻¹ (K₀ × K')} ×_{Spec F} Spec F̄, M)` is fixed by an open subgroup of `F̄ ≃ₐ[F] F̄`,
with its Krull topology, under the constructed Galois action. Here `e` is the splitting
`cmPrimeToSplit D m hm`. -/
def HarrisCMPrimeToGaloisSmoothStatement : Prop :=
  ∀ (m : ℕ) (hm : m ≠ 0) (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
    (d : ℕ) (M : EtaleDerivedSections.ModuleSheaf (Spec (CommRingCat.of F)) R)
    (x : ((primeToGaloisCohomologyFunctor m hm K₀ existence geometry hRigid criterion R
      d).obj M).V),
    ∃ V : OpenSubgroup Galois, ∀ σ ∈ V,
      SmoothRep.hom (((primeToGaloisCohomologyFunctor m hm K₀ existence geometry hRigid
        criterion R d).obj M).ρ σ) x = x

end Langlands.Cohomology.HarrisCMPrimeToGaloisSmooth
