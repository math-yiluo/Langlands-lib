import Langlands.Representation.Exponents.MaximalLeviBlockProjectionStatement
import Langlands.CategoryTheory.FullSubcategoryAdjunctionEquivalence
import Langlands.CategoryTheory.CategoryDecompositionAdjunction
import Langlands.Representation.CuspidalSupport.RationalInertiaDecompositionStatement
import Langlands.Representation.Aubert.General.RepresentedStandardCuspidality
import Langlands.Representation.Aubert.General.StandardFamilyStructure
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusExtension
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Torus.ExistenceProof

/-! # Reduction of the maximal Levi block projection to two published statements -/

noncomputable section

set_option maxHeartbeats 800000

universe u v

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

open GroupScheme Aubert.General Aubert.General.RationalPointFamily

section LinearEquiv

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X

/-- The categorical inertia relation is exactly the linear-equivalence
encoding used by the maximal Levi block statements. -/
theorem isRationalInertiaRelated_iff_linearEquiv
    (ρ σ : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    IsRationalInertiaRelated G ρ σ ↔
      ∃ ψ : Plancherel.unramifiedCharacters
          (fun χ : rationalCharacters G => (Plancherel.rationalNormCharacters G χ).toMul),
        ∃ T : ρ ≃ₗ[ℂ] σ, ∀ (m : rationalPoints G) (x : ρ),
          (((ψ : rationalPoints G →ₜ* ℂˣ) m : ℂˣ) : ℂ) • T (ρ.representation m x) =
            σ.representation m (T x) := by
  constructor
  · rintro ⟨ψ, ⟨e⟩⟩
    let E := SmoothRep.equivOfIso e.symm
    refine ⟨ψ, E.toLinearEquiv, fun m x => ?_⟩
    have h := LinearMap.congr_fun (E.isIntertwining' m) x
    change E.toLinearEquiv
      ((((ψ : rationalPoints G →ₜ* ℂˣ) m : ℂˣ) : ℂ) • ρ.representation m x) =
        σ.representation m (E.toLinearEquiv x) at h
    simpa only [map_smul] using h
  · rintro ⟨ψ, T, hT⟩
    refine ⟨ψ, ⟨(SmoothRep.mkIso (A := rationalUnramifiedTwist G ψ ρ) (B := σ)
      (Representation.Equiv.mk T (fun m => ?_))).symm⟩⟩
    ext x
    change T ((((ψ : rationalPoints G →ₜ* ℂˣ) m : ℂˣ) : ℂ) • ρ.representation m x) =
      σ.representation m (T x)
    simpa only [map_smul] using hT m x

end LinearEquiv

/-- Conditional application of VI.3.3.1 to represented supercuspidality.
All structural premises of that statement are discharged by published proofs. -/
theorem rationalInertiaBlock_isRightAdjoint_of_representedCuspidal
    (hSplit : RationalCuspidalInertiaDecompositionStatement.{u, max u v})
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (ρ : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)),
      ρ.IsIrreducible →
      (∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
        (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
        (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
        (hmul : IsIso (subgroupMultiplication l r)),
        ¬ IsIso p → Subsingleton ((RepresentedParabolic.jacquetFunctor
          p l r hp hr hl hmul).obj ρ)) →
      (rationalInertiaBlockProperty G ρ).ι.IsRightAdjoint := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ ρ hρ hA
  let : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  obtain ⟨T, i, hi, -⟩ := exists_maximalSplitTorus_extension G
    (TorusExistence.trivialTorusHom G)
    ⟨isSplitTorus_splitTorus PEmpty, TorusExistence.isClosedSubgroup_trivialTorusHom G⟩
  obtain ⟨ν, hν⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter i
  have := hi.isSplitSubtorus.mono
  let hRoots := relativeRootSystem k G hG T i hi
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let hU := isClosed_unipotent_of_isNonarchimedeanLocalField i ν
  have hC := RepresentedParabolic.isCuspidal_of_all_represented_parabolics_of_standardCocharacter
    i ν standardCocharacter hG hi hν hRoots hU ρ hA
  have hD := hSplit k G hG T i hi ν hν standardCocharacter hRoots hU ρ hρ hC
  exact Renard.IsCategoryDecomposition.isRightAdjoint_ι hD true

end Langlands.CuspidalSupport

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme CuspidalSupport

/-- The exact target follows from the two prerequisite statements. This is
a conditional reduction, not a proof of either prerequisite or of the target. -/
theorem maximalLeviBlockProjectionEquivalence_of_decomposition_of_blocks
    (hSplit : RationalCuspidalInertiaDecompositionStatement.{u, max u v})
    (hBlocks : MaximalLeviBlockStatements.{u, v}) :
    MaximalLeviBlockProjectionEquivalenceStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul hproper hmax
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hρ hA hnonself
  dsimp only
  let IsTwist : SmoothRep.{0, u, max u v} ℂ (rationalPoints M) → Prop := fun σ =>
    ∃ ψ : Plancherel.unramifiedCharacters
        (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
      ∃ T : ρ ≃ₗ[ℂ] σ, ∀ (m : rationalPoints M) (x : ρ),
        (((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) • T (ρ.representation m x) =
          σ.representation m (T x)
  let InBlockM : ObjectProperty (SmoothRep.{0, u, max u v} ℂ (rationalPoints M)) :=
    fun X => ∀ σ, σ.IsIrreducible → SmoothRep.IsSubquotient σ X → IsTwist σ
  let InBlockG : ObjectProperty (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)) :=
    fun Y => ∀ τ, τ.IsIrreducible → SmoothRep.IsSubquotient τ Y →
      ∃ σ, IsTwist σ ∧
        SmoothRep.IsSubquotient τ ((leviInductionFunctor p l r hp hr hl hmul).obj σ)
  change InBlockM.ι.IsRightAdjoint ∧ _
  constructor
  · have hEq : InBlockM = rationalInertiaBlockProperty M ρ := by
      funext X
      apply propext
      constructor
      · intro hX σ hσ hσX
        exact (isRationalInertiaRelated_iff_linearEquiv M ρ σ).mpr (hX σ hσ hσX)
      · intro hX σ hσ hσX
        exact (isRationalInertiaRelated_iff_linearEquiv M ρ σ).mp (hX σ hσ hσX)
    rw [hEq]
    exact rationalInertiaBlock_isRightAdjoint_of_representedCuspidal
      hSplit k M hl.isConnectedReductive ρ hρ hA
  · intro L adjL
    obtain ⟨_, _, hmaps, hfull, hfaithful, hess⟩ :=
      hBlocks k G hG P M U p l r hp hl hr hmul hproper hmax ρ hρ hA hnonself
    let R := InBlockM.ι ⋙ leviInductionFunctor.{u, max u v} p l r hp hr hl hmul
    have : R.Full := hfull
    have : R.Faithful := hfaithful
    exact Renard.fullSubcategory_adjunction_equivalence InBlockG
      (leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul ⋙ L) R
      ((leviFirstAdjointnessAdjunction.{u, v} p l r hp hl hr hmul).comp adjL)
      (fun X => hmaps X.obj X.property) (fun Y => by
        obtain ⟨X, hX, he⟩ := hess Y.obj Y.property
        exact ⟨⟨X, hX⟩, he⟩)

set_option linter.defProp false in
/-- The conditional block-projection reduction as a defined proof term. -/
def maximalLeviBlockProjectionEquivalenceOfDecompositionOfBlocks :
    RationalCuspidalInertiaDecompositionStatement.{u, max u v} →
      MaximalLeviBlockStatements.{u, v} →
        MaximalLeviBlockProjectionEquivalenceStatement.{u, v} :=
  maximalLeviBlockProjectionEquivalence_of_decomposition_of_blocks

end Langlands.Aubert.General.RepresentedParabolic
