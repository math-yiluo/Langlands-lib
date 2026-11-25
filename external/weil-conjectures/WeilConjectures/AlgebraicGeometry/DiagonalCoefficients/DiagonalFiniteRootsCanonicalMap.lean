/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.RawModuleScalarComparison.RawModuleScalarDerivedPullbackIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Uniqueness of the finite-root scalar map -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
attribute [local irreducible] comparisonUpperStar cartierRootsComparison cartierRootsIso
  forgetComparisonIso cartierForgetComparison

/-- A kernel-normalized finite roots comparison gives the canonical scalar root map.
Source: diagonal coefficient changes (1), root endpoint normalization.
(blueprint: lem-diagonal-finite-roots-canonical-map).
Proof: the two roots isomorphisms have identical composites with the monic kernel
inclusion into units. Cancel that inclusion to identify them. The scalar-forgetting
comparison is the same adjunction mate in both definitions, so substitution gives
the displayed equality. Positive N and its invertibility provide the canonical root
isomorphism; the proof also applies to zero coefficient rings and empty schemes. -/
theorem finiteRoots_toLine_eq_cartierProRootMap {X : Scheme.{u}} {N : ℕ} (r : FiniteRoots X N)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (hN : 0 < N) (hX : IsUnit (N : Γ(X, ⊤))) :
    r.toLine A hA = cartierProRootMap A N hA X hN hX := by
  have he : r.iso = cartierRootsIso X N hN hX := by
    have : Mono (Scheme.proEtaleRootsOfUnityInclusion X N) := by
      dsimp [Scheme.proEtaleRootsOfUnityInclusion]
      infer_instance
    apply Iso.ext
    apply (cancel_mono (Scheme.proEtaleRootsOfUnityInclusion X N)).mp
    refine r.inclusion.trans ?_
    symm
    unfold cartierRootsIso
    change cartierRootsComparison X N ≫ _ = _
    unfold cartierRootsComparison
    exact kernel.lift_ι _ _ _
  unfold FiniteRoots.toLine cartierProRootMap
  rw [he]
  congr 1
  rw [forgetComparisonIso_hom]
  unfold cartierForgetComparison
  rfl

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
