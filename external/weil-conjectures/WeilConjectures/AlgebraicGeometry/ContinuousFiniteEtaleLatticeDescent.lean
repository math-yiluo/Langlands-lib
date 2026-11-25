/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionLocalModel
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionRationalization
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixKernelLocallyFree
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.CategoryTheory.SiteModuleCompatibleTuples

/-! # Integral lattices descend along finite etale surjections

Source: Bhatt--Scholze, first paragraph of the proof of Lemma 6.8.13.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A lisse rational module with an integral lattice on a finite etale cover
has an integral lisse lattice on the base. No descent datum on the input lattice
is required. Source: Bhatt--Scholze, Lemma 6.8.13, first paragraph.
(auxiliary; not a blueprint node)

Proof in words. Construct the integral module as the inverse image, under the
rational adjunction unit P → p_*p^*P, of the image of the pushed lattice map
p_*M → Res(p_*p^*P). This is a categorical image and pullback, with its canonical
inclusion into Res(P); it makes no choices of local splittings or descent data.
The supplied rationalization and the scalar-extension/pushforward mate identify
the pushed map after extending coefficients. Qcqs pushforward preserves the scalar
localization telescope, and the localization counit is invertible. Exact scalar
extension therefore turns the inclusion of the image-pullback into an isomorphism.
Its adjoint is the required rationalization isomorphism to P.

For local freeness, the finite-sheet local matrix model describes the restriction
of this constructed module as the kernel of an integral finite matrix which is
surjective after rationalization. The integral matrix pivot theorem reduces its
kernel, one source rank at a time, to the zero-matrix case. Its rational cokernel
is zero, so the pivot hypothesis continues to hold. This proves local finite
freeness of each model. Undo the coefficient normalization and compose its
trivializing covers with the cover giving the local models. The resulting cover
witnesses the local finite freeness required in the conclusion. Rank zero and
empty schemes are included in these categorical constructions. -/
theorem continuousLisse_finiteEtale_lattice
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P)
    {U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) U))
    (hM : IsLocallyFree (condensedRingObj (integralCoeff ℓ E) U) M)
    (e : Nonempty ((Mod.extendScalars
      (coefficientMap (integralScalarMap ℓ E) U)).obj M ≅
        (CondensedRing.upperStar (Profinite.continuousMapRingObj E) p).obj P)) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X),
      (IsLocallyFree (condensedRingObj (integralCoeff ℓ E) X) N) ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj N ≅ P) := by
  classical
  obtain ⟨e⟩ := e
  let N := latticeIntersection (integralScalarMap ℓ E) X P p M e
  have hN : IsLocallyFree (condensedRingObj (integralCoeff ℓ E) X) N := by
    obtain ⟨C, hC⟩ := continuousLatticeIntersection_localModel ℓ E X P hP p M hM e
    apply localFree_of_cover C
    intro s
    obtain ⟨n, m, f, hf, ⟨eN⟩⟩ := hC s
    have := hf
    have hT :=
      (integralMatrixKernel_locallyFree_of_rational_epi ℓ E (C.X s) n m f).of_iso eN.symm
    exact localFree_of_comap
      (inv (condensedPullbackHom (integralCoeff ℓ E) (C.f s))) hT
  have := continuousLatticeIntersectionRationalization_isIso ℓ E X P p M e
  exact ⟨N, hN, ⟨asIso
    (latticeIntersectionRationalization (integralScalarMap ℓ E) X P p M e)⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
