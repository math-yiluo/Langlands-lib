/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersection
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationCounit
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralUnderivedPushComparison

/-! # Rationalization of the canonical intersection lattice -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical intersection recovers the original rational module after scalar extension.
Source: Bhatt--Scholze, Lemma 6.8.13; localization and qcqs pushforward continuity.
(auxiliary; not a blueprint node)
Proof. Qcqs pushforward commutes with localization. The mates counit equation then
makes the scalar extension of the pushed lattice embedding invertible. Exact scalar
extension carries the pullback of its image to the whole restricted rational module.
The localization counit identifies its scalar extension with the original module. -/
theorem continuousLatticeIntersectionRationalization_isIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    {U : Scheme.{u}} (p : U ⟶ X) [QuasiCompact p] [QuasiSeparated p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) U))
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P) :
    IsIso (latticeIntersectionRationalization (integralScalarMap ℓ E) X P p M e) := by
  have := integralScalarCounit_isIso ℓ E X P
  have := integralScalarCounit_isIso ℓ E X
    ((lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((upperStar (Profinite.continuousMapRingObj E) p).obj P))
  have := integralScalarUnderivedPushHom_isIso ℓ E p M
  have := latticePushedEmbedding_map_isIso (integralScalarMap ℓ E) X P p M e
  exact latticeIntersectionRationalization_isIso_of_map_isIso
    (integralScalarMap ℓ E) X P p M e

end AlgebraicGeometry.ProEtale.CondensedRing
