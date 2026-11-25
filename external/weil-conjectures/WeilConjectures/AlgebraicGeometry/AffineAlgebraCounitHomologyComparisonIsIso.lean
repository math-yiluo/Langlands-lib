/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineAlgebraKInjectiveCounitCompatibility
import WeilConjectures.AlgebraicGeometry.AffineAlgebraCanonicalComparisonIdentification

/-! # Invertibility of the canonical affine direct-image homology comparison

Source: Stacks Project, Tags 0AVW and 08D4.
-/

@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry

/-- The canonical comparison, rather than an arbitrary isomorphism between its
source and target, is invertible for a K-injective complex with quasi-coherent
cohomology under an affine morphism.
Source: Stacks Project, Tag 0AVW, proof of affine-morphism-equivalence, the displayed
cohomology comparison; Tag 08D4 supplies its unbounded justification.
(blueprint: lem-sc-affine-algebra-counit-homology-comparison-isIso).

Proof: Work on an affine basis V of Y. The inverse images U are affine. On each
U, quasi-coherent sheaves have no positive cohomology. K-injectivity computes
sections-derived cohomology of I. Sections on U commute with countable
products, computed sectionwise. The truncation argument of Tag 08D4 with bound one
therefore identifies H^n(Gamma(U,I)) with Gamma(U,H^n(I)) for every integer n,
including unbounded I. The edge morphism is canonical: it sends a
cycle section to its cohomology class. It preserves the f_*O_X action and
commutes with restrictions; hence these morphisms give an invertible comparison
of f_*O_X-module sheaves. For the standard tensor pullback adjunction, this
comparison is the adjoint mate of the homology counit: evaluating the counit on
a pure tensor multiplies its coefficient with the cycle section, and the exact
pullback homology comparison preserves that operation. Thus it equals the map
constructed in affineAlgebraCounitHomologyComparison. Any other adjunction a
with exact left adjoint P is uniquely isomorphic to this one as an adjunction;
the exact homology comparison is natural in that isomorphism and the homEquiv
maps agree under it, so the mate is unchanged. Invertibility follows locally,
hence globally. For empty schemes and zero complexes the comparison is between
zero objects; degrees outside the cohomology support are also between zero
objects. No counit invertibility or derived equivalence is used. -/
theorem affineAlgebraCounitHomologyComparison_isIso
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    [P.Additive] [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P]
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ) :
    IsIso (affineAlgebraCounitHomologyComparison f P a I n) := by
  obtain ⟨e, he⟩ := affine_algebra_kinjective_canonical_comparison_identification
    f P a I hI n
  rw [← he]
  infer_instance

end AlgebraicGeometry
