/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange
import WeilConjectures.AlgebraicGeometry.Proper.ProperRestrictionSiteSquare
import WeilConjectures.AlgebraicGeometry.Open.OpenRestrictionSiteSquare
import all WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition

/-! # Scalar restriction and the compositor on etale-origin complexes

Source: Stacks Project, Tags 09AF, 099R, 0F7J and 0GL6
(blueprint: lem-sf-origin-compact-restriction-composition).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

private theorem transport_square
    {C : Type*} [Category C] {S₀ S T₀ T V₀ V : C}
    (u : S₀ ⟶ S) [Epi u] (l₀ : S₀ ⟶ T₀) (l : S ⟶ T)
    (a₀ : S₀ ⟶ V₀) (a : S ⟶ V) (v : V₀ ⟶ V)
    (c₀ : V₀ ⟶ T₀) (c : V ⟶ T) (w : T₀ ⟶ T)
    (hl : u ≫ l = l₀ ≫ w) (h₀ : l₀ = a₀ ≫ c₀)
    (hc : v ≫ c = c₀ ≫ w) (ha : u ≫ a = a₀ ≫ v) : l = a ≫ c := by
  apply (cancel_epi u).mp
  rw [hl, h₀, Category.assoc, ← hc, ← reassoc_of% ha]

attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftAdjoint Functor.rightAdjoint
  comparisonUpperStar pbcDerivedComparisonRestrict compactSupportSiteComparison

attribute [local irreducible] originCompositionAmbient originCompositionModel

attribute [local irreducible] compactSupportRestrictionIso

end AlgebraicGeometry.ProEtale
