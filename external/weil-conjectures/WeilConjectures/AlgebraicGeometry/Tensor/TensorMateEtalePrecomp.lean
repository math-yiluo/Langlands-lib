/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumExtensionTensor
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
import WeilConjectures.AlgebraicGeometry.Etale.EtalePrecompProjection

/-!
# Canonical tensor mates under etale precomposition

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-cohsm/thm-asd-smooth-tensor.proof.md, paragraph 3
(blueprint: lem-asd-tensor-mate-etale-precomp).

The locality isomorphism uses the graph-normalized compact-support comparison and the
termwise sum/evaluation adjunction. The theorem states both the actual tensor-mate equality
and the sum-counit normalization on the whole ordinary unbounded derived categories.
-/

@[expose] public section

set_option autoImplicit false

universe v

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The canonical etale locality comparison `u^* f^× ≅ (fu)^×`.
Source: the blueprint proposition-exceptional-inverse-image-smooth-morphism proof, paragraph 3
(blueprint: lem-asd-tensor-mate-etale-precomp).

Conjugate the specified proper/open tower comparison against the composite of the
sum-extension/evaluation adjunction and the exceptional adjunction. The normalization `N`
includes the graph-section characterization, so this construction uses no arbitrary
isomorphism or arbitrary adjunction for the etale map. Its existence is supplied by
`nonempty_etaleCompactSupportNormalization`; the theorem below holds for every such `N`.
-/
noncomputable def tensorMateEtalePrecompLocalityIso
    (A : Type (v + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X S : Scheme.{v}} (u : U ⟶ X) (f : X ⟶ S)
    [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    [HasCompactification f] [HasCompactification (u ≫ f)] :
    R(f)^![A] ⋙ (u)^*[ModuleCat A].mapDerivedCategory ≅
      R(u ≫ f)^![A] :=
  ((conjugateIsoEquiv
    (rightDerivedUpperShriekAdjunction A (u ≫ f))
    (((etaleLowerShriekUpperStarAdjunction (ModuleCat A) u
          inferInstance).mapDerivedCategoryAdjunction).comp
      (rightDerivedUpperShriekAdjunction A f)))
    (etaleAmbientLeftComparison A N u f
      (HasCompactification.compactification f)
      (HasCompactification.compactification (u ≫ f)))).symm

end AlgebraicGeometry.Etale
