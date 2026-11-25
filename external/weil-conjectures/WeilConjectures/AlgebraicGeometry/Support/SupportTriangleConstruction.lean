/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtalePairFlasque
public import WeilConjectures.AlgebraicGeometry.Pur.PurSupportExact
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-! # The pro-etale supported-sections cone

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
`lemma-local-cohomology-right-adjoint--2` (blueprint: lemma-local-cohomology-right-adjoint--2).

The three complexes, inclusion, quotient map, and negative shifted projection are fixed.
The triangle takes only the proof that its specified cone quotient is invertible.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Additivity needed to apply the supported kernel termwise. Source: the natural kernel
maps of blueprint `lemma-local-cohomology-right-adjoint--2` (blueprint:
lemma-local-cohomology-right-adjoint--2). Proof: compose the kernel map of a sum with the monic
kernel inclusion. Naturality makes this the sum of the two composites. Cancel the inclusion; the
same argument handles zero. -/
theorem supportKernelAdditive {X U : Scheme.{u}} (j : U ⟶ X) :
    (finiteSupportedSections Λ j).Additive := by
  constructor
  intro M N f g
  let ι := finiteSupportedSectionsι Λ j
  have : Mono (ι.app N) :=
    inferInstanceAs (Mono (((evaluation _ _).obj N).map
      (kernel.ι (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit)))
  apply (cancel_mono (ι.app N)).1
  rw [Preadditive.add_comp, ι.naturality, ι.naturality, ι.naturality]
  simp

attribute [instance] supportKernelAdditive

/-- Additivity of closed inverse image of the supported kernel. Source: blueprint
`lemma-local-cohomology-right-adjoint--2` (blueprint: lemma-local-cohomology-right-adjoint--2).
Proof: `finiteClosedUpperShriek` is the composite of the additive supported-kernel
functor and the additive module inverse image; composition preserves sums. -/
theorem supportShriekAdditive {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X) :
    (finiteClosedUpperShriek Λ s j).Additive := by
  unfold finiteClosedUpperShriek
  infer_instance

attribute [instance] supportShriekAdditive

variable {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
  [IsClosedImmersion s] [IsOpenImmersion j] [QuasiCompact j]
  (hPair : IsCompl (Set.range s) (Set.range j))

/-- The actual inclusion `s_*s^!M → M`: invert the canonical supported-kernel comparison,
then apply its kernel inclusion. Source: blueprint `lemma-local-cohomology-right-adjoint--2`
(blueprint: lemma-local-cohomology-right-adjoint--2). -/
noncomputable def supportModelInclusion :
    finiteClosedUpperShriek Λ s j ⋙ lowerStar (ModuleCat.{u + 1} Λ) s ⟶ 𝟭 _ :=
  letI := finiteSupportedClosedComparison_isIso Λ s j hPair
  (asIso (finiteSupportedClosedComparison Λ s j)).inv ≫ finiteSupportedSectionsι Λ j

/-- The complex `C(I)=j_*j^*I`, applied termwise. Source: blueprint
`lemma-local-cohomology-right-adjoint--2` (blueprint: lemma-local-cohomology-right-adjoint--2). -/
noncomputable def supportCComplex
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ) :=
  ((upperStar (ModuleCat.{u + 1} Λ) j ⋙ lowerStar (ModuleCat.{u + 1} Λ) j).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I

section GenericTriangle

universe v w
variable {C : Type v} [Category.{w} C] [Abelian C] [HasDerivedCategory C]

end GenericTriangle

end AlgebraicGeometry.ProEtale
