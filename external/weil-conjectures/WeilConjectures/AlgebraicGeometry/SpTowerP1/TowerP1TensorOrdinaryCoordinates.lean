/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Data
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Normalized tensor coordinates for projective-line level comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Levels
(blueprint: def-sp-p1-tensor-ordinary-coordinates).

The coordinates retain the canonical associated-module-sheaf functor. Its tensor
comparison is fixed on scalar-unit pure tensors, on total-complex summands, and
on K-flat representatives. Thus the final level equations cannot be satisfied
by choosing unrelated isomorphisms of their endpoints.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ) [Finite (SpTowerShriek.R l E n)]

/-- The actual fixed-scalar pro-etale sheaf category at level n+1.
Source: Levels (blueprint: def-sp-p1-tensor-ordinary-coordinates). -/
abbrev FixedSheaves (T : Scheme.{u}) :=
  Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n)))

/-- Its canonical associated-module-sheaf realization, with constant scalar sections.
Source: Levels (blueprint: def-sp-p1-tensor-ordinary-coordinates). -/
def realization (T : Scheme.{u}) : FixedSheaves l E n T ⥤
    SemilinearSections.Mod.{u + 1, u, u + 1}
      (ProEt.topology T) (SpTowerShriek.B l E T n) :=
  (sfIntrinsicModuleEquivalence T (SpTowerShriek.R l E n)).functor

/-- Additivity of the canonical realization, inherited from its published functor.
Source: Levels (blueprint: def-sp-p1-tensor-ordinary-coordinates). -/
instance realizationAdditive (T : Scheme.{u}) : (realization l E n T).Additive :=
  inferInstanceAs (sfIntrinsicModuleEquivalence T (SpTowerShriek.R l E n)).functor.Additive

/-- The canonical realization preserves kernels.
Source: Levels (blueprint: def-sp-p1-tensor-ordinary-coordinates). -/
instance realizationLimits (T : Scheme.{u}) : PreservesFiniteLimits (realization l E n T) :=
  inferInstanceAs (PreservesFiniteLimits
    (sfIntrinsicModuleEquivalence T (SpTowerShriek.R l E n)).functor)

/-- The canonical realization preserves cokernels.
Source: Levels (blueprint: def-sp-p1-tensor-ordinary-coordinates). -/
instance realizationColimits (T : Scheme.{u}) : PreservesFiniteColimits (realization l E n T) :=
  inferInstanceAs (PreservesFiniteColimits
    (sfIntrinsicModuleEquivalence T (SpTowerShriek.R l E n)).functor)

/-- The same canonical equivalence, exposed for resolution transport.
Source: Levels (blueprint: def-sp-p1-tensor-ordinary-coordinates). -/
instance realizationEquivalence (T : Scheme.{u}) : (realization l E n T).IsEquivalence :=
  inferInstanceAs (sfIntrinsicModuleEquivalence T (SpTowerShriek.R l E n)).functor.IsEquivalence

/-- The pure tensor in the fixed-scalar sheaf tensor, through the actual inclusion tensorator.
Source: Levels (blueprint: def-sp-p1-tensor-ordinary-coordinates). -/
def fixedTensorSection (T : Scheme.{u}) (M N : FixedSheaves l E n T) (U : T.ProEtᵒᵖ)
    (x : M.obj.obj U) (y : N.obj.obj U) : (M ⊗ N).obj.obj U :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n)))) M N).app U)
      (x ⊗ₜ[ULift.{u + 1} (SpTowerShriek.R l E n)] y)

/-- Realization tensor coordinates with every map fixed before localization.
The final square is imposed on all K-flat representatives, not just on cohomology.
Source: Levels (blueprint: def-sp-p1-tensor-ordinary-coordinates). -/
structure TensorOrdinaryCoordinates (T : Scheme.{u}) where
  ordinary : ∀ M N : FixedSheaves l E n T,
    (realization l E n T).obj (M ⊗ N) ≅
      SemilinearSections.ordinaryTensor.{u + 1, u, u + 1} (ProEt.topology T)
        (SpTowerShriek.B l E T n)
        ((realization l E n T).obj M) ((realization l E n T).obj N)
  pure : ∀ (M N : FixedSheaves l E n T) (U : T.ProEtᵒᵖ)
    (x : M.obj.obj U) (y : N.obj.obj U),
    (ordinary M N).hom.val.app U
      (sfIntrinsicRealizationUnit T (SpTowerShriek.R l E n) (M ⊗ N) U
        (fixedTensorSection l E n T M N U x y)) =
      SemilinearSections.tensorSection.{u + 1, u, u + 1} (ProEt.topology T)
        (SpTowerShriek.B l E T n)
        ((realization l E n T).obj M) ((realization l E n T).obj N) U
        (sfIntrinsicRealizationUnit T (SpTowerShriek.R l E n) M U x)
        (sfIntrinsicRealizationUnit T (SpTowerShriek.R l E n) N U y)

end AlgebraicGeometry.ProEtale.SpTowerP1
