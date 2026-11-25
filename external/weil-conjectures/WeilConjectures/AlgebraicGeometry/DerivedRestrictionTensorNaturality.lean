/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Naturality of derived tensor under exact open restriction
Source: Stacks Project, Tag 079U, specialized to an open immersion.
(blueprint: lem-sc-derived-restriction-tensor-naturality).
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

-- Transporting the monoidal model unfolds the exact-functor localization data.
/-- The objectwise tensor comparisons can be chosen bifunctorially.
Source: Stacks Project, Tag 079U (proof), and Tag 08DX (1).
(blueprint: lem-sc-derived-restriction-tensor-naturality).

Proof: identify module tensor pullback along U.ι with exact over-site restriction
followed by the canonical over equivalence. The usual pullback and restriction
adjunctions give the first identification, and Modules.overFunctorEquiv gives the
second. Exactness of restriction transports to module tensor pullback. Exactness
exhibits its mapDerivedCategory as its left derived functor with the localization
factorization as counit. Uniqueness of left derived functors identifies the recorded
derivedPullback U.ι with this exact derived functor; derive the module identification
to obtain a natural isomorphism to R. Take the already stated canonical monoidal
model of derived pullback and transport its monoidal structure through that natural
isomorphism. Its inverse tensorators are the required t, and oplax tensorator
naturality is exactly the displayed equation. All constructions apply to the empty
open and arbitrary unbounded objects. -/
theorem exists_derivedRestriction_tensor_natural
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))] :
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    ∃ t : ∀ K L : schemeDerivedCategory X, R.obj (K ⊗ L) ≅ R.obj K ⊗ R.obj L,
      ∀ K K' L L' (a : K ⟶ K') (b : L ⟶ L'),
        R.map (a ⊗ₘ b) ≫ (t K' L').hom =
          (t K L).hom ≫ (R.map a ⊗ₘ R.map b) := by
  classical
  dsimp only
  let R := SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U ⋙
    Equivalence.functor
      (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
  have : PreservesFiniteLimits R := by
    dsimp [R]
    infer_instance
  have : PreservesFiniteColimits R := by
    dsimp [R]
    infer_instance
  have : R.Additive := inferInstance
  let η : Modules.tensorPullback U.ι ≅ Modules.restrictFunctor U.ι :=
    (Modules.nonempty_tensorPullbackAdjunction U.ι).some.leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction U.ι) ≪≫
        (Modules.restrictFunctorIsoPullback U.ι).symm
  let θ : Modules.tensorPullback U.ι ≅ R := η ≪≫ (Scheme.Modules.overFunctorEquiv U).symm
  let P : SheafOfModules.{uX} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace) :=
    Modules.tensorPullback U.ι
  have : PreservesFiniteLimits P := preservesFiniteLimits_of_natIso θ.symm
  have : PreservesFiniteColimits P := preservesFiniteColimits_of_natIso θ.symm
  have : P.Additive := inferInstance
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    F, hF, hFmap, hFadd, ε, hL, htri, hK⟩ :=
    (derivedPullback_spec.{uX, wD} U.ι)
  have h : F = P := CategoryTheory.Functor.ext hF (fun M N a ↦ hFmap a)
  subst F
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) (.up ℤ)
  have : (derivedPullback.{uX, wD} U.ι).IsLeftDerivedFunctor ε W := hL
  have : P.mapDerivedCategory.{wD, wD}.IsLeftDerivedFunctor
      P.mapDerivedCategoryFactorsh.{wD, wD}.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ P.mapDerivedCategoryFactorsh.{wD, wD}
  let i : derivedPullback.{uX, wD} U.ι ≅ R.mapDerivedCategory.{wD, wD} :=
    Functor.leftDerivedUnique P.mapDerivedCategory.{wD, wD} (derivedPullback.{uX, wD} U.ι)
      ε P.mapDerivedCategoryFactorsh.{wD, wD}.hom W ≪≫ Functor.mapDerivedCategoryNatIso θ
  -- Only the monoidal structure is needed; avoid eliminating its large model certificate.
  let m := Classical.choose (exists_derivedPullbackMonoidalModel.{uX, wD} U.ι)
  let := m.toMonoidal
  let : R.mapDerivedCategory.{wD, wD}.Monoidal := Functor.Monoidal.transport i
  refine ⟨fun K L ↦ (Functor.Monoidal.μIso R.mapDerivedCategory.{wD, wD} K L).symm, ?_⟩
  intro K K' L L' a b
  exact (Functor.OplaxMonoidal.δ_natural R.mapDerivedCategory.{wD, wD} a b).symm

end AlgebraicGeometry.Scheme
