/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

noncomputable local instance tensorNaturality (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- The tensor comparison for canonical open restriction is natural in both modules.
Source: Stacks Project, Tag 01CD, functoriality of pullback and tensor product;
Tag 08DX, proof of (1), applies the resulting comparison locally.
Proof: Scheme.Modules.overFunctorEquiv identifies the canonical over-site composite
with restriction along U.ι. Compose with restrictFunctorIsoPullback to identify it
naturally with Scheme.Modules.pullback U.ι. The source library gives this pullback
its monoidal structure. Transport that structure along the inverse natural
isomorphism using Functor.Monoidal.transport. Choose the inverse tensorators of
the transported structure; Functor.OplaxMonoidal.δ_natural gives the displayed
square. This construction applies to every open, including the empty open.
(blueprint: lem-pc-open-restriction-tensor-natural). -/
theorem exists_openRestriction_tensor_natural (X : Scheme.{u}) (U : X.Opens) :
    let R :=
      SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)
    ∃ e : ∀ (F G : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      R.obj (F ⊗ G) ≅ R.obj F ⊗ R.obj G,
      ∀ (F F' G G' : SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (f : F ⟶ F') (g : G ⟶ G'),
        R.map (f ⊗ₘ g) ≫ (e F' G').hom =
          (e F G).hom ≫ (R.map f ⊗ₘ R.map g) := by
  dsimp only
  let i := Scheme.Modules.overFunctorEquiv U ≪≫
    Scheme.Modules.restrictFunctorIsoPullback U.ι
  let R := SheafOfModules.overFunctor X.ringCatSheaf U ⋙
    (Scheme.Modules.overEquiv U).functor
  let : (Scheme.Modules.pullback U.ι).Monoidal :=
    Scheme.Modules.pullbackMonoidal U.ι
  let : R.Monoidal := Functor.Monoidal.transport i.symm
  refine ⟨fun F G ↦ (Functor.Monoidal.μIso R F G).symm, ?_⟩
  intro F F' G G' f g
  exact (Functor.OplaxMonoidal.δ_natural R f g).symm

end AlgebraicGeometry
