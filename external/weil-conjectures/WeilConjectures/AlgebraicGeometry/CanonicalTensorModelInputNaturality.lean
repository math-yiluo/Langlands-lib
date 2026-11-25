/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison

/-! # Naturality of the localization tensor model

Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96. (blueprint: lem-pc-tensor-model-input-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- The canonical tensor model map commutes with a chain map in its first variable.
Source: Stacks Project, cohomology.tex, Tag 06YH (derived tensor construction), and
Tag 08DJ (representative tensor-Hom comparison).
(blueprint: lem-pc-tensor-model-input-naturality).

Proof: The map pullbackTensorModelMap is the lax monoidal structure map μ of Q,
using the shared sheaf tensor, total-complex tensor, and derived tensor instances.
Apply Functor.LaxMonoidal.μ_natural to f and the identity of L. Q preserves the
identity, and the tensor of chain maps is mapBifunctorMap f (identity L) by the
definition of HomologicalComplex.tensorHom. These substitutions give exactly the
stated equation. Match the local monoidal instances to the instances used in the
definition of pullbackTensorModelMap; its auxiliary additivity, flat resolution,
Grothendieck and colimit proofs are propositions, hence proof irrelevant. The
statement requires no K-flatness: invertibility of μ is not used. It holds for zero
maps, zero complexes and identity maps, directly by lax monoidal naturality. -/
theorem tensorModelMap_input_natural (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P P' L : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) (f : P ⟶ P') :
    let := SheafOfModules.monoidalCategory X.sheaf
    let := schemeDerivedTensorMonoidal X
    (DerivedCategory.Q.map f ⊗ₘ 𝟙 (DerivedCategory.Q.obj L)) ≫
        pullbackTensorModelMap X P' L =
      pullbackTensorModelMap X P L ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f (𝟙 L)
          (curriedTensor _) (.up ℤ))  := by
  dsimp only
  let := pullbackDescentModuleTensor X
  let := moduleSymmetric X
  have := modulePreadditive X
  let := moduleClosed X
  have := moduleGrothendieck X
  have := moduleResolutions X
  have := moduleDerivedMonoidal X
  let := pullbackDescentQLax X
  change (DerivedCategory.Q.map f ⊗ₘ 𝟙 _) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q P' L =
    Functor.LaxMonoidal.μ DerivedCategory.Q P L ≫
      DerivedCategory.Q.map (f ⊗ₘ 𝟙 L)
  have h := Functor.LaxMonoidal.μ_natural DerivedCategory.Q f (𝟙 L)
  rw [CategoryTheory.Functor.map_id] at h
  exact h
end AlgebraicGeometry
