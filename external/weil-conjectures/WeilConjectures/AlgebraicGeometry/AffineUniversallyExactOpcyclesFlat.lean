/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.FlatOpcyclesTorCriterion
import WeilConjectures.AlgebraicGeometry.AffineUniversalTensorExact
import WeilConjectures.AlgebraicGeometry.AffineOpcyclesFlatFromSections

/-! # Flat opcycles of a universally exact affine complex

Source: Stacks Project, Tag 0653, affine specialization and square-zero algebra testing.
(blueprint: lem-pc-affine-universally-exact-opcycles-flat).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Universal vanishing in degree -1 makes the degree-zero opcycles flat.
Source: Stacks Project, Tag 0653, its tensor-exactness criterion, and Tag 01IB.
(blueprint: lem-pc-affine-universally-exact-opcycles-flat).

Proof: Put A = Γ(S, ⊤). The affine quasi-coherent equivalence identifies C with
its global-sections complex P of A-modules. Its terms are flat: use the flatness
hypothesis with both affine opens equal to S. For any A-module N, pull back to
Spec(A ⊕ N), where A ⊕ N is the trivial square-zero extension. The resulting
complex of A-modules is P ⊕ (P tensor N). Its homology in degree -1 is zero by
hypothesis, and the second summand therefore has zero homology. Apply
Module.Flat.opcycles_of_exactAt at zero to P. Sheafification preserves cokernels,
so C.opcycles 0 is the sheaf associated to the flat A-module P.opcycles 0.
For affine opens U contained in V in S, restriction identifies its sections on U
with the tensor product of its sections on V and Γ(S,U). Its sections on V are
flat by localization of the flat associated sheaf, and Γ(S,U) is flat over Γ(S,V)
since U -> V is an open immersion. Transitivity gives the precise IsFlatOver
condition. No boundedness or finite-presentation assumption is used. If S is
empty or C is zero all these modules are zero, so the same argument applies. -/
theorem affine_opcycles_flat_of_universally_exact (S : Scheme.{u}) (hS : IsAffine S)
    (C : CochainComplex S.Modules ℤ)
    (hflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 S))
    (hqc : ∀ n : ℤ, (C.X n).IsQuasicoherent)
    (hexact : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsZero ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology (-1))) :
    (C.opcycles 0).IsFlatOver (𝟙 S) := by
  let F : S.Modules ⥤ ModuleCat.{u} Γ(S, ⊤) :=
    SheafOfModules.evaluation (R := S.ringCatSheaf) (.op ⊤)
  have : F.Additive := ⟨rfl⟩
  let P := (F.mapHomologicalComplex (.up ℤ)).obj C
  have hPflat : ∀ n : ℤ, Module.Flat Γ(S, ⊤) (P.X n) := by
    intro n
    have : IsAffine S := hS
    change Module.Flat Γ(S, ⊤) Γ(C.X n, ⊤)
    convert hflat n ⟨⊤, isAffineOpen_top S⟩ ⟨⊤, isAffineOpen_top S⟩ le_rfl using 1
    ext r m
    change r • m = ((Scheme.Hom.appLE (𝟙 S) ⊤ ⊤ le_rfl).hom r) • m
    congr 1
    simp [Scheme.Hom.appLE]
  have hPtensor : ∀ N : ModuleCat.{u} Γ(S, ⊤),
      (((MonoidalCategory.tensorRight N).mapHomologicalComplex (.up ℤ)).obj P).ExactAt
        (0 - 1) := by
    intro N
    exact affine_universal_tensor_exact S hS C (-1) hqc hexact N
  have hQflat := Module.Flat.opcycles_of_exactAt P 0 hPflat hPtensor
  exact affine_opcycles_flat_from_sections S hS C 0 (hqc _) (hqc _) hQflat

end AlgebraicGeometry.Scheme.Modules
