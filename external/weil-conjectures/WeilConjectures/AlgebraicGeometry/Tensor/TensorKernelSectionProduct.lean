/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedPresentation

/-! # Tensor products with a kernel section

Source: Stacks Project, Tags 08KS and 09MS, the ideal-tensor kernel sequence.
(blueprint: lem-sc-tensor-kernel-section-product).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

private theorem ideal_tensor_shuffle {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] (A B J D : C) (i : J ⟶ 𝟙_ C) (m : A ⊗ B ⟶ D) :
    (α_ A J B).inv ≫ (β_ A J).hom ▷ B ≫ (α_ J A B).hom ≫ J ◁ m ≫
        i ▷ D ≫ (λ_ D).hom = A ◁ (i ▷ B ≫ (λ_ B).hom) ≫ m := by
  rw [whisker_exchange_assoc, leftUnitor_naturality]
  rw [← associator_naturality_left_assoc]
  rw [← comp_whiskerRight_assoc, ← BraidedCategory.braiding_naturality_right]
  rw [braiding_tensorUnit_right]
  simp only [comp_whiskerRight, Category.assoc]
  monoidal

/-- Multiplying a tensor-power section by a kernel section stays in the next kernel.
Source: Stacks Project, Tag 08KS (kernel of the closed-immersion unit) and Tag 09MS
(the tensor-power ideal sequence).
(blueprint: lem-sc-tensor-kernel-section-product).
Proof: The kernel of the unit on L^d is the subsheaf J L^d. The tensor-power
multiplication L^a tensor L^d to L^(a+d) carries L^a tensor J L^d into J L^(a+d):
locally a generator r t with r in J maps to r times the product of the two sections.
Equivalently, use the ideal-kernel comparison and the associator and symmetry to
construct a morphism L^a tensor K_d to J tensor L^(a+d), then follow the
ideal-kernel comparison in degree a+d. Its composite with the kernel inclusion is
the tensor-power multiplication followed after the degree-d kernel inclusion.
Evaluate this morphism on the elementary tensor of s and y to obtain z.
This argument uses only the kernel description, not square-zero annihilation or a
graded algebra presentation. Degree zero uses the tensor unit and the same unitors;
on the empty open all sections are zero. -/
theorem tensorKernel_section_product {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (a d : ℕ)
    (U : X.Opens) (s : Γ(L.tensorPow a, U))
    (y : Γ(kernel (tensorGradedUnit j (L.tensorPow d)), U)) :
    ∃ z : Γ(kernel (tensorGradedUnit j (L.tensorPow (a + d))), U),
      (kernel.ι (tensorGradedUnit j (L.tensorPow (a + d)))).app U z =
        (L.tensorPowAddIso a d).inv.app U
          (tmulSection s ((kernel.ι (tensorGradedUnit j (L.tensorPow d))).app U y)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let A := L.tensorPow a
    let B := L.tensorPow d
    let C := L.tensorPow (a + d)
    let J := j.ker.toModules
    let ed := boundaryIdealKernelIso j B
    let ead := boundaryIdealKernelIso j C
    have hd : ed.hom ≫ kernel.ι (tensorGradedUnit j B) =
        j.ker.toModulesι ▷ B ≫ (λ_ B).hom :=
      Classical.choose_spec (boundaryIdealKernelIso_exists j B)
    have had : ead.hom ≫ kernel.ι (tensorGradedUnit j C) =
        j.ker.toModulesι ▷ C ≫ (λ_ C).hom :=
      Classical.choose_spec (boundaryIdealKernelIso_exists j C)
    let m := (L.tensorPowAddIso a d).inv
    let q : A ⊗ (J ⊗ B) ⟶ J ⊗ C :=
      (α_ A J B).inv ≫ (β_ A J).hom ▷ B ≫ (α_ J A B).hom ≫ J ◁ m
    let v : A ⊗ kernel (tensorGradedUnit j B) ⟶ kernel (tensorGradedUnit j C) :=
      A ◁ ed.inv ≫ q ≫ ead.hom
    have hv : v ≫ kernel.ι (tensorGradedUnit j C) =
        A ◁ kernel.ι (tensorGradedUnit j B) ≫ m := by
      dsimp only [v]
      rw [Category.assoc, Category.assoc, had]
      have hq := ideal_tensor_shuffle A B J C j.ker.toModulesι m
      change q ≫ (j.ker.toModulesι ▷ C ≫ (λ_ C).hom) =
        A ◁ (j.ker.toModulesι ▷ B ≫ (λ_ B).hom) ≫ m at hq
      rw [hq, ← hd, ← whiskerLeft_comp_assoc]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    refine ⟨v.app U (tmulSection s y), ?_⟩
    have he := congrArg (fun φ ↦ φ.app U (tmulSection s y)) hv
    change (kernel.ι (tensorGradedUnit j C)).app U (v.app U (tmulSection s y)) =
      m.app U ((A ◁ kernel.ι (tensorGradedUnit j B)).app U (tmulSection s y)) at he
    rw [whiskerLeft_app_tmulSection] at he
    exact he

end
end AlgebraicGeometry.Scheme.Modules
