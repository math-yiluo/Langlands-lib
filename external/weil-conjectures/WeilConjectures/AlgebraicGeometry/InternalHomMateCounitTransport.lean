/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Invariance of evaluation mates under a change of pullback counit

Source: Stacks Project, cohomology.tex, Tags 08I3 and 08I4, evaluation-mate construction;
Tag 06YJ, uniqueness of derived functors with their counits.
(blueprint: lem-pc-internal-hom-mate-counit-transport).
-/

@[expose] public section

set_option autoImplicit false
universe uC uD vC vD
open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

/-- Simultaneously transporting the pullback adjunction and its tensor comparison
leaves the internal-Hom evaluation mate unchanged.
Source: Stacks Project, cohomology.tex, Tags 08I3, 08I4 and 06YJ.
(blueprint: lem-pc-internal-hom-mate-counit-transport).

Proof: the transported Hom equivalence precomposes with the comparison iso; its
inverse and its counit precompose with the inverse iso. Naturality of tensor-Hom
moves the inverse iso through evaluation. Expand the transported tensor comparison.
Its input inverse cancels the outer Hom-equivalence comparison. On the two output
factors, the comparison cancels the inverse from evaluation and from the counit,
respectively. Tensor composition and the iso identities leave the original mate.
This works for identity comparisons, zero objects, and arbitrary counit twists. -/
theorem internalHomMate_counit_transport
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (H : Cᵒᵖ × C ⥤ C) (F : D ⥤ C) (R : C ⥤ D) (p : F ⊣ R)
    (t : tensor D ⋙ F ≅ F.prod F ⋙ tensor C)
    (ex : ∀ A L M : C, (A ⟶ H.obj (op L, M)) ≃ (A ⊗ L ⟶ M))
    (hx : ∀ (A A' L M : C) (a : A' ⟶ A) (g : A ⟶ H.obj (op L, M)),
      ex A' L M (a ≫ g) = (a ⊗ₘ 𝟙 L) ≫ ex A L M g)
    (δ : F ≅ F) (L M : C) (A : D) (α : A ⟶ R.obj (H.obj (op L, M))) :
    let p' := p.ofNatIsoLeft δ
    let t' := Functor.isoWhiskerLeft (tensor D) δ.symm ≪≫ t ≪≫
      Functor.isoWhiskerRight (NatIso.prod δ δ) (tensor C)
    p'.homEquiv _ M (t'.hom.app (A, R.obj L) ≫
      (𝟙 _ ⊗ₘ p'.counit.app L) ≫ ex _ L M ((p'.homEquiv _ _).symm α)) =
    p.homEquiv _ M (t.hom.app (A, R.obj L) ≫
      (𝟙 _ ⊗ₘ p.counit.app L) ≫ ex _ L M ((p.homEquiv _ _).symm α)) := by
  dsimp only
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply,
    Adjunction.homEquiv_ofNatIsoLeft_symm_apply, hx]
  congr 1
  simp only [Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, NatIso.prod_hom, NatTrans.prod, Functor.prod_obj,
    tensor_obj, tensor_map, Adjunction.ofNatIsoLeft_counit]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp,
    Iso.hom_inv_id_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  simp

end AlgebraicGeometry
