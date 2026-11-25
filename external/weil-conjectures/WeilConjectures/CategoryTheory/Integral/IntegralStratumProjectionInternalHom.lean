/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Tensor projection and internal Hom

Source: Stacks Project, Tags 0E8I and 08J9
(blueprint: lem-weil-pbc-projection-internal-hom).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c v d w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace CategoryTheory

private def fixedFirstTensorAdjunction
    {C : Type c} [Category.{v} C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (β : @SymmetricCategory C _ S.monoidal)
    (P : C) :
    (Prod.sectR P C ⋙ S.tensor) ⊣ (Functor.curry.obj H).obj (op P) := by
  let := S.monoidal
  let := β
  let e : MonoidalCategory.tensorRight P ≅ MonoidalCategory.tensorLeft P :=
    (BraidedCategory.tensorLeftIsoTensorRight P).symm
  let e' : MonoidalCategory.tensorLeft P ≅ Prod.sectR P C ⋙ S.tensor :=
    NatIso.ofComponents (fun N ↦ Iso.refl _) (by
      intro N N' f
      change P ◁ f ≫ 𝟙 _ = 𝟙 _ ≫ (𝟙 P ⊗ₘ f)
      simp only [Category.comp_id, Category.id_comp]
      exact (MonoidalCategory.id_tensorHom P f).symm)
  exact (S.adjunction P).ofNatIsoLeft (e ≪≫ e')

/-- A tensor projection formula identifies internal Hom from an extended source.
The two adjunctions allow distinct right adjoints, covering both open extension
and closed direct image.
Source: Stacks Project, Tags 0E8I and 08J9
(blueprint: lem-weil-pbc-projection-internal-hom).

Proof: fix P in the projection formula. The resulting left functor is F followed
by tensor with P followed by E. Its right adjoint is the right adjoint of E,
followed by internal Hom from P, followed by the right adjoint of F. Symmetry
identifies fixed-first tensor with fixed-second tensor, whose adjoint is the
specified internal Hom. The projection formula identifies that left functor
with tensor by E(P). Uniqueness of right adjoints gives the displayed natural
isomorphism, without any boundedness or geometric assumption. -/
theorem internalHom_of_tensorProjection
    {C : Type c} [Category.{v} C] {D : Type d} [Category.{w} D]
    {H : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure HD)
    (β : @SymmetricCategory C _ S.monoidal)
    (βD : @SymmetricCategory D _ T.monoidal)
    (E : D ⥤ C) (F : C ⥤ D) (ER : C ⥤ D) (FR : D ⥤ C)
    (a : E ⊣ ER) (b : F ⊣ FR)
    (φ : (𝟭 D).prod F ⋙ T.tensor ⋙ E ≅ E.prod (𝟭 C) ⋙ S.tensor)
    (P : D) :
    Nonempty ((Functor.curry.obj H).obj (op (E.obj P)) ≅
      ER ⋙ (Functor.curry.obj HD).obj (op P) ⋙ FR) := by
  let θ : F ⋙ (Prod.sectR P D ⋙ T.tensor) ⋙ E ≅
      Prod.sectR (E.obj P) C ⋙ S.tensor :=
    NatIso.ofComponents (fun N ↦ φ.app (P, N)) (by
      intro N N' f
      have h := φ.hom.naturality ((𝟙 P, f) : (P, N) ⟶ (P, N'))
      simpa only [Functor.comp_map, Functor.prod_map, Prod.sectR_map,
        Functor.id_map, Functor.map_id, Iso.app_hom] using h)
  let t := fixedFirstTensorAdjunction T βD P
  let s := fixedFirstTensorAdjunction S β (E.obj P)
  exact ⟨s.rightAdjointUniq (((b.comp t).comp a).ofNatIsoLeft θ)⟩

end CategoryTheory
