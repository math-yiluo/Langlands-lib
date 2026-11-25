/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom

/-!
# Internal-Hom comparison for derived direct image

Source: Stacks Project, cohomology.tex, Remark remark-projection-formula-for-internal-hom
(blueprint: lem-pc-sheaf-rhom-projection-formula).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u w vC vD uC uD

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

section InternalHomMate
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [MonoidalCategory C] [MonoidalCategory D]
variable (H : Cᵒᵖ × C ⥤ C) (J : Dᵒᵖ × D ⥤ D)
  (F : D ⥤ C) (R : C ⥤ D) (p : F ⊣ R)
  (t : tensor D ⋙ F ⟶ F.prod F ⋙ tensor C)
  (ex : ∀ A L M : C, (A ⟶ H.obj (op L, M)) ≃ (A ⊗ L ⟶ M))
  (ey : ∀ A L M : D, (A ⟶ J.obj (op L, M)) ≃ (A ⊗ L ⟶ M))
  (hx : ∀ (A A' L L' M M' : C) (a : A' ⟶ A) (b : L' ⟶ L) (d : M ⟶ M')
    (g : A ⟶ H.obj (op L, M)),
    ex A' L' M' (a ≫ g ≫ H.map (b.op, d)) = (a ⊗ₘ b) ≫ ex A L M g ≫ d)
  (hy : ∀ (A A' L L' M M' : D) (a : A' ⟶ A) (b : L' ⟶ L) (d : M ⟶ M')
    (g : A ⟶ J.obj (op L, M)),
    ey A' L' M' (a ≫ g ≫ J.map (b.op, d)) = (a ⊗ₘ b) ≫ ey A L M g ≫ d)
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
include hx hy in
/-- Transpose evaluation with fixed natural tensor-Hom bijections.
The formula at the identity defines each component. Naturality in the test object
proves its mate equation. Applying the target equivalence to a naturality square,
then using the source equivalence's naturality, the tensor comparison's naturality,
and counit naturality proves that the components form a natural transformation.
Unlike the isomorphism-based helper in GlobalHomAdjunctionIso, this construction
requires only a natural tensor comparison, which need not be invertible.
Source: Stacks, Tag 08I3 (blueprint: lem-pc-sheaf-rhom-projection-formula). -/
private theorem internalHomMate_of_tensorComparison :
    ∃ c : H ⋙ R ⟶ R.op.prod R ⋙ J,
      ∀ (L M : C) (A : D) (α : A ⟶ R.obj (H.obj (op L, M))),
        ey A (R.obj L) (R.obj M) (α ≫ c.app (op L, M)) =
          p.homEquiv _ M (t.app (A, R.obj L) ≫
            (𝟙 _ ⊗ₘ p.counit.app L) ≫ ex _ L M ((p.homEquiv _ _).symm α)) := by
  let c (L M : C) : R.obj (H.obj (op L, M)) ⟶ J.obj (op (R.obj L), R.obj M) :=
    (ey _ _ _).symm (p.homEquiv _ M (t.app (_, R.obj L) ≫
      (𝟙 _ ⊗ₘ p.counit.app L) ≫ ex _ L M ((p.homEquiv _ _).symm (𝟙 _))))
  have mate (L M : C) (A : D) (α : A ⟶ R.obj (H.obj (op L, M))) :
      ey A (R.obj L) (R.obj M) (α ≫ c L M) =
        p.homEquiv _ M (t.app (A, R.obj L) ≫
          (𝟙 _ ⊗ₘ p.counit.app L) ≫ ex _ L M ((p.homEquiv _ _).symm α)) := by
    have h₁ := hy _ _ _ _ _ _ α (𝟙 (R.obj L)) (𝟙 (R.obj M)) (c L M)
    change ey _ _ _ (α ≫ c L M ≫ J.map (𝟙 _)) = _ at h₁
    simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h₁
    rw [h₁]
    dsimp only [c]
    rw [Equiv.apply_symm_apply, ← p.homEquiv_naturality_left]
    congr 1
    have h₂ := hx _ _ _ _ _ _ (F.map α) (𝟙 L) (𝟙 M)
      ((p.homEquiv _ _).symm (𝟙 (R.obj (H.obj (op L, M)))))
    change ex _ _ _ (F.map α ≫ _ ≫ H.map (𝟙 _)) = _ at h₂
    simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h₂
    have hp := p.homEquiv_naturality_left_symm α (𝟙 (R.obj (H.obj (op L, M))))
    simp only [Category.comp_id] at hp
    rw [hp]
    dsimp only [Functor.prod_obj] at *
    rw [h₂]
    have ht := t.naturality (X := (A, R.obj L))
      (Y := (R.obj (H.obj (op L, M)), R.obj L)) (α, 𝟙 (R.obj L))
    dsimp at ht
    simp only [CategoryTheory.Functor.map_id] at ht
    rw [← Category.assoc, ht]
    simp only [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Category.comp_id]
    congr 2
    simp
  refine ⟨{ app := fun Z ↦ c Z.1.unop Z.2, naturality := ?_ }, mate⟩
  intro Z Z' g
  obtain ⟨L, M⟩ := Z
  obtain ⟨L', M'⟩ := Z'
  obtain ⟨b, d⟩ := g
  dsimp
  apply (ey _ _ _).injective
  rw [mate]
  have hn := hy _ _ _ _ _ _ (𝟙 (R.obj (H.obj (L, M))))
    (R.map b.unop) (R.map d) (c L.unop M)
  simp only [Category.id_comp] at hn
  change ey _ _ _ (c L.unop M ≫ J.map ((R.map b.unop).op, R.map d)) = _ at hn
  rw [hn]
  dsimp only [c]
  rw [Equiv.apply_symm_apply]
  rw [← p.homEquiv_naturality_right, ← p.homEquiv_naturality_left]
  congr 1
  have he := hx _ _ _ _ _ _ (𝟙 (F.obj (R.obj (H.obj (L, M))))) b.unop d
    ((p.homEquiv _ _).symm (𝟙 (R.obj (H.obj (L, M)))))
  simp only [Category.id_comp] at he
  have hp := p.homEquiv_naturality_right_symm (𝟙 (R.obj (H.obj (L, M))))
    (H.map (b, d))
  simp only [Category.id_comp] at hp
  rw [hp]
  dsimp only [Functor.prod_obj] at *
  simp only [Quiver.Hom.op_unop] at he
  rw [he]
  have ht := t.naturality
    (X := (R.obj (H.obj (L, M)), R.obj L'.unop))
    (Y := (R.obj (H.obj (L, M)), R.obj L.unop))
    (𝟙 _, R.map b.unop)
  dsimp at ht
  simp only [CategoryTheory.Functor.map_id] at ht
  simp only [Category.assoc]
  rw [reassoc_of% ht]
  simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp]
  congr 2
  exact congrArg (fun z ↦ (𝟙 (F.obj (R.obj (H.obj (L, M))))) ⊗ₘ z)
    (p.counit_naturality b.unop).symm

end InternalHomMate

section TensorHomAdjunction
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  (H : Cᵒᵖ × C ⥤ C)
  (e : ∀ A L M : C, (A ⟶ H.obj (op L, M)) ≃ (A ⊗ L ⟶ M))
  (h : ∀ (A A' L L' M M' : C) (a : A' ⟶ A) (b : L' ⟶ L) (d : M ⟶ M')
    (g : A ⟶ H.obj (op L, M)),
    e A' L' M' (a ≫ g ≫ H.map (b.op, d)) = (a ⊗ₘ b) ≫ e A L M g ≫ d)
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Build the tensor-Hom adjunction from the pinned natural bijections.
Source: Stacks, Tag 08DJ (blueprint: lem-pc-sheaf-rhom-projection-formula). -/
private def tensorAdjunctionCore (L : C) :
    Adjunction.CoreHomEquiv (tensorRight L) ((Functor.curry.obj H).obj (op L)) where
  homEquiv A M := (e A L M).symm
  homEquiv_naturality_left_symm {A'} {A} {M} a g := by
    change e A' L M (a ≫ g) = (a ▷ L) ≫ e A L M g
    have h' := h _ _ _ _ _ _ a (𝟙 L) (𝟙 _) g
    change e _ _ _ (a ≫ g ≫ H.map (𝟙 _)) = _ at h'
    erw [H.map_id, Category.comp_id] at h'
    erw [Category.comp_id] at h'
    simpa only [tensorHom_id] using h'
  homEquiv_naturality_right g d := by
    apply (e _ _ _).injective
    erw [Equiv.apply_symm_apply]
    have h' := h _ _ _ _ _ _ (𝟙 _) (𝟙 L) d ((e _ _ _).symm g)
    simp only [Category.id_comp, id_tensorHom_id, Equiv.apply_symm_apply] at h'
    exact h'.symm

end TensorHomAdjunction



/-- The natural internal-Hom comparison for `Rf_*`, specified as the mate of evaluation.
The witnesses `a`, `bX`, `bY` and `t` exhibit the pullback/direct-image adjunction,
tensor/internal-Hom adjunctions and pullback/tensor comparison. The last equation
specifies the comparison, rather than merely asserting the existence of some arrow.

Source: Stacks Project, cohomology.tex, Remark remark-projection-formula-for-internal-hom
(blueprint: lem-pc-sheaf-rhom-projection-formula).

Proof:
1. Use lem-pc-ringed-spaces-derived-adjoint-general for the adjunction `a` and
   lem-sc-derived-internal-hom-adjunction for `bX` and `bY`. Evaluation is the counit
   of the latter adjunctions, equivalently the transpose of the identity of RHom.
2. For a test object `A` and `α : A ⟶ Rf_* RHom(L,M)`, transpose `α` by `a`, then
   by `bX`. Use lem-pc-derived-pullback-tensor-product to identify the pullback of
   `A ⊗ Rf_*L` with `Lf^*A ⊗ Lf^*Rf_*L`. Precompose with identity tensor the
   counit `Lf^*Rf_*L ⟶ L`. Transpose back by `a` and `bY`. Yoneda constructs the
   asserted comparison. This is the relative cup product followed by `Rf_*` of
   evaluation, exactly the construction in the source remark.
3. All operations are natural; hence the comparison is natural in both `L` and
   `M`. The displayed equation records its mate construction on every test map.
   No invertibility of the resulting comparison is asserted. -/
theorem exists_derivedDirectImage_internalHom_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∃ (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
      (bX : ∀ L : schemeDerivedCategory X, tensorRight L ⊣
        (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf)).obj
            (op L))
      (bY : ∀ L : schemeDerivedCategory Y, tensorRight L ⊣
        (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
            (op L))
      (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
        (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
      (c : derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf ⋙
          schemeDerivedDirectImage f ⟶
        (schemeDerivedDirectImage f).op.prod (schemeDerivedDirectImage f) ⋙
          derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf),
      ∀ (L M : schemeDerivedCategory X) (A : schemeDerivedCategory Y)
        (α : A ⟶ (schemeDerivedDirectImage f).obj
          ((derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf).obj
            (op L, M))),
        ((bY ((schemeDerivedDirectImage f).obj L)).homEquiv A
          ((schemeDerivedDirectImage f).obj M)).symm (α ≫ c.app (op L, M)) =
        a.homEquiv (A ⊗ (schemeDerivedDirectImage f).obj L) M
          (t.hom.app (A, (schemeDerivedDirectImage f).obj L) ≫
            (𝟙 ((derivedPullback f).obj A) ⊗ₘ a.counit.app L) ≫
            ((bX L).homEquiv ((derivedPullback f).obj A) M).symm
              ((a.homEquiv A
                ((derivedInternalHom (Opens.grothendieckTopology X)
                  X.toRingedSpace.sheaf).obj (op L, M))).symm α)) := by
  classical
  let HX := derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf
  let HY := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
  let ex : ∀ A L M : schemeDerivedCategory X,
      (A ⟶ HX.obj (op L, M)) ≃ (A ⊗ L ⟶ M) :=
    Classical.choose (exists_canonicalDerivedTensorHom.{u, w} X)
  let ey : ∀ A L M : schemeDerivedCategory Y,
      (A ⟶ HY.obj (op L, M)) ≃ (A ⊗ L ⟶ M) :=
    Classical.choose (exists_canonicalDerivedTensorHom.{u, w} Y)
  have hx := (Classical.choose_spec (exists_canonicalDerivedTensorHom.{u, w} X)).1
  have hy := (Classical.choose_spec (exists_canonicalDerivedTensorHom.{u, w} Y)).1
  let a : derivedPullback f ⊣ schemeDerivedDirectImage f :=
    Classical.choice (nonempty_derivedPullbackAdjunction.{u, w} f)
  let m : (derivedPullback f).CoreMonoidal :=
    Classical.choose (exists_derivedPullbackMonoidalModel.{u, w} f)
  let F := derivedPullback f
  let t : tensor (schemeDerivedCategory Y) ⋙ F ≅
      F.prod F ⋙ tensor (schemeDerivedCategory X) :=
    NatIso.ofComponents (fun Z ↦ (m.μIso Z.1 Z.2).symm) (by
      intro Z Z' g
      dsimp
      apply (cancel_epi (m.μIso Z.1 Z.2).hom).1
      apply (cancel_mono (m.μIso Z'.1 Z'.2).hom).1
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
      simp only [tensorHom_def, F.map_comp, Category.assoc]
      rw [← m.μIso_hom_natural_left_assoc, ← m.μIso_hom_natural_right])
  let bx := fun L ↦ Adjunction.mkOfHomEquiv (tensorAdjunctionCore HX ex hx L)
  let by' := fun L ↦ Adjunction.mkOfHomEquiv (tensorAdjunctionCore HY ey hy L)
  apply Exists.elim (@internalHomMate_of_tensorComparison (schemeDerivedCategory X)
    (schemeDerivedCategory Y) inferInstance inferInstance
    (schemeDerivedTensorMonoidal X) (schemeDerivedTensorMonoidal Y)
    HX HY F (schemeDerivedDirectImage f) a t.hom ex ey hx hy)
  intro c hc
  refine ⟨a, bx, by', t, c, ?_⟩
  intro L M A α
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  simpa only [bx, by', Adjunction.mkOfHomEquiv_homEquiv,
    tensorAdjunctionCore, Equiv.symm_symm, HX, HY, F, Functor.prod_obj,
    Functor.comp_obj, tensor_obj, tensorRight, curriedTensor, Functor.flip_obj_obj] using hc L M A α

end AlgebraicGeometry
