import Langlands.AlgebraicGeometry.ModuleDual
import Langlands.AlgebraicGeometry.Modules.PullbackTensor
import Langlands.AlgebraicGeometry.Modules.TensorMonoidalComparisonProofs

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

noncomputable section

namespace Langlands.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The sectionwise evaluation `Hom(M, N) ⊗ M → N` of presheaves of modules, sending
`f ⊗ m` to `internalHomEval M N U f m` on each open `U`. -/
def internalHomTensorEvalPresheaf (M N : X.Modules) :
    (internalHom M N).val ⊗ M.val ⟶ N.val where
  app U := ModuleCat.ofHom (TensorProduct.lift (internalHomEval M N U.unop))
  naturality := by
    intro U V i
    refine ModuleCat.MonoidalCategory.tensor_ext (fun f m => ?_)
    exact internalHomEval_restrict M N i.unop f m

@[simp]
lemma internalHomTensorEvalPresheaf_app_tmul (M N : X.Modules) (U : X.Opens)
    (f : Γ(internalHom M N, U)) (m : Γ(M, U)) :
    ((internalHomTensorEvalPresheaf M N).app (op U)).hom (f ⊗ₜ m) =
      internalHomEval M N U f m :=
  rfl

/-- The tensor evaluation `tensorObj (internalHom M N) M → N` of module sheaves: the sheaf map
corresponding under `tensorHomEquiv` to the sectionwise evaluation. -/
def internalHomTensorEval (M N : X.Modules) : tensorObj (internalHom M N) M ⟶ N :=
  (tensorHomEquiv _ _ _).symm (internalHomTensorEvalPresheaf M N)

lemma tensorHomEquiv_internalHomTensorEval (M N : X.Modules) :
    tensorHomEquiv _ _ _ (internalHomTensorEval M N) = internalHomTensorEvalPresheaf M N :=
  (tensorHomEquiv _ _ _).apply_symm_apply _

/-- The sectionwise tensor adjoint of `internalHomTensorEval` sends `f ⊗ m` to `f(m)`. -/
@[simp]
lemma tensorHomEquiv_internalHomTensorEval_app_tmul (M N : X.Modules) (U : X.Opens)
    (f : Γ(internalHom M N, U)) (m : Γ(M, U)) :
    ((tensorHomEquiv _ _ _ (internalHomTensorEval M N)).app (op U)).hom (f ⊗ₜ m) =
      internalHomEval M N U f m := by
  rw [tensorHomEquiv_internalHomTensorEval]
  rfl

/-- `tensorHomEquiv` is precomposition of the underlying presheaf map with the sheafification
unit of the sectionwise tensor. -/
lemma tensorHomEquiv_eq_tensorSheafifyUnit_comp {M N P : X.Modules} (g : tensorObj M N ⟶ P) :
    tensorHomEquiv M N P g = tensorSheafifyUnit M N ≫ g.val :=
  (sheafifyAdjunction X).homEquiv_unit _ _ _

/-- On the image of `f ⊗ m` in the sheaf tensor, the evaluation is `f(m)`. -/
lemma internalHomTensorEval_app_tensorSheafifyUnit (M N : X.Modules) (U : X.Opens)
    (f : Γ(internalHom M N, U)) (m : Γ(M, U)) :
    ((internalHomTensorEval M N).val.app (op U)).hom
        (((tensorSheafifyUnit (internalHom M N) M).app (op U)).hom (f ⊗ₜ m)) =
      internalHomEval M N U f m := by
  rw [← tensorHomEquiv_internalHomTensorEval_app_tmul,
    tensorHomEquiv_eq_tensorSheafifyUnit_comp]
  rfl

/-- `internalHomTensorEval` is the unique sheaf map whose sectionwise tensor adjoint sends
`f ⊗ m` to `f(m)`. -/
lemma eq_internalHomTensorEval_iff (M N : X.Modules) (g : tensorObj (internalHom M N) M ⟶ N) :
    g = internalHomTensorEval M N ↔
      ∀ (U : X.Opens) (f : Γ(internalHom M N, U)) (m : Γ(M, U)),
        ((tensorHomEquiv _ _ _ g).app (op U)).hom (f ⊗ₜ m) = internalHomEval M N U f m := by
  constructor
  · rintro rfl
    exact tensorHomEquiv_internalHomTensorEval_app_tmul M N
  · intro h
    apply (tensorHomEquiv _ _ _).injective
    rw [tensorHomEquiv_internalHomTensorEval]
    refine PresheafOfModules.hom_ext (fun U => ModuleCat.MonoidalCategory.tensor_ext
      (fun f m => ?_))
    exact h U.unop f m

/-- The evaluation `tensorObj M (dual M) → 𝒪_X`, `m ⊗ φ ↦ φ(m)`, obtained from
`internalHomTensorEval` by first swapping the tensor factors. -/
def dualTensorEval (M : X.Modules) : tensorObj M (dual M) ⟶ structureSheaf X :=
  (tensorComm M (dual M)).hom ≫ internalHomTensorEval M (Langlands.SchemeModule.structureModule X)

/-- The sectionwise tensor adjoint of `dualTensorEval` is the braiding followed by the
sectionwise evaluation. -/
lemma tensorHomEquiv_dualTensorEval (M : X.Modules) :
    tensorHomEquiv _ _ _ (dualTensorEval M) =
      (β_ M.val (dual M).val).hom ≫
        internalHomTensorEvalPresheaf M (Langlands.SchemeModule.structureModule X) := by
  rw [← tensorHomEquiv_internalHomTensorEval]
  exact (sheafifyAdjunction X).homEquiv_naturality_left _ _

/-- The sectionwise tensor adjoint of `dualTensorEval` sends `m ⊗ φ` to `φ(m)`. -/
@[simp]
lemma tensorHomEquiv_dualTensorEval_app_tmul (M : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) (φ : Γ(dual M, U)) :
    ((tensorHomEquiv _ _ _ (dualTensorEval M)).app (op U)).hom (m ⊗ₜ φ) = dualEval M U φ m := by
  rw [tensorHomEquiv_dualTensorEval]
  rfl

/-- On the image of `m ⊗ φ` in the sheaf tensor, the dual evaluation is `φ(m)`. -/
lemma dualTensorEval_app_tensorSheafifyUnit (M : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) (φ : Γ(dual M, U)) :
    ((dualTensorEval M).val.app (op U)).hom
        (((tensorSheafifyUnit M (dual M)).app (op U)).hom (m ⊗ₜ φ)) =
      dualEval M U φ m := by
  rw [← tensorHomEquiv_dualTensorEval_app_tmul, tensorHomEquiv_eq_tensorSheafifyUnit_comp]
  rfl

/-- `dualTensorEval` is the unique sheaf map whose sectionwise tensor adjoint sends `m ⊗ φ`
to `φ(m)`. -/
lemma eq_dualTensorEval_iff (M : X.Modules) (g : tensorObj M (dual M) ⟶ structureSheaf X) :
    g = dualTensorEval M ↔
      ∀ (U : X.Opens) (m : Γ(M, U)) (φ : Γ(dual M, U)),
        ((tensorHomEquiv _ _ _ g).app (op U)).hom (m ⊗ₜ φ) = dualEval M U φ m := by
  constructor
  · rintro rfl
    exact tensorHomEquiv_dualTensorEval_app_tmul M
  · intro h
    apply (tensorHomEquiv _ _ _).injective
    refine PresheafOfModules.hom_ext (fun U => ModuleCat.MonoidalCategory.tensor_ext
      (fun m φ => ?_))
    exact (h U.unop m φ).trans (tensorHomEquiv_dualTensorEval_app_tmul M U.unop m φ).symm

/-- The internal-Hom evaluation for the monoidal structure on `X.Modules`, obtained by
composing `internalHomTensorEval` with the comparison `localizedTensorIso`. -/
def internalHomMonoidalEval (M N : X.Modules) : internalHom M N ⊗ M ⟶ N :=
  (localizedTensorIso X (internalHom M N) M).hom ≫ internalHomTensorEval M N

/-- The dual evaluation `M ⊗ dual M → 𝟙_ X.Modules` for the monoidal structure on `X.Modules`,
obtained by composing `dualTensorEval` with the comparison `localizedTensorIso`. -/
def dualMonoidalEval (M : X.Modules) : M ⊗ dual M ⟶ 𝟙_ X.Modules :=
  (localizedTensorIso X M (dual M)).hom ≫ dualTensorEval M

/-- Through `localizedTensorIso`, the monoidal internal-Hom evaluation is the explicit one. -/
lemma localizedTensorIso_inv_internalHomMonoidalEval (M N : X.Modules) :
    (localizedTensorIso X (internalHom M N) M).inv ≫ internalHomMonoidalEval M N =
      internalHomTensorEval M N :=
  Iso.inv_hom_id_assoc _ _

/-- Through `localizedTensorIso`, the monoidal dual evaluation is the explicit one. -/
lemma localizedTensorIso_inv_dualMonoidalEval (M : X.Modules) :
    (localizedTensorIso X M (dual M)).inv ≫ dualMonoidalEval M = dualTensorEval M :=
  Iso.inv_hom_id_assoc _ _

/-- The monoidal dual evaluation is the braiding followed by the monoidal internal-Hom
evaluation with values in the structure sheaf. -/
lemma dualMonoidalEval_eq_braiding_comp (M : X.Modules) :
    dualMonoidalEval M =
      (β_ M (dual M)).hom ≫
        internalHomMonoidalEval M (Langlands.SchemeModule.structureModule X) := by
  rw [dualMonoidalEval, dualTensorEval, internalHomMonoidalEval, ← Category.assoc,
    tensorMonoidalSymmetryComparison X M (dual M), Category.assoc]
  rfl

end Langlands.Scheme.Modules
