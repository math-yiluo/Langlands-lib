import Langlands.CategoryTheory.EquivariantDiagramFunctor
import Mathlib.CategoryTheory.Action.Limits

/-! # Preadditive varying-group equivariant diagrams -/

universe uG uI vI uC vC uE vE

namespace Langlands.EquivariantDiagram

open CategoryTheory

variable {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{uG}}
variable {C : Type uC} [Category.{vC} C]
variable {E : Type uE} [Category.{vE} E]

section Preadditive

variable [Preadditive C] {M N : EquivariantDiagram D C}

instance : Zero (M ⟶ N) where
  zero := ⟨0, by intro i g; simp⟩

instance : Add (M ⟶ N) where
  add f h := ⟨f.hom + h.hom, by intro i g; simp [f.comm, h.comm]⟩

instance : Neg (M ⟶ N) where
  neg f := ⟨-f.hom, by intro i g; simp [f.comm]⟩

instance : Sub (M ⟶ N) where
  sub f h := ⟨f.hom - h.hom, by intro i g; simp [f.comm, h.comm]⟩

instance : SMul ℕ (M ⟶ N) where
  smul n f := ⟨n • f.hom, by
    intro i g
    simp only [NatTrans.app_nsmul, Preadditive.comp_nsmul,
      Preadditive.nsmul_comp, f.comm]⟩

instance : SMul ℤ (M ⟶ N) where
  smul n f := ⟨n • f.hom, by
    intro i g
    simp only [NatTrans.app_zsmul, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp, f.comm]⟩

@[simp] theorem zero_hom : (0 : M ⟶ N).hom = 0 := rfl
@[simp] theorem add_hom (f h : M ⟶ N) : (f + h).hom = f.hom + h.hom := rfl
@[simp] theorem neg_hom (f : M ⟶ N) : (-f).hom = -f.hom := rfl
@[simp] theorem sub_hom (f h : M ⟶ N) : (f - h).hom = f.hom - h.hom := rfl
@[simp] theorem nsmul_hom (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl
@[simp] theorem zsmul_hom (n : ℤ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

omit [Preadditive C] in
theorem hom_injective : Function.Injective (fun f : M ⟶ N => f.hom) :=
  fun _ _ h => Hom.ext h

/-- Pointwise addition of equivariant natural transformations is bilinear under composition. -/
instance preadditive : Preadditive (EquivariantDiagram D C) where
  homGroup M N :=
    hom_injective.addCommGroup (M₂ := M.obj ⟶ N.obj) _ zero_hom add_hom neg_hom sub_hom
      (fun _ _ => rfl) (fun _ _ => rfl)
  add_comp _ _ _ f h k := by
    apply Hom.ext
    exact Preadditive.add_comp _ _ _ f.hom h.hom k.hom
  comp_add _ _ _ f h k := by
    apply Hom.ext
    exact Preadditive.comp_add _ _ _ f.hom h.hom k.hom

/-- Forgetting the actions preserves the pointwise Hom-group addition. -/
instance forget_additive : (forget (D := D) (C := C)).Additive where
  map_add := rfl

/-- Evaluation is additive with the existing preadditive structure on actions. -/
instance evaluation_additive (i : I) : (evaluation (D := D) (C := C) i).Additive where
  map_add := by
    intro M N f h
    apply Action.Hom.ext
    rfl

/-- The equivariant inclusion of Hom groups into natural transformations. -/
def homAddHom : (M ⟶ N) →+ (M.obj ⟶ N.obj) :=
  (forget (D := D) (C := C)).mapAddHom

@[simp] theorem homAddHom_apply (f : M ⟶ N) : homAddHom f = f.hom := rfl

/-- Finite sums are computed on the underlying natural transformations. -/
@[simp] theorem sum_hom {A : Type*} (s : Finset A) (f : A → (M ⟶ N)) :
    (∑ a ∈ s, f a).hom = ∑ a ∈ s, (f a).hom :=
  (forget (D := D) (C := C)).map_sum f s

variable [Preadditive E]

/-- Additive coefficient functors give additive functors on varying-group diagrams. -/
instance mapFunctor_additive (F : C ⥤ E) [F.Additive] :
    (mapFunctor (D := D) F).Additive where
  map_add := by
    intro M N f h
    apply Hom.ext
    apply NatTrans.ext
    funext i
    exact F.map_add

end Preadditive

section Postcomposition

variable [Preadditive E]

/-- Postcomposition is additive on natural transformations of coefficient functors. -/
instance postcompose_additive : (postcompose (D := D) (C := C) (E := E)).Additive where
  map_add := by
    intro F H α β
    apply NatTrans.ext
    funext M
    apply Hom.ext
    apply NatTrans.ext
    funext i
    rfl

end Postcomposition

end Langlands.EquivariantDiagram
