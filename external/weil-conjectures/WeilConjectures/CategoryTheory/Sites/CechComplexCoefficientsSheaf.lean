/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.CategoryTheory.Sites.CechComplexCoefficients
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The augmented Čech complex of a single morphism and the sheaf condition

Let `C` be a category, `V` an object of `C` such that `Over V` has finite products, `U₀` an
object of `Over V` and `P` a presheaf on `C` with values in a preadditive category `A`. The
augmentation `P(V) ⟶ P(U₀)` of the Čech complex `Č(U₀, P)` is a kernel of the first Čech
differential `P(U₀) ⟶ P(U₀ ×_V U₀)` if and only if `P` satisfies the sheaf condition for the
single morphism `U₀ ⟶ V` (with respect to all the functors `Hom(a, -)`).

For a short exact sequence `0 ⟶ P₁ ⟶ P₂ ⟶ P₃ ⟶ 0` of presheaves with values in an abelian
category, the Čech complexes also form a short exact sequence, and we deduce the usual
dimension shifting statements: if the augmentations of `P₁` and `P₂` are kernels and the Čech
complex of `P₁` is exact in degree `1`, then the augmentation of `P₃` is a kernel; and the
Čech complex of `P₃` is exact in degree `n` if those of `P₂` and `P₁` are exact in degrees `n`
and `n + 1`.

## Main statements

- `CategoryTheory.Presheaf.isLimit_overCechAugmentation_of_isSheafFor`: the augmentation of
  `Č(U₀, P)` is a kernel if `P` is a sheaf for the single morphism `U₀ ⟶ V`.
- `CategoryTheory.Presheaf.isSheafFor_singleton_of_isLimit_overCechAugmentation`: the converse.
- `CategoryTheory.Presheaf.isLimit_overCechAugmentation_X₃`: the augmentation of the cokernel
  of a short exact sequence of presheaves is a kernel.
- `CategoryTheory.Presheaf.exactAt_overCechComplex_X₃`: exactness of the Čech complex of the
  cokernel of a short exact sequence of presheaves.
-/

@[expose] public section

universe w v v' u'

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type w} [Category.{v} C] {V : C} [HasFiniteProducts (Over V)] (U₀ : Over V)

/-- The member `cechNerveObj (fun _ ↦ U₀) (fun _ : Fin 1 ↦ 0)` of the Čech nerve of `U₀` with
one factor is isomorphic to `U₀`. -/
@[simps]
noncomputable def cechNerveObjOneIso :
    cechNerveObj (fun _ : Fin 1 ↦ U₀) (fun _ : Fin 1 ↦ 0) ≅ U₀ where
  hom := Pi.π _ 0
  inv := Pi.lift fun _ ↦ 𝟙 U₀
  hom_inv_id := Pi.hom_ext _ _ fun l ↦ by
    obtain rfl := Subsingleton.elim (α := Fin 1) l 0
    rw [Category.assoc, Pi.lift_comp_π, Category.comp_id, Category.id_comp]
  inv_hom_id := Pi.lift_comp_π _ _

/-- The first face `U₀ ×_V U₀ ⟶ U₀` of the Čech nerve forgets the first factor. -/
@[reassoc (attr := simp)]
lemma cechNerveMap_succAbove_zero_cechNerveObjOneIso_hom :
    cechNerveMap (fun _ : Fin 1 ↦ U₀) (fun _ : Fin 2 ↦ 0) (0 : Fin 2).succAbove ≫
      (cechNerveObjOneIso U₀).hom = Pi.π _ 1 :=
  cechNerveMap_π _ _ _ 0

/-- The second face `U₀ ×_V U₀ ⟶ U₀` of the Čech nerve forgets the second factor. -/
@[reassoc (attr := simp)]
lemma cechNerveMap_succAbove_one_cechNerveObjOneIso_hom :
    cechNerveMap (fun _ : Fin 1 ↦ U₀) (fun _ : Fin 2 ↦ 0) (1 : Fin 2).succAbove ≫
      (cechNerveObjOneIso U₀).hom = Pi.π _ 0 :=
  cechNerveMap_π _ _ _ 0

/-- Two morphisms `p₁ p₂ : Z ⟶ U₀` over `V` factor through `U₀ ×_V U₀`, as the second and first
faces. -/
lemma exists_comp_cechNerveMap_succAbove {Z : C} (p₁ p₂ : Z ⟶ U₀.left)
    (hp : p₁ ≫ U₀.hom = p₂ ≫ U₀.hom) :
    ∃ g : Z ⟶ (cechNerveObj (fun _ : Fin 1 ↦ U₀) (fun _ : Fin 2 ↦ 0)).left,
      g ≫ (cechNerveMap (fun _ : Fin 1 ↦ U₀) (fun _ : Fin 2 ↦ 0) (1 : Fin 2).succAbove).left =
          p₁ ≫ (cechNerveObjOneIso U₀).inv.left ∧
        g ≫ (cechNerveMap (fun _ : Fin 1 ↦ U₀) (fun _ : Fin 2 ↦ 0) (0 : Fin 2).succAbove).left =
          p₂ ≫ (cechNerveObjOneIso U₀).inv.left := by
  let G : Over.mk (p₁ ≫ U₀.hom) ⟶ cechNerveObj (fun _ : Fin 1 ↦ U₀) (fun _ : Fin 2 ↦ 0) :=
    Pi.lift ![Over.homMk p₁, Over.homMk p₂ hp.symm]
  have h₁ : G ≫ cechNerveMap _ _ (1 : Fin 2).succAbove =
      Over.homMk p₁ ≫ (cechNerveObjOneIso U₀).inv := Pi.hom_ext _ _ fun l ↦ by
    obtain rfl := Subsingleton.elim (α := Fin 1) l 0
    rw [Category.assoc, cechNerveMap_π, Pi.lift_comp_π, Category.assoc, cechNerveObjOneIso_inv,
      Pi.lift_comp_π, Category.comp_id]
    rfl
  have h₂ : G ≫ cechNerveMap _ _ (0 : Fin 2).succAbove =
      Over.homMk p₂ hp.symm ≫ (cechNerveObjOneIso U₀).inv := Pi.hom_ext _ _ fun l ↦ by
    obtain rfl := Subsingleton.elim (α := Fin 1) l 0
    rw [Category.assoc, cechNerveMap_π, Pi.lift_comp_π, Category.assoc, cechNerveObjOneIso_inv,
      Pi.lift_comp_π, Category.comp_id]
    rfl
  exact ⟨G.left, congrArg CommaMorphism.left h₁, congrArg CommaMorphism.left h₂⟩

variable {A : Type u'} [Category.{v'} A]

/-- The isomorphism `P(U₀) ≅ P(cechNerveObj (fun _ ↦ U₀) (fun _ : Fin 1 ↦ 0))` induced by
`CategoryTheory.Presheaf.cechNerveObjOneIso`. -/
@[simps]
noncomputable def overCechObjZeroIso (P : Cᵒᵖ ⥤ A) :
    P.obj (op U₀.left) ≅ P.obj (op (cechNerveObj (fun _ : Fin 1 ↦ U₀) (fun _ : Fin 1 ↦ 0)).left)
    where
  hom := P.map (cechNerveObjOneIso U₀).hom.left.op
  inv := P.map (cechNerveObjOneIso U₀).inv.left.op
  hom_inv_id := by
    rw [← P.map_comp, ← op_comp, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, op_id, P.map_id]
  inv_hom_id := by
    rw [← P.map_comp, ← op_comp, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, op_id, P.map_id]

omit [HasFiniteProducts (Over V)] in
/-- The functor `Hom(a, P(-))` acts by postcomposition with the restrictions of `P`. -/
@[simp]
lemma comp_coyoneda_obj_map_apply (P : Cᵒᵖ ⥤ A) (a : A) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (y : a ⟶ P.obj X) : (P ⋙ coyoneda.obj (op a)).map f y = y ≫ P.map f :=
  rfl

section Preadditive

variable [Preadditive A] (P : Cᵒᵖ ⥤ A)

/-- The first Čech differential `P(U₀) ⟶ P(U₀ ×_V U₀)` is the difference of the restrictions
along the two faces. -/
lemma overCechComplex_obj_d_zero_one : ((overCechComplex U₀).obj P).d 0 1 =
    P.map (cechNerveMap (fun _ : Fin 1 ↦ U₀) (fun _ : Fin 2 ↦ 0) (0 : Fin 2).succAbove).left.op -
      P.map (cechNerveMap (fun _ : Fin 1 ↦ U₀) (fun _ : Fin 2 ↦ 0)
        (1 : Fin 2).succAbove).left.op := by
  rw [overCechComplex_obj_d, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

/-- The augmentation is the restriction along `U₀ ⟶ V`, followed by the isomorphism
`CategoryTheory.Presheaf.overCechObjZeroIso`. -/
lemma overCechAugmentation_eq :
    overCechAugmentation U₀ P = P.map U₀.hom.op ≫ (overCechObjZeroIso U₀ P).hom := by
  rw [overCechAugmentation, overCechObjZeroIso_hom, ← P.map_comp, ← op_comp, Over.w]

/-- The augmentation of the Čech complex is natural in the presheaf: for `φ : P ⟶ Q` the square
```
P(V) ──aug──▶ Č⁰(U₀, P)
  │φ_V           │φ
  ▼              ▼
Q(V) ──aug──▶ Č⁰(U₀, Q)
```
commutes. -/
@[reassoc]
lemma overCechAugmentation_naturality {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q) :
    overCechAugmentation U₀ P ≫ ((overCechComplex U₀).map φ).f 0 =
      φ.app (op V) ≫ overCechAugmentation U₀ Q := by
  rw [overCechComplex_map_f, overCechAugmentation, overCechAugmentation]
  exact φ.naturality _

/-- A morphism `y : a ⟶ P(V)` composes with the augmentation to `x` if and only if its
restriction along `U₀ ⟶ V` is `x`, transported along
`CategoryTheory.Presheaf.overCechObjZeroIso`. -/
lemma comp_overCechAugmentation_eq_iff {a : A} (y : a ⟶ P.obj (op V))
    (x : a ⟶ ((overCechComplex U₀).obj P).X 0) :
    y ≫ overCechAugmentation U₀ P = x ↔
      y ≫ P.map U₀.hom.op = x ≫ (overCechObjZeroIso U₀ P).inv := by
  rw [Iso.eq_comp_inv, Category.assoc, ← overCechAugmentation_eq]

/-- If `P` is a sheaf for the single morphism `U₀ ⟶ V`, then every morphism `a ⟶ P(U₀)` killed
by the first Čech differential factors uniquely through the augmentation. -/
lemma existsUnique_comp_overCechAugmentation
    (h : ∀ a : A, (Presieve.singleton U₀.hom).IsSheafFor (P ⋙ coyoneda.obj (op a))) {a : A}
    (x : a ⟶ ((overCechComplex U₀).obj P).X 0) (hx : x ≫ ((overCechComplex U₀).obj P).d 0 1 = 0) :
    ∃! y : a ⟶ P.obj (op V), y ≫ overCechAugmentation U₀ P = x := by
  rw [overCechComplex_obj_d_zero_one, Preadditive.comp_sub, sub_eq_zero] at hx
  obtain ⟨y, hy, hy'⟩ := Presieve.isSheafFor_singleton.1 (h a)
    (x ≫ (overCechObjZeroIso U₀ P).inv) fun p₁ p₂ hp ↦ by
      obtain ⟨g, h₁, h₂⟩ := exists_comp_cechNerveMap_succAbove U₀ p₁ p₂ hp
      simp only [comp_coyoneda_obj_map_apply, overCechObjZeroIso_inv, Category.assoc,
        ← P.map_comp, ← op_comp, ← h₁, ← h₂]
      rw [op_comp, op_comp, P.map_comp, P.map_comp, ← Category.assoc, ← Category.assoc, hx]
  exact ⟨y, (comp_overCechAugmentation_eq_iff U₀ P y x).2 hy,
    fun y' hy'' ↦ hy' y' ((comp_overCechAugmentation_eq_iff U₀ P y' x).1 hy'')⟩

/-- If `P` is a sheaf for the single morphism `U₀ ⟶ V` (with respect to all the functors
`Hom(a, -)`), then the augmentation `P(V) ⟶ P(U₀)` is a kernel of the first Čech differential.
-/
noncomputable def isLimitOverCechAugmentationOfIsSheafFor
    (h : ∀ a : A, (Presieve.singleton U₀.hom).IsSheafFor (P ⋙ coyoneda.obj (op a))) :
    IsLimit (KernelFork.ofι (overCechAugmentation U₀ P) (overCechAugmentation_d U₀ P)) :=
  KernelFork.IsLimit.ofι _ _
    (fun x hx ↦ (existsUnique_comp_overCechAugmentation U₀ P h x hx).exists.choose)
    (fun x hx ↦ (existsUnique_comp_overCechAugmentation U₀ P h x hx).exists.choose_spec)
    (fun x hx _ hm ↦ (existsUnique_comp_overCechAugmentation U₀ P h x hx).unique hm
      (existsUnique_comp_overCechAugmentation U₀ P h x hx).exists.choose_spec)

/-- If `P` is a sheaf for the single morphism `U₀ ⟶ V` (with respect to all the functors
`Hom(a, -)`), then the augmentation `P(V) ⟶ P(U₀)` is a kernel of the first Čech differential.
-/
lemma isLimit_overCechAugmentation_of_isSheafFor
    (h : ∀ a : A, (Presieve.singleton U₀.hom).IsSheafFor (P ⋙ coyoneda.obj (op a))) :
    Nonempty (IsLimit (KernelFork.ofι (overCechAugmentation U₀ P) (overCechAugmentation_d U₀ P))) :=
  ⟨isLimitOverCechAugmentationOfIsSheafFor U₀ P h⟩


/-- Conversely, if the augmentation `P(V) ⟶ P(U₀)` is a kernel of the first Čech differential,
then `P` is a sheaf for the single morphism `U₀ ⟶ V` with respect to all the functors
`Hom(a, -)`. -/
lemma isSheafFor_singleton_of_isLimit_overCechAugmentation
    (hc : IsLimit (KernelFork.ofι (overCechAugmentation U₀ P) (overCechAugmentation_d U₀ P)))
    (a : A) : (Presieve.singleton U₀.hom).IsSheafFor (P ⋙ coyoneda.obj (op a)) := by
  rw [Presieve.isSheafFor_singleton]
  intro t ht
  have ht' := ht (Pi.π (fun _ : Fin 2 ↦ U₀) 1).left (Pi.π (fun _ : Fin 2 ↦ U₀) 0).left
    (by rw [Over.w, Over.w])
  simp only [comp_coyoneda_obj_map_apply] at ht'
  have hx : (t ≫ (overCechObjZeroIso U₀ P).hom) ≫ ((overCechComplex U₀).obj P).d 0 1 = 0 := by
    rw [overCechComplex_obj_d_zero_one, Preadditive.comp_sub, sub_eq_zero, Category.assoc,
      Category.assoc, overCechObjZeroIso_hom,
      ← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, ← Over.comp_left, ← Over.comp_left,
      cechNerveMap_succAbove_zero_cechNerveObjOneIso_hom,
      cechNerveMap_succAbove_one_cechNerveObjOneIso_hom]
    exact ht'
  obtain ⟨y, hy⟩ := KernelFork.IsLimit.lift' hc _ hx
  have hy₀ : y ≫ P.map U₀.hom.op = t := by
    have := (comp_overCechAugmentation_eq_iff U₀ P y _).1 hy
    rwa [Category.assoc, Iso.hom_inv_id, Category.comp_id] at this
  refine ⟨y, hy₀, fun y' hy' ↦ Fork.IsLimit.hom_ext hc ?_⟩
  refine ((comp_overCechAugmentation_eq_iff U₀ P y' (t ≫ (overCechObjZeroIso U₀ P).hom)).2
    ?_).trans hy.symm
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact hy'

/-- The version of `isSheafFor_singleton_of_isLimit_overCechAugmentation` for a single
morphism `f : U ⟶ V`, with `U₀ = Over.mk f`. -/
lemma isSheafFor_singleton_of_isLimit_overCechAugmentation_mk {U : C} (f : U ⟶ V)
    (hc : IsLimit (KernelFork.ofι (overCechAugmentation (Over.mk f) P)
      (overCechAugmentation_d (Over.mk f) P))) (a : A) :
    (Presieve.singleton f).IsSheafFor (P ⋙ coyoneda.obj (op a)) :=
  isSheafFor_singleton_of_isLimit_overCechAugmentation (Over.mk f) P hc a

end Preadditive

/-! ### Short exact sequences of presheaves -/

section Abelian

variable [Abelian A] {S : ShortComplex (Cᵒᵖ ⥤ A)}

/-- For a short exact sequence of presheaves `0 ⟶ P₁ ⟶ P₂ ⟶ P₃ ⟶ 0` (objectwise), if the
augmentations of the Čech complexes of `P₁` and `P₂` are kernels and the Čech complex of `P₁` is
exact in degree `1`, then the augmentation of the Čech complex of `P₃` is a kernel. -/
noncomputable def isLimitOverCechAugmentationX₃
    (hS : ∀ X : Cᵒᵖ, (S.map ((evaluation Cᵒᵖ A).obj X)).ShortExact)
    (h₁ : IsLimit (KernelFork.ofι (overCechAugmentation U₀ S.X₁)
      (overCechAugmentation_d U₀ S.X₁)))
    (h₂ : IsLimit (KernelFork.ofι (overCechAugmentation U₀ S.X₂)
      (overCechAugmentation_d U₀ S.X₂)))
    (h₁' : ((overCechComplex U₀).obj S.X₁).ExactAt 1) :
    IsLimit (KernelFork.ofι (overCechAugmentation U₀ S.X₃)
      (overCechAugmentation_d U₀ S.X₃)) := by
  have hm (k : ℕ) : Mono (((overCechComplex U₀).map S.f).f k) := (hS _).mono_f
  have hfg (k : ℕ) :
      ((overCechComplex U₀).map S.f).f k ≫ ((overCechComplex U₀).map S.g).f k = 0 :=
    (S.map ((evaluation Cᵒᵖ A).obj _)).zero
  have hfgV : S.f.app (op V) ≫ S.g.app (op V) = 0 := (S.map ((evaluation Cᵒᵖ A).obj _)).zero
  have hex (k : ℕ) {T : A} (x : T ⟶ ((overCechComplex U₀).obj S.X₂).X k)
      (hx : x ≫ ((overCechComplex U₀).map S.g).f k = 0) :
      ∃ (T' : A) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ ((overCechComplex U₀).obj S.X₁).X k),
        π ≫ x = y ≫ ((overCechComplex U₀).map S.f).f k :=
    (hS (op (cechNerveObj (fun _ : Fin 1 ↦ U₀)
      (fun _ : Fin (k + 1) ↦ 0)).left)).exact.exact_up_to_refinements x hx
  have hsurj (k : ℕ) {T : A} (z : T ⟶ ((overCechComplex U₀).obj S.X₃).X k) :
      ∃ (T' : A) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ ((overCechComplex U₀).obj S.X₂).X k),
        π ≫ z = y ≫ ((overCechComplex U₀).map S.g).f k :=
    have : Epi (((overCechComplex U₀).map S.g).f k) := (hS _).epi_g
    surjective_up_to_refinements_of_epi (((overCechComplex U₀).map S.g).f k) z
  have hsurjV {T : A} (z : T ⟶ S.X₃.obj (op V)) :
      ∃ (T' : A) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ S.X₂.obj (op V)),
        π ≫ z = y ≫ S.g.app (op V) :=
    have : Epi (S.g.app (op V)) := (hS (op V)).epi_g
    surjective_up_to_refinements_of_epi (S.g.app (op V)) z
  have hK₁ {T : A} (x : T ⟶ ((overCechComplex U₀).obj S.X₁).X 1)
      (hx : x ≫ ((overCechComplex U₀).obj S.X₁).d 1 2 = 0) :
      ∃ (T' : A) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ ((overCechComplex U₀).obj S.X₁).X 0),
        π ≫ x = y ≫ ((overCechComplex U₀).obj S.X₁).d 0 1 :=
    ((HomologicalComplex.exactAt_iff' ((overCechComplex U₀).obj S.X₁) 0 1 2 (by simp)
      (by simp)).1 h₁').exact_up_to_refinements x hx
  have hnf : overCechAugmentation U₀ S.X₁ ≫ ((overCechComplex U₀).map S.f).f 0 =
      S.f.app (op V) ≫ overCechAugmentation U₀ S.X₂ := overCechAugmentation_naturality U₀ S.f
  have hng : overCechAugmentation U₀ S.X₂ ≫ ((overCechComplex U₀).map S.g).f 0 =
      S.g.app (op V) ≫ overCechAugmentation U₀ S.X₃ := overCechAugmentation_naturality U₀ S.g
  have hmono₂ : Mono (overCechAugmentation U₀ S.X₂) := Fork.IsLimit.mono h₂
  -- the augmentation of `P₃` is a monomorphism
  have hmono₃ : Mono (overCechAugmentation U₀ S.X₃) := by
    refine Preadditive.mono_of_cancel_zero _ fun {T} y₃ hy₃ ↦ ?_
    obtain ⟨T₁, π₁, _, y₂, hy₂⟩ := hsurjV y₃
    obtain ⟨T₂, π₂, _, x₁, hx₁⟩ := hex 0 (y₂ ≫ overCechAugmentation U₀ S.X₂) (by
      rw [Category.assoc, hng, ← Category.assoc, ← hy₂, Category.assoc, hy₃, Limits.comp_zero])
    obtain ⟨y₁, hy₁⟩ := KernelFork.IsLimit.lift' h₁ x₁ (by
      rw [← cancel_mono (((overCechComplex U₀).map S.f).f 1), Category.assoc,
        ← ((overCechComplex U₀).map S.f).comm 0 1, ← Category.assoc, ← hx₁, Category.assoc,
        Category.assoc, overCechAugmentation_d, Limits.comp_zero, Limits.comp_zero,
        Limits.zero_comp])
    have hy₁' : y₁ ≫ overCechAugmentation U₀ S.X₁ = x₁ := hy₁
    have h : π₂ ≫ y₂ = y₁ ≫ S.f.app (op V) := by
      rw [← cancel_mono (overCechAugmentation U₀ S.X₂), Category.assoc, hx₁, Category.assoc,
        ← hnf, ← Category.assoc, hy₁']
    rw [← cancel_epi (π₂ ≫ π₁), Limits.comp_zero, Category.assoc, hy₂, ← Category.assoc, h,
      Category.assoc, hfgV, Limits.comp_zero]
  -- exactness at `P₃(U₀)`
  refine ShortComplex.Exact.fIsKernel (S := ShortComplex.mk _ _ (overCechAugmentation_d U₀ S.X₃))
    ?_
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x₃ hx₃
  have hx₃' : x₃ ≫ ((overCechComplex U₀).obj S.X₃).d 0 1 = 0 := hx₃
  obtain ⟨T₁, π₁, _, x₂, hx₂⟩ := hsurj 0 x₃
  obtain ⟨T₂, π₂, _, x₁', hx₁'⟩ := hex 1 (x₂ ≫ ((overCechComplex U₀).obj S.X₂).d 0 1) (by
    rw [Category.assoc, ← ((overCechComplex U₀).map S.g).comm 0 1, ← Category.assoc, ← hx₂,
      Category.assoc, hx₃', Limits.comp_zero])
  obtain ⟨T₃, π₃, _, x₁, hx₁⟩ := hK₁ x₁' (by
    rw [← cancel_mono (((overCechComplex U₀).map S.f).f 2), Category.assoc,
      ← ((overCechComplex U₀).map S.f).comm 1 2, ← Category.assoc, ← hx₁', Category.assoc,
      Category.assoc, HomologicalComplex.d_comp_d, Limits.comp_zero, Limits.comp_zero,
      Limits.zero_comp])
  obtain ⟨y₂, hy₂⟩ := KernelFork.IsLimit.lift' h₂
    (π₃ ≫ π₂ ≫ x₂ - x₁ ≫ ((overCechComplex U₀).map S.f).f 0) (by
      rw [Preadditive.sub_comp, Category.assoc, Category.assoc, hx₁', ← Category.assoc, hx₁,
        Category.assoc, Category.assoc, ((overCechComplex U₀).map S.f).comm, sub_self])
  have hy₂' : y₂ ≫ overCechAugmentation U₀ S.X₂ =
      π₃ ≫ π₂ ≫ x₂ - x₁ ≫ ((overCechComplex U₀).map S.f).f 0 := hy₂
  refine ⟨T₃, π₃ ≫ π₂ ≫ π₁, inferInstance, y₂ ≫ S.g.app (op V), ?_⟩
  have : (y₂ ≫ S.g.app (op V)) ≫ overCechAugmentation U₀ S.X₃ = (π₃ ≫ π₂ ≫ π₁) ≫ x₃ := by
    rw [Category.assoc, ← hng, ← Category.assoc, hy₂', Preadditive.sub_comp, Category.assoc x₁,
      hfg, Limits.comp_zero, sub_zero]
    simp only [Category.assoc]
    rw [hx₂]
  exact this.symm

/-- The Čech complexes of a short exact sequence of presheaves (objectwise) form a short exact
sequence of complexes. -/
lemma shortExact_mapShortComplex_overCechComplex
    (hS : ∀ X : Cᵒᵖ, (S.map ((evaluation Cᵒᵖ A).obj X)).ShortExact) :
    ((overCechComplex U₀).mapShortComplex.obj S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact
    ((overCechComplex U₀).mapShortComplex.obj S) fun k ↦
    hS (op (cechNerveObj (fun _ : Fin 1 ↦ U₀) (fun _ : Fin (k + 1) ↦ 0)).left)

/-- For a short exact sequence of presheaves `0 ⟶ P₁ ⟶ P₂ ⟶ P₃ ⟶ 0` (objectwise), the Čech
complex of `P₃` is exact in degree `n` if the Čech complexes of `P₂` and `P₁` are exact in
degrees `n` and `n + 1`. -/
lemma exactAt_overCechComplex_X₃
    (hS : ∀ X : Cᵒᵖ, (S.map ((evaluation Cᵒᵖ A).obj X)).ShortExact) (n : ℕ)
    (h₂ : ((overCechComplex U₀).obj S.X₂).ExactAt n)
    (h₁ : ((overCechComplex U₀).obj S.X₁).ExactAt (n + 1)) :
    ((overCechComplex U₀).obj S.X₃).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h₁ h₂ ⊢
  exact ((shortExact_mapShortComplex_overCechComplex U₀ hS).homology_exact₃ n (n + 1)
    rfl).isZero_X₂_iff.2 ⟨h₂.eq_of_src _ _, h₁.eq_of_tgt _ _⟩

end Abelian

end CategoryTheory.Presheaf

namespace CategoryTheory.Sheaf

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C} {A : Type u'}
  [Category.{v'} A] [Preadditive A] {V : C} [HasFiniteProducts (Over V)]

/-- For a sheaf `G` and an object `U₀` over `V` whose structure morphism generates a covering
sieve, the augmentation `G(V) ⟶ G(U₀)` is a kernel of the first Čech differential. -/
noncomputable def isLimitOverCechAugmentation (G : Sheaf J A) (U₀ : Over V)
    (hU₀ : Sieve.generate (Presieve.singleton U₀.hom) ∈ J V) :
    IsLimit (KernelFork.ofι (Presheaf.overCechAugmentation U₀ G.obj)
      (Presheaf.overCechAugmentation_d U₀ G.obj)) :=
  Presheaf.isLimitOverCechAugmentationOfIsSheafFor U₀ G.obj fun a ↦
    (Presieve.isSheafFor_iff_generate _).2 (G.property a _ hU₀)

end CategoryTheory.Sheaf
