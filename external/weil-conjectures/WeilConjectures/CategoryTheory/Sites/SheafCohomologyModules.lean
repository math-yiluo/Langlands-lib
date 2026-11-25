/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyTorsion
public import WeilConjectures.Mathlib.Data.ZMod.Basic

/-!
# Injective sheaves of modules over a finite ring are acyclic

Let `Λ` be a finite ring and `I` an injective sheaf of `Λ`-modules on a site. Then the underlying
abelian sheaf of `I` has no cohomology in positive degrees
(`CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective`). This allows to compare the
cohomology of sheaves of `Λ`-modules with abelian sheaf cohomology.

The proof goes through coinduction `A ↦ Hom_ℤ(Λ, A)`, which is right adjoint to forgetting the
`Λ`-module structure. Embedding the underlying abelian sheaf of `I` into an injective abelian
sheaf `A`, the sheaf `I` is a retract of the coinduced sheaf of `A`. Decomposing `Λ` as a finite
direct sum of cyclic groups `ZMod q`, the underlying abelian sheaf of the coinduced sheaf of `A`
is a finite sum of retracts of the `q`-torsion subsheaves of `A`
(`CategoryTheory.Sheaf.subsingleton_H_forget₂_coinduce_of_injective`), which are acyclic by
`CategoryTheory.Sheaf.subsingleton_H_kernel_nsmul_of_injective`.

## Main statements

- `CategoryTheory.Sheaf.H.subsingleton_of_sum_comp_eq_id`: an abelian sheaf whose identity is a
  finite sum of morphisms factoring through sheaves without cohomology in degree `n` has no
  cohomology in degree `n`.
- `CategoryTheory.Sheaf.subsingleton_H_forget₂_coinduce_of_injective`: for a finite ring `Λ` and
  an injective abelian sheaf `A`, the coinduced sheaf `Hom_ℤ(Λ, A)` is acyclic.
- `CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective`: injective sheaves of modules over a
  finite ring are acyclic.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

open Abelian Limits Opposite

namespace Sheaf

/-- A finite sum of morphisms of abelian sheaves is computed sectionwise. -/
lemma Hom.sum_hom_app_apply {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : Sheaf J AddCommGrpCat.{w}} {ι : Type*} (s : Finset ι) (f : ι → (F ⟶ G)) (U : Cᵒᵖ)
    (x : F.obj.obj U) : (∑ i ∈ s, f i).hom.app U x = ∑ i ∈ s, (f i).hom.app U x := by
  let ev : (F ⟶ G) →+ (F.obj.obj U →+ G.obj.obj U) :=
    { toFun f := (f.hom.app U).hom
      map_zero' := rfl
      map_add' _ _ := rfl }
  exact (DFunLike.congr_fun (map_sum ev f s) x).trans (AddMonoidHom.finsetSum_apply _ _ _)

/-- An abelian sheaf `F` has no cohomology in degree `n` as soon as its identity is a finite sum
of morphisms factoring through sheaves without cohomology in degree `n`. -/
lemma H.subsingleton_of_sum_comp_eq_id {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] {ι : Type*} [Fintype ι]
    {F : Sheaf J AddCommGrpCat.{w}} {G : ι → Sheaf J AddCommGrpCat.{w}} (φ : ∀ i, F ⟶ G i)
    (ψ : ∀ i, G i ⟶ F) (h : ∑ i, φ i ≫ ψ i = 𝟙 F) (n : ℕ) [∀ i, Subsingleton (H (G i) n)] :
    Subsingleton (H F n) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  rw [← H.map_id_apply x, ← h]
  refine (map_sum (AddMonoidHom.mk' (fun f ↦ H.map f n x) fun f g ↦ H.map_add_apply f g x) _
    _).trans (Finset.sum_eq_zero fun i _ ↦ ?_)
  rw [AddMonoidHom.mk'_apply, H.map_comp_apply, Subsingleton.elim (H.map (φ i) n x) 0, map_zero]

section Coinduce

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Λ : Type w) [Ring Λ]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- Evaluation at `x : Λ`, from the underlying abelian sheaf of the coinduced sheaf
`Hom_ℤ(Λ, A)` to `A`. -/
noncomputable def forget₂CoinduceEval (A : Sheaf J AddCommGrpCat.{w}) (x : Λ) :
    (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj
      ((sheafCompose J (ModuleCat.coinduce Λ)).obj A) ⟶ A where
  hom :=
    { app U := AddCommGrpCat.ofHom ((AddMonoidHom.eval x).comp
        (ModuleCat.coinduceObjAddEquiv Λ (A.obj.obj U)).toAddMonoidHom)
      naturality U V g := by
        ext f
        exact ModuleCat.coinduceObjAddEquiv_map_apply Λ (A.obj.map g) f x }

@[simp]
lemma forget₂CoinduceEval_hom_app_apply (A : Sheaf J AddCommGrpCat.{w}) (x : Λ) (U : Cᵒᵖ)
    (f : ((sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj
      ((sheafCompose J (ModuleCat.coinduce Λ)).obj A)).obj.obj U) :
    (forget₂CoinduceEval Λ A x).hom.app U f =
      ModuleCat.coinduceObjAddEquiv Λ (A.obj.obj U) f x :=
  rfl

/-- Evaluation at an element `x` with `q • x = 0` is killed by multiplication by `q`. -/
lemma forget₂CoinduceEval_comp_nsmul (A : Sheaf J AddCommGrpCat.{w}) {x : Λ} {q : ℕ}
    (hx : q • x = 0) : forget₂CoinduceEval Λ A x ≫ (q • 𝟙 A) = 0 := by
  ext U f
  refine (map_nsmul (ModuleCat.coinduceObjAddEquiv Λ (A.obj.obj U) f) q x).symm.trans ?_
  rw [hx, map_zero]
  rfl

/-- The sections of the `q`-torsion subsheaf of an abelian sheaf are killed by `q`. -/
lemma nsmul_kernel_ι_hom_app (A : Sheaf J AddCommGrpCat.{w}) (q : ℕ) (U : Cᵒᵖ)
    (s : (kernel (q • 𝟙 A)).obj.obj U) : q • (kernel.ι (q • 𝟙 A)).hom.app U s = 0 :=
  congr($(kernel.condition (q • 𝟙 A)).hom.app U s)

/-- The morphism from the `q`-torsion subsheaf of `A` to the underlying abelian sheaf of the
coinduced sheaf `Hom_ℤ(Λ, A)` induced by an additive map `c : Λ →+ ZMod q`: a section `s` is
sent to `r ↦ (c r).val • s`. -/
noncomputable def kernelNsmulToForget₂Coinduce (A : Sheaf J AddCommGrpCat.{w}) {q : ℕ}
    [NeZero q] (c : Λ →+ ZMod q) :
    kernel (q • 𝟙 A) ⟶ (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj
      ((sheafCompose J (ModuleCat.coinduce Λ)).obj A) where
  hom :=
    { app U := AddCommGrpCat.ofHom
        ((ModuleCat.coinduceObjAddEquiv Λ (A.obj.obj U)).symm.toAddMonoidHom.comp
          (((kernel.ι (q • 𝟙 A)).hom.app U).hom.zmodValNsmul (nsmul_kernel_ι_hom_app A q U) c))
      naturality U V g := by
        ext s
        refine (ModuleCat.coinduceObjAddEquiv Λ (A.obj.obj V)).injective
          (AddMonoidHom.ext fun r ↦ ?_)
        refine Eq.trans ?_ (ModuleCat.coinduceObjAddEquiv_map_apply Λ (A.obj.map g) _ r).symm
        exact (congrArg ((c r).val • ·)
          (NatTrans.naturality_apply (kernel.ι (q • 𝟙 A)).hom g s)).trans
            (map_nsmul (A.obj.map g).hom _ _).symm }

@[simp]
lemma coinduceObjAddEquiv_kernelNsmulToForget₂Coinduce_hom_app_apply
    (A : Sheaf J AddCommGrpCat.{w}) {q : ℕ} [NeZero q] (c : Λ →+ ZMod q) (U : Cᵒᵖ)
    (s : (kernel (q • 𝟙 A)).obj.obj U) (r : Λ) :
    ModuleCat.coinduceObjAddEquiv Λ (A.obj.obj U)
      ((kernelNsmulToForget₂Coinduce Λ A c).hom.app U s) r =
        (c r).val • (kernel.ι (q • 𝟙 A)).hom.app U s :=
  rfl

end Coinduce

section Acyclic

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max w v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{max w v})]

/-- For a finite ring `Λ` and an injective abelian sheaf `A`, the underlying abelian sheaf of
the coinduced sheaf `Hom_ℤ(Λ, A)` has no cohomology in positive degrees: decomposing `Λ` as a
finite direct sum of cyclic groups `ZMod q`, it is a finite sum of retracts of the `q`-torsion
subsheaves of `A`, which are acyclic. -/
theorem subsingleton_H_forget₂_coinduce_of_injective (Λ : Type (max w v)) [Ring Λ] [Finite Λ]
    [J.HasSheafCompose (forget₂ (ModuleCat.{max w v} Λ) AddCommGrpCat.{max w v})]
    (A : Sheaf J AddCommGrpCat.{max w v}) [Injective A] (n : ℕ) :
    Subsingleton (H ((sheafCompose J (forget₂ (ModuleCat.{max w v} Λ) AddCommGrpCat)).obj
      ((sheafCompose J (ModuleCat.coinduce Λ)).obj A)) (n + 1)) := by
  classical
  obtain ⟨ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite Λ
  have hq (i : ι) : NeZero (p i ^ e i) := ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have (i : ι) := subsingleton_H_kernel_nsmul_of_injective A (hq i).out n
  -- the generator of the `i`-th cyclic summand of `Λ` and the projection onto it
  let x (i : ι) : Λ := f.symm (DirectSum.of _ i 1)
  have hx (i : ι) : (p i ^ e i) • x i = 0 := by
    rw [← map_nsmul, ← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero, map_zero]
  let c (i : ι) : Λ →+ ZMod (p i ^ e i) := (DFinsupp.evalAddMonoidHom i).comp f.toAddMonoidHom
  refine H.subsingleton_of_sum_comp_eq_id
    (fun i ↦ kernel.lift _ _ (forget₂CoinduceEval_comp_nsmul Λ A (hx i)))
    (fun i ↦ kernelNsmulToForget₂Coinduce Λ A (c i)) ?_ (n + 1)
  ext U g
  refine (ModuleCat.coinduceObjAddEquiv Λ (A.obj.obj U)).injective (AddMonoidHom.ext fun r ↦ ?_)
  have hφ (i : ι) : (kernel.ι (p i ^ e i • 𝟙 A)).hom.app U ((kernel.lift _ _
      (forget₂CoinduceEval_comp_nsmul Λ A (hx i))).hom.app U g) =
        ModuleCat.coinduceObjAddEquiv Λ (A.obj.obj U) g (x i) :=
    congr($(kernel.lift_ι _ _ (forget₂CoinduceEval_comp_nsmul Λ A (hx i))).hom.app U g)
  have h (i : ι) : (c i r).val • x i = f.symm (DirectSum.of _ i (f r i)) := by
    rw [← map_nsmul, ← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    rfl
  rw [Hom.sum_hom_app_apply, map_sum, AddMonoidHom.finsetSum_apply]
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.comp_app, NatTrans.id_app, AddCommGrpCat.hom_comp, AddCommGrpCat.hom_id,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply,
    coinduceObjAddEquiv_kernelNsmulToForget₂Coinduce_hom_app_apply, hφ, ← map_nsmul, h]
  rw [← map_sum, ← map_sum, DirectSum.sum_univ_of, AddEquiv.symm_apply_apply]

/-- **Injective sheaves of modules over a finite ring are acyclic.** For a finite ring `Λ` and an
injective sheaf of `Λ`-modules `I`, the underlying abelian sheaf of `I` has no cohomology in
positive degrees: `I` is a retract of the coinduced sheaf `Hom_ℤ(Λ, A)` of an injective abelian
sheaf `A` containing the underlying abelian sheaf of `I`, and the latter is acyclic by
`CategoryTheory.Sheaf.subsingleton_H_forget₂_coinduce_of_injective`.

This is used to compare the cohomology of sheaves of `Λ`-modules with abelian sheaf cohomology
(blueprint `theorem-results-from-etale-theory--4`). -/
theorem subsingleton_H_forget₂_of_injective [EnoughInjectives (Sheaf J AddCommGrpCat.{max w v})]
    (Λ : Type (max w v)) [CommRing Λ] [Finite Λ]
    [J.HasSheafCompose (forget₂ (ModuleCat.{max w v} Λ) AddCommGrpCat.{max w v})]
    (I : Sheaf J (ModuleCat.{max w v} Λ)) [Injective I] (n : ℕ) :
    Subsingleton
      (H ((sheafCompose J (forget₂ (ModuleCat.{max w v} Λ) AddCommGrpCat)).obj I) (n + 1)) := by
  let ι := Injective.ι ((sheafCompose J (forget₂ (ModuleCat.{max w v} Λ) AddCommGrpCat)).obj I)
  let m := (forget₂CoinduceAdj J Λ).homEquiv _ _ ι
  have := mono_forget₂CoinduceAdj_homEquiv J Λ ι
  have := subsingleton_H_forget₂_coinduce_of_injective Λ (Injective.under
    ((sheafCompose J (forget₂ (ModuleCat.{max w v} Λ) AddCommGrpCat)).obj I)) n
  refine H.subsingleton_of_sum_comp_eq_id (ι := Unit)
    (fun _ ↦ (sheafCompose J (forget₂ (ModuleCat.{max w v} Λ) AddCommGrpCat)).map m)
    (fun _ ↦ (sheafCompose J (forget₂ (ModuleCat.{max w v} Λ) AddCommGrpCat)).map
      (Injective.factorThru (𝟙 I) m)) ?_ (n + 1)
  rw [Fintype.sum_unique, ← Functor.map_comp, Injective.comp_factorThru, Functor.map_id]

end Acyclic

end Sheaf

end CategoryTheory
