/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedConstantPresentation.CompletedConstantCompletionFunctor
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Maps

/-! # Right exactness of completed constant finite modules

Source: Stacks Project, More on Algebra, Tag 0912; Modules on Sites, Tags 093J--093M.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.CompletedConstantPresentation

private noncomputable def sections (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] (U : X.ProEtᵒᵖ) :
    ModuleCat.{u + 1} A ⥤ ModuleCat.{u + 1} A :=
  adicLisseConstantModules X A ⋙ (SheafOfModules.evaluation (adicLisseRing X A) U :
      SheafOfModules.{u + 1} (adicLisseRing X A) ⥤ ModuleCat.{u + 1} _) ⋙
    ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} ((adicLisseConstantUnit X A).app U).hom

private instance sections_additive (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] (U : X.ProEtᵒᵖ) :
    (sections X A U).Additive := by
  have := CompletedConstantReduction.constant_additive X A
  constructor
  intro M N f g
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((adicLisseConstantModules X A).map (f + g)).val.app U x = _
  rw [Functor.map_add]
  rfl

private theorem sections_surjective (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] {M N : ModuleCat.{u + 1} A}
    (f : M ⟶ N) (hf : Function.Surjective f) (U : X.ProEtᵒᵖ) :
    Function.Surjective ((sections X A U).map f) := by
  classical
  let e := constantCommuteCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let f' := (forget₂ (ModuleCat A) AddCommGrpCat).map f
  let s : N → M := Function.surjInv hf
  let s' := (constantSheaf (ProEt.topology X) (Type (u + 1))).map (TypeCat.ofHom s)
  have hs : s' ≫ (constantSheaf (ProEt.topology X) (Type (u + 1))).map
      ((CategoryTheory.forget _).map f') = 𝟙 _ := by
    rw [← Functor.map_comp]
    rw [← (constantSheaf (ProEt.topology X) (Type (u + 1))).map_id]
    congr 1
    ext x
    exact Function.surjInv_eq hf x
  have hnat := NatTrans.naturality e.hom f'
  intro y
  let y' := ((e.hom.app (AddCommGrpCat.of N)).hom.app U) y
  let x' := (s'.hom.app U) y'
  refine ⟨((e.inv.app (AddCommGrpCat.of M)).hom.app U) x', ?_⟩
  have hn := congrArg (fun t ↦ t.hom.app U) hnat
  have hh := congrArg (fun t ↦ t.hom.app U) hs
  have hcomp := congrArg (fun t ↦ t.hom.app U) (e.inv_hom_id_app (AddCommGrpCat.of M))
  have hycomp := congrArg (fun t ↦ t.hom.app U) (e.hom_inv_id_app (AddCommGrpCat.of N))
  have hnx := congrArg (fun t ↦ t (((e.inv.app (AddCommGrpCat.of M)).hom.app U) x')) hn
  have hcx := congrArg (fun t ↦ t x') hcomp
  have hhx := congrArg (fun t ↦ t y') hh
  have hy := congrArg (fun t ↦ t y) hycomp
  dsimp at hnx hcx hhx hy
  have hx : ((e.hom.app (AddCommGrpCat.of N)).hom.app U)
      (((sections X A U).map f) (((e.inv.app (AddCommGrpCat.of M)).hom.app U) x')) = y' := by
    change _ = x' at hcx
    change _ = y' at hhx
    calc
      _ = _ := hnx
      _ = _ := congrArg _ hcx
      _ = _ := hhx
  calc
    _ = ((e.inv.app (AddCommGrpCat.of N)).hom.app U)
        (((e.hom.app (AddCommGrpCat.of N)).hom.app U)
          (((sections X A U).map f)
            (((e.inv.app (AddCommGrpCat.of M)).hom.app U) x'))) := by
      symm
      exact congrArg (fun t ↦ t
        (((sections X A U).map f)
          (((e.inv.app (AddCommGrpCat.of M)).hom.app U) x'))) hycomp
    _ = _ := congrArg _ hx
    _ = y := hy

private theorem sections_preservesFiniteLimits (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] (U : X.ProEtᵒᵖ) :
    PreservesFiniteLimits (sections X A U) := by
  have : PreservesFiniteLimits (adicLisseConstantModules X A) :=
    (CompletedConstantReduction.constant_exact X A).1
  have : PreservesFiniteLimits
      ((SheafOfModules.evaluation (adicLisseRing X A) U :
      SheafOfModules.{u + 1} (adicLisseRing X A) ⥤ ModuleCat.{u + 1} _)) := by
    exact inferInstance
  let : CommRing ((adicLisseRing X A).obj.obj U) :=
    inferInstanceAs (CommRing ((adicLisseConstantRing X A).obj.obj U))
  have hr : PreservesFiniteLimits
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        ((adicLisseConstantUnit X A).app U).hom) := inferInstance
  let H : SheafOfModules.{u + 1} (adicLisseRing X A) ⥤ ModuleCat.{u + 1} A :=
    SheafOfModules.evaluation (adicLisseRing X A) U ⋙
      ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        ((adicLisseConstantUnit X A).app U).hom
  have : PreservesFiniteLimits H := comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits (adicLisseConstantModules X A) H

attribute [local instance] sections_preservesFiniteLimits

private theorem sections_preservesFiniteColimits (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] (U : X.ProEtᵒᵖ) :
    PreservesFiniteColimits (sections X A U) := by
  have := CompletedConstantReduction.constant_additive X A
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).2
  intro S hS
  refine ⟨?_, (ModuleCat.epi_iff_surjective _).2
    (sections_surjective X A S.g hS.moduleCat_surjective_g U)⟩
  exact ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).1
    inferInstance S hS).1

attribute [local instance] sections_preservesFiniteColimits

private theorem sections_exact (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] {M N P : ModuleCat.{u + 1} A}
    (f : M ⟶ N) (g : N ⟶ P) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (U : X.ProEtᵒᵖ) :
    Function.Exact ((sections X A U).map f) ((sections X A U).map g) := by
  let S := ShortComplex.moduleCatMk f.hom g.hom hfg.linearMap_comp_eq_zero
  have hS : S.Exact := ModuleCat.shortComplex_exact S hfg
  have : Epi S.g := (ModuleCat.epi_iff_surjective _).2 hg
  have h := ((Functor.preservesFiniteColimits_tfae (sections X A U)).out 4 2 rfl rfl).1
    inferInstance S ⟨hS, inferInstance⟩
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h.1

private def kernelToQuotient {A : Type (u + 1)} [CommRing A]
    {M N : ModuleCat.{u + 1} A} (f : M ⟶ N) (I : Ideal A) (n : ℕ) :
    ModuleCat.of A f.hom.ker ⟶ ModuleCat.of A (M ⧸ (I ^ (n + 1) • ⊤ : Submodule A M)) :=
  ModuleCat.ofHom (((I ^ (n + 1) • ⊤ : Submodule A M).mkQ).comp f.hom.ker.subtype)

private theorem quotient_kernel_exact {A : Type (u + 1)} [CommRing A]
    {M N : ModuleCat.{u + 1} A} (f : M ⟶ N) (hf : Function.Surjective f)
    (I : Ideal A) (n : ℕ) :
    Function.Exact (kernelToQuotient f I n) (completedConstantQuotientMap I f n) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    constructor
    · intro hx
      have hx' : f x ∈ (I ^ (n + 1) • ⊤ : Submodule A N) :=
        (Submodule.Quotient.mk_eq_zero _).1 hx
      have himage : Submodule.map f.hom (I ^ (n + 1) • ⊤ : Submodule A M) =
          (I ^ (n + 1) • ⊤ : Submodule A N) := by
        rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hf]
      rw [← himage] at hx'
      obtain ⟨d, hd, hdx⟩ := hx'
      refine ⟨⟨x - d, by simp [LinearMap.mem_ker, map_sub, hdx]⟩, ?_⟩
      change (I ^ (n + 1) • ⊤ : Submodule A M).mkQ (x - d) =
        (I ^ (n + 1) • ⊤ : Submodule A M).mkQ x
      rw [map_sub]
      have hd0 : (I ^ (n + 1) • ⊤ : Submodule A M).mkQ d = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 hd
      rw [hd0, sub_zero]
    · rintro ⟨y, hy⟩
      rw [← hy]
      change Submodule.Quotient.mk (f y.val) = 0
      rw [(LinearMap.mem_ker.1 y.property), Submodule.Quotient.mk_zero]

private theorem quotient_surjective {A : Type (u + 1)} [CommRing A]
    {M N : ModuleCat.{u + 1} A} (f : M ⟶ N) (hf : Function.Surjective f)
    (I : Ideal A) (n : ℕ) :
    Function.Surjective (completedConstantQuotientMap I f n) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    obtain ⟨y, rfl⟩ := hf x
    exact ⟨Submodule.Quotient.mk y, rfl⟩

-- Correct each successive lift by the image of one fixed kernel module. This avoids
-- needing a separate surjectivity theorem for transitions between quotient kernels.
private theorem lift_compatible_surjections
    {R : Type (u + 1)} [CommRing R]
    (M N : ℕ → ModuleCat.{u + 1} R) (K : ModuleCat.{u + 1} R)
    (t : ∀ n, M (n + 1) ⟶ M n) (s : ∀ n, N (n + 1) ⟶ N n)
    (q : ∀ n, M n ⟶ N n) (k : ∀ n, K ⟶ M n)
    (hq : ∀ n, Function.Surjective (q n))
    (he : ∀ n, Function.Exact (k n) (q n))
    (hn : ∀ n x, q n (t n x) = s n (q (n + 1) x))
    (hk : ∀ n x, t n (k (n + 1) x) = k n x)
    (y : ∀ n, N n) (hy : ∀ n, s n (y (n + 1)) = y n) :
    ∃ x : ∀ n, M n, (∀ n, q n (x n) = y n) ∧ (∀ n, t n (x (n + 1)) = x n) := by
  classical
  have step (n : ℕ) (x : M n) (hx : q n x = y n) :
      ∃ z : M (n + 1), q (n + 1) z = y (n + 1) ∧ t n z = x := by
    obtain ⟨z, hz⟩ := hq (n + 1) (y (n + 1))
    have hd : q n (x - t n z) = 0 := by rw [map_sub, hx, hn, hz, hy, sub_self]
    obtain ⟨d, hd⟩ := (he n (x - t n z)).1 hd
    refine ⟨z + k (n + 1) d, ?_, ?_⟩
    · rw [map_add, hz, (he (n + 1) _).2 ⟨d, rfl⟩, add_zero]
    · rw [map_add, hk, hd]
      abel
  let x : (n : ℕ) → { z : M n // q n z = y n } := fun n ↦ Nat.rec
    (⟨(hq 0 (y 0)).choose, (hq 0 (y 0)).choose_spec⟩ : {z : M 0 // q 0 z = y 0})
    (fun n z ↦ ⟨(step n z.val z.property).choose,
      (step n z.val z.property).choose_spec.1⟩) n
  exact ⟨fun n ↦ (x n).val, fun n ↦ (x n).property,
    fun n ↦ (step n (x n).val (x n).property).choose_spec.2⟩

private theorem section_limit_exists (X : Scheme.{u})
    {R : Sheaf (ProEt.topology X) RingCat.{u + 1}}
    (F : ℕᵒᵖ ⥤ SheafOfModules.{u + 1} R) (U : X.ProEtᵒᵖ)
    (x : ∀ n : ℕ, (F.obj (op n)).val.obj U)
    (hx : ∀ n, (F.map (homOfLE (Nat.le_succ n)).op).val.app U (x (n + 1)) = x n) :
    ∃ y : (limit F).val.obj U, ∀ n, (limit.π F (op n)).val.app U y = x n := by
  let V := SheafOfModules.evaluation R U ⋙ CategoryTheory.forget (ModuleCat _)
  have hmap : ∀ n m (h : n ≤ m), (F.map (homOfLE h).op).val.app U (x m) = x n := by
    intro n m h
    induction h with
    | refl => simp
    | @step m h ih =>
      have he : (homOfLE (Nat.le_succ_of_le h)).op =
          (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
      rw [he, F.map_comp]
      change (F.map (homOfLE h).op).val.app U
        ((F.map (homOfLE (Nat.le_succ m)).op).val.app U (x (m + 1))) = _
      rw [hx, ih]
  let z : (F ⋙ V).sections := ⟨fun j ↦ x j.unop, by
    intro j j' f
    change (F.map f).val.app U (x j.unop) = x j'.unop
    have he : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
    rw [he]
    exact hmap _ _ _⟩
  let e := Types.isLimitEquivSections (isLimitOfPreserves V (limit.isLimit F))
  refine ⟨e.symm z, ?_⟩
  intro n
  exact congrArg (fun s : (F ⋙ V).sections ↦ s.val (op n)) (e.apply_symm_apply z)

private theorem section_limit_ext (X : Scheme.{u})
    {R : Sheaf (ProEt.topology X) RingCat.{u + 1}}
    (F : ℕᵒᵖ ⥤ SheafOfModules.{u + 1} R) (U : X.ProEtᵒᵖ)
    (x y : (limit F).val.obj U)
    (h : ∀ n : ℕ, (limit.π F (op n)).val.app U x =
      (limit.π F (op n)).val.app U y) : x = y := by
  let V := SheafOfModules.evaluation R U ⋙ CategoryTheory.forget (ModuleCat _)
  apply (Types.isLimitEquivSections (isLimitOfPreserves V (limit.isLimit F))).injective
  apply Subtype.ext
  funext n
  exact h n.unop

private theorem completion_section_surjective (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    {P Q : ModuleCat.{u + 1} (AdicCompletion I A)} (f : P ⟶ Q)
    (hf : Function.Surjective f) (U : X.ProEtᵒᵖ) :
    Function.Surjective (((completion X I).map f).val.app U) := by
  let M := completedConstantUnderlyingModule I P
  let N := completedConstantUnderlyingModule I Q
  let g : M ⟶ N := (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map f
  let F := (tower X I).obj P
  let G := (tower X I).obj Q
  let E := sections X A U
  let Mp (n : ℕ) := ModuleCat.of A (M ⧸ (I ^ (n + 1) • ⊤ : Submodule A M))
  let Np (n : ℕ) := ModuleCat.of A (N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N))
  let t (n : ℕ) := E.map (ModuleCat.ofHom (Submodule.factorPowSucc I M (n + 1)))
  let s (n : ℕ) := E.map (ModuleCat.ofHom (Submodule.factorPowSucc I N (n + 1)))
  let q (n : ℕ) := E.map (completedConstantQuotientMap I g n)
  let k (n : ℕ) := E.map (kernelToQuotient g I n)
  have hq (n : ℕ) : Function.Surjective (q n) :=
    sections_surjective X A _ (quotient_surjective g hf I n) U
  have he (n : ℕ) : Function.Exact (k n) (q n) :=
    sections_exact X A _ _ (quotient_kernel_exact g hf I n)
      (quotient_surjective g hf I n) U
  have hn (n : ℕ) (x : E.obj (Mp (n + 1))) : q n (t n x) = s n (q (n + 1) x) := by
    have h : ModuleCat.ofHom (Submodule.factorPowSucc I M (n + 1)) ≫
        completedConstantQuotientMap I g n =
          completedConstantQuotientMap I g (n + 1) ≫
            ModuleCat.ofHom (Submodule.factorPowSucc I N (n + 1)) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ x => rfl
    have hh := congrArg E.map h
    simp only [Functor.map_comp] at hh
    exact ConcreteCategory.congr_hom hh x
  have hk (n : ℕ) (x : E.obj (ModuleCat.of A g.hom.ker)) :
      t n (k (n + 1) x) = k n x := by
    have h : kernelToQuotient g I (n + 1) ≫
        ModuleCat.ofHom (Submodule.factorPowSucc I M (n + 1)) = kernelToQuotient g I n := by
      rfl
    have hh := congrArg E.map h
    simp only [Functor.map_comp] at hh
    exact ConcreteCategory.congr_hom hh x
  change Function.Surjective ((limMap ((tower X I).map f)).val.app U)
  intro y
  let yp (n : ℕ) := (limit.π G (op n)).val.app U y
  have hyp (n : ℕ) : s n (yp (n + 1)) = yp n := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun h ↦ h.val.app U) (limit.w G (homOfLE (Nat.le_succ n)).op)) y
    change (G.map (homOfLE (Nat.le_succ n)).op).val.app U (yp (n + 1)) = yp n at h
    simp only [G, tower, adicLisseModuleSystem,
      Functor.ofOpSequence_map_homOfLE_succ] at h
    exact h
  obtain ⟨x, hx, ht⟩ := lift_compatible_surjections
    (fun n ↦ E.obj (Mp n)) (fun n ↦ E.obj (Np n)) (E.obj (ModuleCat.of A g.hom.ker))
    t s q k hq he hn hk yp hyp
  have ht' : ∀ n, (F.map (homOfLE (Nat.le_succ n)).op).val.app U (x (n + 1)) = x n := by
    intro n
    simp only [F, tower, adicLisseModuleSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact ht n
  obtain ⟨z, hz⟩ := section_limit_exists X F U x ht'
  refine ⟨z, section_limit_ext X G U _ y (fun n ↦ ?_)⟩
  have h := ConcreteCategory.congr_hom
    (congrArg (fun h ↦ h.val.app U) (limMap_π ((tower X I).map f) (op n))) z
  change (limit.π G (op n)).val.app U ((limMap ((tower X I).map f)).val.app U z) = _ at h
  rw [h]
  change q n ((limit.π F (op n)).val.app U z) = yp n
  rw [hz]
  exact hx n

private theorem sections_exact_all (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] {M N P : ModuleCat.{u + 1} A}
    (f : M ⟶ N) (g : N ⟶ P) (hfg : Function.Exact f g) (U : X.ProEtᵒᵖ) :
    Function.Exact ((sections X A U).map f) ((sections X A U).map g) := by
  let S := ShortComplex.moduleCatMk f.hom g.hom hfg.linearMap_comp_eq_zero
  have hS : S.Exact := ModuleCat.shortComplex_exact S hfg
  have h := ((Functor.exact_tfae (sections X A U)).out 4 2 rfl rfl).1
    ⟨inferInstance, inferInstance⟩ S hS
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h

private theorem sections_kernel_bound (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] {M N P : ModuleCat.{u + 1} A}
    (f : M ⟶ N) (g : M ⟶ P) (hfg : f.hom.ker ≤ g.hom.ker) (U : X.ProEtᵒᵖ)
    (x : (sections X A U).obj M) (hx : (sections X A U).map f x = 0) :
    (sections X A U).map g x = 0 := by
  let i : ModuleCat.of A f.hom.ker ⟶ M := ModuleCat.ofHom f.hom.ker.subtype
  obtain ⟨z, hz⟩ := (sections_exact_all X A i f f.hom.exact_subtype_ker_map U x).1 hx
  have h : i ≫ g = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact hfg z.property
  have hh := congrArg (sections X A U).map h
  rw [Functor.map_comp, Functor.map_zero] at hh
  rw [← hz]
  exact ConcreteCategory.congr_hom hh z

private def mapToQuotient {A : Type (u + 1)} [CommRing A]
    {M N : ModuleCat.{u + 1} A} (f : M ⟶ N) (I : Ideal A) (n : ℕ) :
    M ⟶ ModuleCat.of A (N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N)) :=
  ModuleCat.ofHom (((I ^ (n + 1) • ⊤ : Submodule A N).mkQ).comp f.hom)

private theorem quotient_exact {A : Type (u + 1)} [CommRing A]
    {M N P : ModuleCat.{u + 1} A} (f : M ⟶ N) (g : N ⟶ P)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (I : Ideal A) (n : ℕ) :
    Function.Exact (mapToQuotient f I n) (completedConstantQuotientMap I g n) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    constructor
    · intro hx
      have hx' : g x ∈ (I ^ (n + 1) • ⊤ : Submodule A P) :=
        (Submodule.Quotient.mk_eq_zero _).1 hx
      have himage : Submodule.map g.hom (I ^ (n + 1) • ⊤ : Submodule A N) =
          (I ^ (n + 1) • ⊤ : Submodule A P) := by
        rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hg]
      rw [← himage] at hx'
      obtain ⟨d, hd, hdx⟩ := hx'
      obtain ⟨y, hy⟩ := (hfg (x - d)).1 (by simp [map_sub, hdx])
      refine ⟨y, ?_⟩
      change (I ^ (n + 1) • ⊤ : Submodule A N).mkQ (f y) =
        (I ^ (n + 1) • ⊤ : Submodule A N).mkQ x
      rw [hy, map_sub]
      have hd0 : (I ^ (n + 1) • ⊤ : Submodule A N).mkQ d = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 hd
      rw [hd0, sub_zero]
    · rintro ⟨y, hy⟩
      rw [← hy]
      change Submodule.Quotient.mk (g (f y)) = 0
      rw [hfg.apply_apply_eq_zero y, Submodule.Quotient.mk_zero]

-- Artin-Rees over the completed ring controls the filtration after restriction to A.
-- Source: Stacks, Algebra, lemmas Artin-Rees (00IN) and map-AR.
private theorem completion_artinRees (_X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P Q : ModuleCat.{u + 1} (AdicCompletion I A)}
    [Module.Finite (AdicCompletion I A) Q] (f : P ⟶ Q) (hf : Function.Injective f) :
    ∃ c : ℕ, ∀ n : ℕ,
      (mapToQuotient
        ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map f) I
          (n + c)).hom.ker ≤
        (mapToQuotient (𝟙 (completedConstantUnderlyingModule I P)) I n).hom.ker := by
  let C := AdicCompletion I A
  let J := I.map (algebraMap A C)
  have : IsNoetherianRing C := AdicCompletion.isNoetherianRing I
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul J f.hom.range
  have hpow (V : ModuleCat.{u + 1} C) (n : ℕ) (x : V) :
      x ∈ (J ^ n • ⊤ : Submodule C V) ↔
        x ∈ (I ^ n • ⊤ : Submodule A (completedConstantUnderlyingModule I V)) := by
    let : Module A V := Module.compHom V (algebraMap A C)
    let : IsScalarTower A C V := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    have h := Submodule.restrictScalars_map_smul_eq (I ^ n) (⊤ : Submodule C V)
    rw [Ideal.map_pow] at h
    exact SetLike.ext_iff.mp h x
  refine ⟨c, fun n x hx ↦ ?_⟩
  have hx' : f x ∈ (J ^ (n + c + 1) • ⊤ : Submodule C Q) :=
    (hpow Q (n + c + 1) (f x)).2
      ((Submodule.Quotient.mk_eq_zero
        (I ^ (n + c + 1) • ⊤ : Submodule A (completedConstantUnderlyingModule I Q))).1 hx)
  have hmem : f x ∈ (J ^ (n + 1) • f.hom.range : Submodule C Q) := by
    have hle : J ^ (n + c + 1 - c) • (J ^ c • ⊤ ⊓ f.hom.range) ≤
        J ^ (n + c + 1 - c) • f.hom.range := smul_mono_right _ inf_le_right
    have he : n + c + 1 - c = n + 1 := by omega
    rw [he] at hle
    apply hle
    have h := hc (n + c + 1) (by omega)
    rw [he] at h
    rw [← h]
    exact ⟨hx', ⟨x, rfl⟩⟩
  rw [← Submodule.map_top, ← Submodule.map_smul''] at hmem
  obtain ⟨z, hz, hzx⟩ := hmem
  have hz' : z = x := hf hzx
  subst z
  apply (Submodule.Quotient.mk_eq_zero
    (I ^ (n + 1) • ⊤ : Submodule A (completedConstantUnderlyingModule I P))).2
  exact (hpow P (n + 1) x).1 hz

-- Package the quotient maps as a functor before proving compatibility. Induction can
-- then use the functor laws without unfolding quotient constructions in its motive.
private def quotient_tower {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (N : ModuleCat.{u + 1} A) : ℕᵒᵖ ⥤ ModuleCat.{u + 1} A where
  obj n := ModuleCat.of A (N ⧸ (I ^ (n.unop + 1) • ⊤ : Submodule A N))
  map f := ModuleCat.ofHom (Submodule.factorPow I N
    (Nat.add_le_add_right (leOfHom f.unop) 1))
  map_id _ := by
    apply ModuleCat.hom_ext
    exact Submodule.mapQ_id _
  map_comp {X Y Z} f g := by
    have h₁ : (I ^ (X.unop + 1) • ⊤ : Submodule A N) ≤ I ^ (Y.unop + 1) • ⊤ :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1))
    have h₂ : (I ^ (Y.unop + 1) • ⊤ : Submodule A N) ≤ I ^ (Z.unop + 1) • ⊤ :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom g.unop) 1))
    apply ModuleCat.hom_ext
    exact (Submodule.factor_comp h₁ h₂).symm

private theorem module_sequence_compatible
    {A : Type (u + 1)} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{u + 1} A)
    (y : ∀ n : ℕ, F.obj (op n))
    (hy : ∀ n, F.map (homOfLE (Nat.le_succ n)).op (y (n + 1)) = y n) :
    ∀ m n (h : n ≤ m), F.map (homOfLE h).op (y m) = y n := by
  intro m n h
  induction h with
  | refl => simp
  | @step m h ih =>
    have he : (homOfLE (Nat.le_succ_of_le h)).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [he, F.map_comp]
    change F.map (homOfLE h).op (F.map (homOfLE (Nat.le_succ m)).op (y (m + 1))) = _
    exact (congrArg (fun z ↦ F.map (homOfLE h).op z) (hy m)).trans ih

private theorem quotient_sections_compatible
    {A : Type (u + 1)} [CommRing A] (E : ModuleCat.{u + 1} A ⥤ ModuleCat.{u + 1} A)
    (I : Ideal A) (N : ModuleCat.{u + 1} A)
    (y : ∀ n : ℕ, E.obj (ModuleCat.of A (N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N))))
    (hy : ∀ n, E.map (ModuleCat.ofHom (Submodule.factorPowSucc I N (n + 1)))
      (y (n + 1)) = y n) :
    ∀ m n (h : n ≤ m), E.map (ModuleCat.ofHom
      (Submodule.factorPow I N (Nat.add_le_add_right h 1))) (y m) = y n := by
  exact module_sequence_compatible (quotient_tower I N ⋙ E) y hy

private theorem shifted_exact_lifts
    {A : Type (u + 1)} [CommRing A] (K : ModuleCat.{u + 1} A)
    (M N : ℕ → ModuleCat.{u + 1} A)
    (j : ∀ n, K ⟶ M n) (k : ∀ n, K ⟶ N n) (f : ∀ n, M n ⟶ N n)
    (t : ∀ n, M (n + 1) ⟶ M n) (s : ∀ m n, n ≤ m → (N m ⟶ N n))
    (hj : ∀ n x, t n (j (n + 1) x) = j n x)
    (hk : ∀ m n h x, s m n h (k m x) = k n x)
    (hf : ∀ n x, f n (j n x) = k n x)
    (c : ℕ) (hb : ∀ n x, k (n + c) x = 0 → j n x = 0)
    (y : ∀ n, N n) (hy : ∀ m n h, s m n h (y m) = y n)
    (he : ∀ n, ∃ z, k n z = y n) :
    ∃ a : ∀ n, M n, (∀ n, t n (a (n + 1)) = a n) ∧ ∀ n, f n (a n) = y n := by
  classical
  choose z hz using he
  let a (n : ℕ) := j n (z (n + c))
  refine ⟨a, ?_, ?_⟩
  · intro n
    have hd : k (n + c) (z (n + 1 + c) - z (n + c)) = 0 := by
      rw [map_sub, hz]
      have h := hk (n + 1 + c) (n + c) (by omega) (z (n + 1 + c))
      rw [hz, hy (n + 1 + c) (n + c) (by omega)] at h
      rw [← h, sub_self]
    have hd' := hb n _ hd
    rw [map_sub] at hd'
    exact (hj n (z (n + 1 + c))).trans (sub_eq_zero.mp hd')
  · intro n
    change f n (j n (z (n + c))) = y n
    rw [hf]
    have h := hk (n + c) n (by omega) (z (n + c))
    rw [hz, hy (n + c) n (by omega)] at h
    exact h.symm

-- Shift arbitrary lifts by the uniform Artin-Rees bound. Their differences then vanish
-- in the required quotients, so the shifted lifts define a section of the limit.
private theorem completion_section_exact (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P Q R : ModuleCat.{u + 1} (AdicCompletion I A)}
    [Module.Finite (AdicCompletion I A) Q]
    (f : P ⟶ Q) (g : Q ⟶ R) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (U : X.ProEtᵒᵖ) :
    Function.Exact (((completion X I).map f).val.app U)
      (((completion X I).map g).val.app U) := by
  classical
  let M := completedConstantUnderlyingModule I P
  let N := completedConstantUnderlyingModule I Q
  let L := completedConstantUnderlyingModule I R
  let fa : M ⟶ N := (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map f
  let ga : N ⟶ L := (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map g
  let E := sections X A U
  let F := (tower X I).obj P
  let G := (tower X I).obj Q
  let H := (tower X I).obj R
  let j (n : ℕ) := mapToQuotient (𝟙 M) I n
  let k (n : ℕ) := mapToQuotient fa I n
  let q (n : ℕ) := completedConstantQuotientMap I ga n
  let t (V : ModuleCat.{u + 1} A) (m n : ℕ) (h : n ≤ m) :=
    ModuleCat.ofHom (Submodule.factorPow I V (Nat.add_le_add_right h 1))
  have kt (m n : ℕ) (h : n ≤ m) (x : E.obj M) :
      E.map (t N m n h) (E.map (k m) x) = E.map (k n) x := by
    have hh : k m ≫ t N m n h = k n := by rfl
    have hh' := congrArg E.map hh
    rw [Functor.map_comp] at hh'
    exact ConcreteCategory.congr_hom hh' x
  have jt (m n : ℕ) (h : n ≤ m) (x : E.obj M) :
      E.map (t M m n h) (E.map (j m) x) = E.map (j n) x := by
    have hh : j m ≫ t M m n h = j n := by rfl
    have hh' := congrArg E.map hh
    rw [Functor.map_comp] at hh'
    exact ConcreteCategory.congr_hom hh' x
  obtain ⟨c, hc⟩ := completion_artinRees X I f hf
  intro y
  constructor
  · intro hy
    change (limMap ((tower X I).map g)).val.app U y = 0 at hy
    let yp (n : ℕ) : E.obj (ModuleCat.of A (N ⧸
        (I ^ (n + 1) • ⊤ : Submodule A N))) := (limit.π G (op n)).val.app U y
    have yp_step (n : ℕ) : E.map (t N (n + 1) n (Nat.le_succ n))
        (yp (n + 1)) = yp n := by
      have hh := ConcreteCategory.congr_hom
        (congrArg (fun a ↦ a.val.app U) (limit.w G (homOfLE (Nat.le_succ n)).op)) y
      change (G.map (homOfLE (Nat.le_succ n)).op).val.app U (yp (n + 1)) = yp n at hh
      simp only [G, tower, adicLisseModuleSystem,
        Functor.ofOpSequence_map_homOfLE_succ] at hh
      exact hh
    have yp_t (m n : ℕ) (h : n ≤ m) : E.map (t N m n h) (yp m) = yp n :=
      quotient_sections_compatible E I N yp yp_step m n h
    have yp_q (n : ℕ) : E.map (q n) (yp n) = 0 := by
      have hh := ConcreteCategory.congr_hom
        (congrArg (fun a ↦ a.val.app U) (limMap_π ((tower X I).map g) (op n))) y
      change (limit.π H (op n)).val.app U
        ((limMap ((tower X I).map g)).val.app U y) = E.map (q n) (yp n) at hh
      rw [hy, map_zero] at hh
      exact hh.symm
    have hz (n : ℕ) : ∃ z : E.obj M, E.map (k n) z = yp n :=
      (sections_exact X A (k n) (q n) (quotient_exact fa ga hfg hg I n)
        (quotient_surjective ga hg I n) U (yp n)).1 (yp_q n)
    let l (n : ℕ) := completedConstantQuotientMap I fa n
    have hjf (n : ℕ) (x : E.obj M) : E.map (l n) (E.map (j n) x) = E.map (k n) x := by
      have h : j n ≫ l n = k n := rfl
      have hh := congrArg E.map h
      rw [Functor.map_comp] at hh
      exact ConcreteCategory.congr_hom hh x
    obtain ⟨a, ha, haf⟩ := shifted_exact_lifts (E.obj M)
      (fun n ↦ E.obj (ModuleCat.of A (M ⧸ (I ^ (n + 1) • ⊤ : Submodule A M))))
      (fun n ↦ E.obj (ModuleCat.of A (N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N))))
      (fun n ↦ E.map (j n)) (fun n ↦ E.map (k n)) (fun n ↦ E.map (l n))
      (fun n ↦ E.map (t M (n + 1) n (Nat.le_succ n)))
      (fun m n h ↦ E.map (t N m n h))
      (fun n x ↦ jt (n + 1) n (Nat.le_succ n) x) kt hjf c
      (fun n x hx ↦ sections_kernel_bound X A (k (n + c)) (j n) (hc n) U x hx)
      yp yp_t hz
    have ha' : ∀ n, (F.map (homOfLE (Nat.le_succ n)).op).val.app U
        (a (n + 1)) = a n := by
      intro n
      simp only [F, tower, adicLisseModuleSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact ha n
    obtain ⟨x, hx⟩ := section_limit_exists X F U a ha'
    refine ⟨x, section_limit_ext X G U _ y (fun n ↦ ?_)⟩
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun a ↦ a.val.app U) (limMap_π ((tower X I).map f) (op n))) x
    change (limit.π G (op n)).val.app U
      ((limMap ((tower X I).map f)).val.app U x) =
        E.map (completedConstantQuotientMap I fa n) ((limit.π F (op n)).val.app U x) at hh
    change (limit.π G (op n)).val.app U
      ((limMap ((tower X I).map f)).val.app U x) = yp n
    rw [hh, hx]
    exact haf n
  · rintro ⟨x, rfl⟩
    have h : f ≫ g = 0 := ModuleCat.hom_ext hfg.linearMap_comp_eq_zero
    have hh := congrArg (completion X I).map h
    rw [Functor.map_comp, Functor.map_zero] at hh
    exact ConcreteCategory.congr_hom (congrArg (fun a ↦ a.val.app U) hh) x

private noncomputable def sectionwise_cokernel (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A]
    {M N P : SheafOfModules.{u + 1} (adicLisseRing X A)}
    (f : M ⟶ N) (g : N ⟶ P) (h : f ≫ g = 0)
    (he : ∀ U, Function.Exact (f.val.app U) (g.val.app U))
    (hs : ∀ U, Function.Surjective (g.val.app U)) :
    IsColimit (CokernelCofork.ofπ g h) := by
  apply isColimitOfReflects (SheafOfModules.forget (adicLisseRing X A))
  apply PresheafOfModules.evaluationJointlyReflectsColimits
  intro U
  change IsColimit ((SheafOfModules.evaluation (adicLisseRing X A) U).mapCocone
    (CokernelCofork.ofπ g h))
  refine (isColimitMapCoconeCoforkEquiv'
    (SheafOfModules.evaluation (adicLisseRing X A) U) h).symm ?_
  exact ModuleCat.isColimitCokernelCofork (f.val.app U) (g.val.app U) (he U) (hs U)

/-- Completion of constant modules preserves cokernels of maps between finite modules.
Source: Stacks Project, More on Algebra, Tag 0912 (lemma-limit-flat); Modules on Sites,
Tags 093J--093M (constant exactness, finite-presentation tensor comparison and flat sections).
(blueprint: lem-weil-pbc-completed-constant-completion-right-exact).

Proof: put C = AdicCompletion I A and J = IC. The completion theorem makes C Noetherian,
and evaluation identifies C/J^(n+1) with A/I^(n+1), compatibly with transitions.
One may first replace the essentially small pro-etale site by its coefficient-sized
equivalent site; constant sheaves, limits and cokernels transport across that equivalence.
For every C-module V, J^k V = I^k V after restriction to A: C-multiplication in a generator
can be absorbed into V. On any site object U let B_n be the sections of the constant
C/J^(n+1). They are flat over C/J^(n+1) and the transitions are surjective, by constant
section flatness and exactness. Tag 0912 identifies V tensor_C lim B_n with
lim (V tensor_C B_n) for each finite V. Finite V is finitely presented over C, so Tag 093K
identifies the latter with lim constant(V/J^(n+1)V)(U), naturally in V and U. Thus a
finite-module presentation P -> Q -> coker f -> 0 becomes, sectionwise, its tensor
with lim B_n and remains right exact. These sectionwise cokernel diagrams commute
with restrictions and hence give cokernel diagrams of sheaves. The universal property
is preservation of the indicated parallel-pair colimit. The cokernel is finite, so
all three applications of the finite tensor comparison are legitimate. No injectivity
of f is assumed. Zero modules, I=0, I=top and the zero ring obey the same diagrams. -/
theorem completion_preservesCokernel (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P Q : ModuleCat.{u + 1} (AdicCompletion I A)}
    [Module.Finite (AdicCompletion I A) P] [Module.Finite (AdicCompletion I A) Q]
    (f : P ⟶ Q) :
    PreservesColimit (parallelPair f 0) (completion X I) := by
  -- Work with the image to avoid imposing injectivity on the original map.
  let C := AdicCompletion I A
  let D := ModuleCat.of C f.hom.range
  let r : P ⟶ D := ModuleCat.ofHom f.hom.rangeRestrict
  let i : D ⟶ Q := ModuleCat.ofHom f.hom.range.subtype
  let q : Q ⟶ ModuleCat.of C (Q ⧸ f.hom.range) := ModuleCat.ofHom f.hom.range.mkQ
  let F := completion X I
  have hri : r ≫ i = f := rfl
  have hiq : Function.Exact i q := LinearMap.exact_subtype_mkQ f.hom.range
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hi : Function.Injective i := Subtype.val_injective
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨y, hy⟩ := x.property
    exact ⟨y, Subtype.ext hy⟩
  have hzero : f ≫ q = 0 := ModuleCat.hom_ext (LinearMap.range_mkQ_comp f.hom)
  have he (U : X.ProEtᵒᵖ) :
      Function.Exact ((F.map f).val.app U) ((F.map q).val.app U) := by
    have he := completion_section_exact X I i q hi hiq hq U
    intro y
    constructor
    · intro hy
      obtain ⟨z, hz⟩ := (he y).1 hy
      obtain ⟨x, hx⟩ := completion_section_surjective X I r hr U z
      refine ⟨x, ?_⟩
      have h := congrArg F.map hri
      rw [Functor.map_comp] at h
      rw [← h]
      change (F.map i).val.app U ((F.map r).val.app U x) = y
      rw [hx, hz]
    · rintro ⟨x, rfl⟩
      have h := congrArg F.map hzero
      rw [Functor.map_comp, Functor.map_zero] at h
      exact ConcreteCategory.congr_hom (congrArg (fun a ↦ a.val.app U) h) x
  apply preservesColimit_of_preserves_colimit_cocone (ModuleCat.cokernelIsColimit f)
  refine (isColimitMapCoconeCoforkEquiv' F hzero).symm ?_
  exact sectionwise_cokernel X (F.map f) (F.map q)
    (by rw [← F.map_comp, hzero, F.map_zero]) he
    (fun U ↦ completion_section_surjective X I q hq U)

end AlgebraicGeometry.Scheme.CompletedConstantPresentation
