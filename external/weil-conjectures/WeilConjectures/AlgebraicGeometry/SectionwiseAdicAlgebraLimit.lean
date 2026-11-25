/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.RingTheory.LimitFlatModules

/-! # Sectionwise adic algebra limits

Source: Stacks Project, sites-modules.tex, Tags 093M and 0912 (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Evaluate a constant-ring algebra sheaf as an algebra over the original ring.
Source: Stacks Project, Tag 093M (auxiliary; not a blueprint node). The scalar map is the
constant-presheaf
sheafification unit followed by the structural map; no algebra action is chosen. -/
def adicAlgebraSections {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [CommRing A] (U : Cᵒᵖ) :
    Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)) ⥤ CommAlgCat.{u} A :=
  Under.post ((sheafSections J CommRingCat.{u}).obj U) ⋙
    Under.map ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U) ⋙
    (commAlgCatEquivUnder (CommRingCat.of A)).inverse

/-- The algebra of sections of the n+1 term of the given tower.
Source: Stacks Project, Tag 093M (auxiliary; not a blueprint node). -/
abbrev adicTerm {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [CommRing A]
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    (n : ℕ) (U : Cᵒᵖ) : CommAlgCat.{u} A :=
  (adicAlgebraSections J A U).obj (S.obj (op n))

/-- Sections of the ring-sheaf limit with their induced A-algebra structure.
Source: Stacks Project, Tag 093M (auxiliary; not a blueprint node). -/
abbrev adicLimit {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [CommRing A]
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    (U : Cᵒᵖ) : CommAlgCat.{u} A :=
  (adicAlgebraSections J A U).obj (limit S)

/-- The transition on algebras of sections.
Source: Stacks Project, Tag 093M (auxiliary; not a blueprint node). -/
def adicTransition {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [CommRing A]
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    (m n : ℕ) (h : n ≤ m) (U : Cᵒᵖ) : adicTerm J A S m U →ₐ[A] adicTerm J A S n U :=
  ((adicAlgebraSections J A U).map (S.map (homOfLE h).op)).hom

/-- The original limit projection on algebras of sections.
Source: Stacks Project, Tag 093M (auxiliary; not a blueprint node). -/
def adicProjection {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [CommRing A]
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    (n : ℕ) (U : Cᵒᵖ) : adicLimit J A S U →ₐ[A] adicTerm J A S n U :=
  ((adicAlgebraSections J A U).map (limit.π S (op n))).hom

/-- Canonical comparison into the product of sectionwise tensor products.
Source: Stacks Project, Tag 0912 (auxiliary; not a blueprint node). Its image will be exactly the
compatible families. -/
def adicTensorComparison {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [CommRing A]
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    (U : Cᵒᵖ) (F : Type w) [AddCommGroup F] [Module A F] :
    TensorProduct A (adicLimit J A S U) F →ₗ[A]
      (∀ n : ℕ, TensorProduct A (adicTerm J A S n U) F) :=
  LinearMap.pi (fun n ↦ (adicProjection J A S n U).toLinearMap.rTensor F)

/-- A constant-ring algebra sheaf regarded as a module over the constant ring sheaf.
Source: Stacks Project, Tag 093M (auxiliary; not a blueprint node). This is restriction of scalars
of the unit. -/
abbrev adicUnderlyingModule {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [CommRing A]
    (B : Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A))) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map B.hom)).obj
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B.right))

private abbrev adicSectionModules {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A] (U : Cᵒᵖ) :=
  adicAlgebraSections J A U ⋙ forget₂ (CommAlgCat A) (AlgCat A) ⋙
    forget₂ (AlgCat A) (ModuleCat A)

private def adicModuleLimitIso {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    (U : Cᵒᵖ) : ModuleCat.of A (adicLimit J A S U) ≅ limit (S ⋙ adicSectionModules J A U) :=
  IsLimit.conePointUniqueUpToIso
    (show IsLimit ((adicSectionModules J A U).mapCone (limit.cone S)) by
      apply isLimitOfReflects (forget (ModuleCat A))
      exact isLimitOfPreserves
        (Under.forget _ ⋙ sheafToPresheaf J CommRingCat ⋙
          (evaluation Cᵒᵖ CommRingCat).obj U ⋙ forget CommRingCat) (limit.isLimit S))
    (limit.isLimit _)

private theorem adicModuleLimitIso_π {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    (U : Cᵒᵖ) (n : ℕ) :
    (adicModuleLimitIso J A S U).hom ≫ limit.π (S ⋙ adicSectionModules J A U) (op n) =
      ModuleCat.ofHom (adicProjection J A S n U).toLinearMap :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

private theorem adicProjection_transition {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    (m n : ℕ) (h : n ≤ m) (U : Cᵒᵖ) (b : adicLimit J A S U) :
    adicTransition J A S m n h U (adicProjection J A S m U b) =
      adicProjection J A S n U b := by
  have h := congrArg (fun f ↦ ((adicAlgebraSections J A U).map f).hom b)
    (limit.w S (homOfLE h).op)
  simpa only [adicTransition, adicProjection, Functor.map_comp,
    CommAlgCat.hom_comp, AlgHom.comp_apply] using h

private def adicRestriction {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (B : Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    {U V : Cᵒᵖ} (g : U ⟶ V) :
    (adicAlgebraSections J A U).obj B →ₐ[A] (adicAlgebraSections J A V).obj B :=
  { (B.right.obj.map g).hom with
    commutes' := by
      intro a
      have h₁ := congrArg (fun f ↦ f a)
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).naturality g)
      have h₂ := congrArg (fun f ↦ f
        (((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U) a))
        (B.hom.hom.naturality g)
      exact h₂.symm.trans (congrArg (B.hom.hom.app V) h₁.symm) }

private theorem adicProjection_restrict {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    (n : ℕ) {U V : Cᵒᵖ} (g : U ⟶ V) (b : adicLimit J A S U) :
    adicProjection J A S n V ((limit S).right.obj.map g b) =
      (S.obj (op n)).right.obj.map g (adicProjection J A S n U b) := by
  exact congrArg (fun f ↦ f b) ((limit.π S (op n)).right.hom.naturality g)

private theorem adicTensor_projection {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    (U : Cᵒᵖ) (F : Type w) [AddCommGroup F] [Module A F]
    (x : TensorProduct A (adicLimit J A S U) F) (n : ℕ) :
    (limit.π (S ⋙ adicSectionModules J A U) (op n)).hom.lTensor F
        ((adicModuleLimitIso J A S U).toLinearEquiv.lTensor F
          (TensorProduct.comm A _ _ x)) =
      TensorProduct.comm A _ _ (adicTensorComparison J A S U F x n) := by
  induction x using TensorProduct.inductionOn with
  | tmul b f =>
    change f ⊗ₜ[A] ((limit.π (S ⋙ adicSectionModules J A U) (op n)).hom
      ((adicModuleLimitIso J A S U).hom.hom b)) =
      f ⊗ₜ[A] adicProjection J A S n U b
    exact congrArg (fun z ↦ f ⊗ₜ[A] z)
      (congrArg (fun g ↦ g.hom b) (adicModuleLimitIso_π J A S U n))
  | add x y hx hy => simp only [map_add, hx, hy, Pi.add_apply]

private theorem adicSectionwiseFlatTensor {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A)
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    [∀ (n : ℕ) (U : Cᵒᵖ), Module (A ⧸ I ^ (n + 1)) (adicTerm J A S n U)]
    [∀ (n : ℕ) (U : Cᵒᵖ), IsScalarTower A (A ⧸ I ^ (n + 1)) (adicTerm J A S n U)]
    (hflat : ∀ (n : ℕ) (U : Cᵒᵖ),
      Module.Flat (A ⧸ I ^ (n + 1)) (adicTerm J A S n U))
    (hsurj : ∀ (n : ℕ) (U : Cᵒᵖ),
      Function.Surjective (adicTransition J A S (n + 1) n (Nat.le_succ n) U)) :
    (∀ U : Cᵒᵖ, Module.Flat A (adicLimit J A S U)) ∧
    (∀ (U : Cᵒᵖ) (F : Type w) [AddCommGroup F] [Module A F] [Module.Finite A F],
      Function.Injective (adicTensorComparison J A S U F) ∧
      ∀ x : ∀ n : ℕ, TensorProduct A (adicTerm J A S n U) F,
        (∀ n : ℕ,
          (adicTransition J A S (n + 1) n (Nat.le_succ n) U).toLinearMap.rTensor F
            (x (n + 1)) = x n) ↔
        ∃ y, adicTensorComparison J A S U F y = x) := by
  have ht (U : Cᵒᵖ) := by
    letI : ∀ n : ℕ, Module (A ⧸ I ^ (n + 1))
        ((S ⋙ adicSectionModules J A U).obj (op n)) := fun n ↦ inferInstanceAs
          (Module (A ⧸ I ^ (n + 1)) (adicTerm J A S n U))
    letI : ∀ n : ℕ, IsScalarTower A (A ⧸ I ^ (n + 1))
        ((S ⋙ adicSectionModules J A U).obj (op n)) := fun n ↦ inferInstanceAs
          (IsScalarTower A (A ⧸ I ^ (n + 1)) (adicTerm J A S n U))
    exact ModuleCat.limit_flat_of_flat_quotients.{u, u, w} A I
      (S ⋙ adicSectionModules J A U) (fun n ↦ hflat n U) (fun n ↦ hsurj n U)
  refine ⟨fun U ↦ ?_, ?_⟩
  · let := (ht U).1
    exact Module.Flat.of_linearEquiv (adicModuleLimitIso J A S U).toLinearEquiv
  intro U F _ _ _
  let e := (TensorProduct.comm A (adicLimit J A S U) F).trans
    ((adicModuleLimitIso J A S U).toLinearEquiv.lTensor F)
  obtain ⟨hi, hs⟩ := (ht U).2 F
  refine ⟨?_, fun x ↦ ⟨?_, ?_⟩⟩
  · intro x y hxy
    apply e.injective
    apply hi
    ext n
    change (limit.π (S ⋙ adicSectionModules J A U) (op n)).hom.lTensor F
      (e x) = (limit.π (S ⋙ adicSectionModules J A U) (op n)).hom.lTensor F (e y)
    exact (adicTensor_projection J A S U F x n).trans
      ((congrArg (fun z ↦ TensorProduct.comm A _ _ (z n)) hxy).trans
        (adicTensor_projection J A S U F y n).symm)
  · intro hx
    obtain ⟨y, hy⟩ := hs (fun n ↦ TensorProduct.comm A _ _ (x n)) (fun n ↦ by
      change (adicTransition J A S (n + 1) n (Nat.le_succ n) U).toLinearMap.lTensor F
        (TensorProduct.comm A _ _ (x (n + 1))) = _
      rw [LinearMap.lTensor_comm, hx n]
      rfl)
    refine ⟨e.symm y, funext fun n ↦ ?_⟩
    apply (TensorProduct.comm A _ _).injective
    rw [← adicTensor_projection]
    change (limit.π (S ⋙ adicSectionModules J A U) (op n)).hom.lTensor F
      (e (e.symm y)) = _
    rw [e.apply_symm_apply, hy n]
    rfl
  · rintro ⟨y, rfl⟩ n
    change ((adicTransition J A S (n + 1) n (Nat.le_succ n) U).toLinearMap.rTensor F)
      (((adicProjection J A S (n + 1) U).toLinearMap.rTensor F) y) =
      ((adicProjection J A S n U).toLinearMap.rTensor F) y
    induction y using TensorProduct.inductionOn with
    | tmul b f =>
      exact congrArg (fun z : adicTerm J A S n U ↦ z ⊗ₜ[A] f)
        (adicProjection_transition J A S (n + 1) n (Nat.le_succ n) U b)
    | add x y hx hy => simp only [map_add, hx, hy]

private theorem adicTransition_comp {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    (k m n : ℕ) (hnm : n ≤ m) (hmk : m ≤ k) (U : Cᵒᵖ)
    (b : adicTerm J A S k U) :
    adicTransition J A S m n hnm U (adicTransition J A S k m hmk U b) =
      adicTransition J A S k n (hnm.trans hmk) U b := by
  change (((adicAlgebraSections J A U).map (S.map (homOfLE hnm).op)).hom.comp
    ((adicAlgebraSections J A U).map (S.map (homOfLE hmk).op)).hom) b = _
  have h := (S ⋙ adicAlgebraSections J A U).map_comp
    (homOfLE hmk).op (homOfLE hnm).op
  exact congrArg (fun f ↦ f.hom b) h.symm

private theorem adicTransition_self {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    (n : ℕ) (U : Cᵒᵖ) (b : adicTerm J A S n U) :
    adicTransition J A S n n le_rfl U b = b := by
  change ((S ⋙ adicAlgebraSections J A U).map (𝟙 (op n))).hom b = b
  rw [Functor.map_id]
  rfl

private theorem adicProjection_surjective {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    (hsurj : ∀ (n : ℕ) (U : Cᵒᵖ),
      Function.Surjective (adicTransition J A S (n + 1) n (Nat.le_succ n) U))
    (n : ℕ) (U : Cᵒᵖ) : Function.Surjective (adicProjection J A S n U) := by
  classical
  intro b
  let lift (k : ℕ) (x : adicTerm J A S k U) := (hsurj k U x).choose
  have hlift (k : ℕ) (x : adicTerm J A S k U) :
      adicTransition J A S (k + 1) k (Nat.le_succ k) U (lift k x) = x :=
    (hsurj k U x).choose_spec
  let tail (k : ℕ) (h : n ≤ k) : adicTerm J A S k U :=
    Nat.leRecOn h (fun {k} x ↦ lift k x) b
  let x (k : ℕ) : adicTerm J A S k U :=
    if h : n ≤ k then tail k h else adicTransition J A S n k (Nat.le_of_not_ge h) U b
  have hx (k : ℕ) : adicTransition J A S (k + 1) k (Nat.le_succ k) U (x (k + 1)) = x k := by
    by_cases h : n ≤ k
    · simp only [x, dite_eq_left h, dite_eq_left (h.trans (Nat.le_succ k)), tail]
      rw [Nat.leRecOn_succ h, hlift]
    · by_cases h' : n ≤ k + 1
      · have he : n = k + 1 := by omega
        subst n
        simp only [x, dite_eq_left le_rfl, dite_eq_right h, tail, Nat.leRecOn_self]
      · simp only [x, dite_eq_right h, dite_eq_right h']
        exact adicTransition_comp J A S _ _ _ _ _ _ _
  have hcompat (k m : ℕ) (h : m ≤ k) : adicTransition J A S k m h U (x k) = x m := by
    induction k, h using Nat.le_induction with
    | base => exact adicTransition_self J A S m U (x m)
    | succ k h ih =>
      rw [← adicTransition_comp J A S (k + 1) k m h (Nat.le_succ k) U, hx, ih]
  let F := S ⋙ adicSectionModules J A U
  let cone : Cone (F ⋙ forget (ModuleCat A)) :=
    Types.coneOfSection (s := fun k ↦ x k.unop) (by
      intro k m f
      exact hcompat k.unop m.unop (leOfHom f.unop))
  have hc : IsLimit ((forget (ModuleCat A)).mapCone
      ((adicSectionModules J A U).mapCone (limit.cone S))) := by
    exact isLimitOfPreserves
      (Under.forget _ ⋙ sheafToPresheaf J CommRingCat ⋙
        (evaluation Cᵒᵖ CommRingCat).obj U ⋙ forget CommRingCat) (limit.isLimit S)
  refine ⟨hc.lift cone PUnit.unit, ?_⟩
  have hp := congrArg (fun f ↦ f PUnit.unit) (hc.fac cone (op n))
  change adicProjection J A S n U (hc.lift cone PUnit.unit) = x n at hp
  simpa only [x, dite_eq_left le_rfl, tail, Nat.leRecOn_self] using hp

private theorem adicConstantLifts {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (U : C) (n : ℕ)
    (a : Fin n → ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)).obj.obj (op U)) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
      ∃ c : Fin n → A, ∀ i,
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op V)) (c i) =
          ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)).obj.map f.op (a i) := by
  classical
  induction n with
  | zero =>
    refine ⟨⊤, J.top_mem _, fun V f hf ↦ ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩⟩
  | succ n ih =>
    obtain ⟨S, hS, hs⟩ := ih (fun i ↦ a i.succ)
    let η := toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
    refine ⟨S ⊓ Presheaf.imageSieve η (a 0),
      J.intersection_covering hS (Presheaf.imageSieve_mem J η (a 0)), ?_⟩
    rintro V f ⟨hf, hg⟩
    obtain ⟨c, hc⟩ := hs V f hf
    obtain ⟨c₀, hc₀⟩ := hg
    refine ⟨Fin.cons c₀ c, Fin.cases ?_ (fun i ↦ ?_)⟩
    · exact hc₀
    · exact hc i

private theorem adicSheafFlat {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (B : Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    (hflat : ∀ U : Cᵒᵖ, Module.Flat A ((adicAlgebraSections J A U).obj B)) :
    SheafOfModules.IsFlatOnSite.{u, u, u, u}
      (R := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A))
      (adicUnderlyingModule J A B) := by
  apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion
    ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A))
  intro U n a s hrel
  obtain ⟨S, hS, hs⟩ := adicConstantLifts J A U n a
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨c, hc⟩ := hs V f hf
  let := hflat (op V)
  let t : Fin n → (adicAlgebraSections J A (op V)).obj B :=
    fun i ↦ B.right.obj.map f.op (s i)
  have hsmul (i : Fin n) :
      c i • t i = ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)).obj.map
        f.op (a i) • ((adicUnderlyingModule J A B).val.restrictₛₗ f.op (s i)) := by
    change (algebraMap A ((adicAlgebraSections J A (op V)).obj B) (c i)) * t i = _
    change B.hom.hom.app (op V)
      (((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op V)) (c i)) *
      (B.right.obj.map f.op (s i)) = _
    rw [hc i]
    rfl
  have hrel' : ∑ i, c i • t i = 0 := by
    simp_rw [hsmul]
    have h := congrArg ((adicUnderlyingModule J A B).val.map f.op) hrel
    rw [map_sum, map_zero] at h
    change (∑ i, (adicUnderlyingModule J A B).val.map f.op (a i • s i)) = 0 at h
    simp_rw [(adicUnderlyingModule J A B).val.map_smul] at h
    exact h
  obtain ⟨l, b, v, hv, hb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel'
  let η := (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op V)
  refine ⟨l, (fun i j ↦ η (b i j)), v, ?_, ?_⟩
  · intro i
    change t i = _
    rw [hv i]
    rfl
  · intro j
    simp_rw [← hc]
    change ∑ i, η (c i) * η (b i j) = 0
    simpa only [map_sum, map_mul, map_zero] using congrArg η (hb j)

private theorem adicProjection_mem_ker_iff {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A)
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    [∀ (n : ℕ) (U : Cᵒᵖ), Module (A ⧸ I ^ (n + 1)) (adicTerm J A S n U)]
    [∀ (n : ℕ) (U : Cᵒᵖ), IsScalarTower A (A ⧸ I ^ (n + 1)) (adicTerm J A S n U)]
    (hi : ∀ (U : Cᵒᵖ) (n : ℕ),
      Function.Injective (adicTensorComparison J A S U (A ⧸ I ^ (n + 1))))
    (hred : ∀ (m n : ℕ) (U : Cᵒᵖ),
      ∃ e : TensorProduct A (adicTerm J A S m U) (A ⧸ I ^ (n + 1)) ≃ₗ[A]
        adicTerm J A S (min m n) U,
        ∀ (b : adicTerm J A S m U) (a : A),
          e (b ⊗ₜ[A] Ideal.Quotient.mk _ a) =
            a • adicTransition J A S m (min m n) (Nat.min_le_left m n) U b)
    (n : ℕ) (U : Cᵒᵖ) (b : adicLimit J A S U) :
    adicProjection J A S n U b = 0 ↔
      b ∈ (I ^ (n + 1)).map (algebraMap A (adicLimit J A S U)) := by
  constructor
  · intro hb
    have ht : b ⊗ₜ[A] (1 : A ⧸ I ^ (n + 1)) = 0 := by
      apply hi U n
      ext m
      change (adicProjection J A S m U b) ⊗ₜ[A] (1 : A ⧸ I ^ (n + 1)) = 0
      obtain ⟨e, he⟩ := hred m n U
      apply e.injective
      rw [map_zero]
      change e ((adicProjection J A S m U b) ⊗ₜ[A]
        Ideal.Quotient.mk (I ^ (n + 1)) 1) = 0
      rw [he, one_smul, adicProjection_transition]
      rw [← adicProjection_transition J A S n (min m n) (Nat.min_le_right m n) U,
        hb, map_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
      (adicLimit J A S U) (I ^ (n + 1))).injective
    rw [map_zero, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    exact ht
  · intro hb
    have hle : (I ^ (n + 1)).map (algebraMap A (adicLimit J A S U)) ≤
        RingHom.ker (adicProjection J A S n U).toRingHom := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      change adicProjection J A S n U (algebraMap A (adicLimit J A S U) a) = 0
      rw [AlgHom.commutes]
      have hzero : (a : A) • (1 : adicTerm J A S n U) = 0 := by
        rw [← IsScalarTower.algebraMap_smul (A ⧸ I ^ (n + 1)) a
          (1 : adicTerm J A S n U)]
        have ha' : algebraMap A (A ⧸ I ^ (n + 1)) a = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr ha
        rw [ha', zero_smul]
      simpa only [Algebra.smul_def, mul_one] using hzero
    exact hle hb

private def adicProjectionModule {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    (n : ℕ) : adicUnderlyingModule J A (limit S) ⟶
      adicUnderlyingModule J A (S.obj (op n)) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (adicUnderlyingModule J A (limit S)).val.obj U)
        (Y := (adicUnderlyingModule J A (S.obj (op n))).val.obj U)
        { toFun := fun b ↦ adicProjection J A S n U b
          map_add' := map_add _
          map_smul' := by
            intro a b
            let p : (limit S).right.obj.obj U →+* (S.obj (op n)).right.obj.obj U :=
              ((limit.π S (op n)).right.hom.app U).hom
            let b' : (limit S).right.obj.obj U := b
            change p ((limit S).hom.hom.app U a * b') =
              (S.obj (op n)).hom.hom.app U a * p b'
            rw [map_mul]
            congr 1
            exact congrArg (fun f ↦ f.hom.app U a) (Under.w (limit.π S (op n))) }
      naturality := by
        intro U V g
        ext b
        exact adicProjection_restrict J A S n g b }

private theorem adicModuleFactor {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A] (I : Ideal A)
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    (n : ℕ)
    (hsurj : ∀ U : Cᵒᵖ, Function.Surjective (adicProjection J A S n U))
    (hker : ∀ (U : Cᵒᵖ) (b : adicLimit J A S U),
      adicProjection J A S n U b = 0 ↔
        b ∈ (I ^ (n + 1)).map (algebraMap A (adicLimit J A S U)))
    (N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A))))
    (f : adicUnderlyingModule J A (limit S) ⟶ N)
    (hf : ∀ (U : Cᵒᵖ) (a : ↥(I ^ (n + 1))) (b : adicLimit J A S U),
      f.val.app U (algebraMap A (adicLimit J A S U) a * b) = 0) :
    ∃! g : adicUnderlyingModule J A (S.obj (op n)) ⟶ N,
      adicProjectionModule J A S n ≫ g = f := by
  classical
  let q := adicProjectionModule J A S n
  have hk (U : Cᵒᵖ) : LinearMap.ker (q.val.app U).hom ≤
      LinearMap.ker (f.val.app U).hom := by
    intro b hb
    have hb' := (hker U b).mp hb
    change f.val.app U b = 0
    change b ∈ Ideal.span (algebraMap A (adicLimit J A S U) '' (↑(I ^ (n + 1)) : Set A)) at hb'
    have hz : ∀ x ∈ Ideal.span (algebraMap A (adicLimit J A S U) '' (↑(I ^ (n + 1)) : Set A)),
        ∀ c : adicLimit J A S U, f.val.app U (x * c) = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        exact fun c ↦ hf U ⟨a, ha⟩ c
      | zero => intro c; simp only [zero_mul, map_zero]
      | add x y hx hy ihx ihy =>
        intro c
        rw [add_mul, map_add, ihx c, ihy c, add_zero]
      | smul c x hx ih =>
        intro d
        change f.val.app U ((c * x) * d) = 0
        rw [mul_comm c x, mul_assoc]
        exact ih (c * d)
    simpa only [mul_one] using hz b hb' 1
  let gU (U : Cᵒᵖ) : (adicUnderlyingModule J A (S.obj (op n))).val.obj U →ₗ[
      ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)).obj.obj U] N.val.obj U :=
    ((LinearMap.ker (q.val.app U).hom).liftQ (f.val.app U).hom (hk U)).comp
      ((q.val.app U).hom.quotKerEquivOfSurjective (hsurj U)).symm.toLinearMap
  have hg (U : Cᵒᵖ) (b : adicLimit J A S U) :
      gU U (q.val.app U b) = f.val.app U b := by
    simp only [gU, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  let g : adicUnderlyingModule J A (S.obj (op n)) ⟶ N :=
    { val :=
        { app := fun U ↦ ModuleCat.ofHom
            (X := (adicUnderlyingModule J A (S.obj (op n))).val.obj U)
            (Y := N.val.obj U) (gU U)
          naturality := by
            intro U V k
            ext b
            obtain ⟨b, rfl⟩ := hsurj U b
            change gU V ((adicUnderlyingModule J A (S.obj (op n))).val.map k
              (q.val.app U b)) = N.val.map k (gU U (q.val.app U b))
            rw [← PresheafOfModules.naturality_apply q.val, hg, hg]
            exact PresheafOfModules.naturality_apply f.val k b } }
  refine ⟨g, ?_, ?_⟩
  · ext U b
    exact hg U b
  · intro g' hg'
    ext U b
    obtain ⟨b, rfl⟩ := hsurj U b
    have h := congrArg (fun k ↦ k.val.app U b) hg'
    exact h.trans (hg U b).symm

/-- Flatness, finite tensor comparisons and canonical quotient projections for an adic
algebra-sheaf tower. Positive exponents are indexed by n : ℕ, meaning n+1.
Source: Stacks Project, sites-modules.tex, Tag 093M, generalized algebra-tower argument;
more-algebra.tex, Tag 0912 (auxiliary; not a blueprint node).

Proof:
1. Evaluate the sheaf limit on U. Apply `ModuleCat.limit_flat_of_flat_quotients` to
   the section module tower, using the quotient scalar towers, flatness and surjectivity.
   Swap the two tensor factors to obtain the stated projection formula. On pure tensors
   restrictions and maps of finite modules commute with every projection.
2. Regard the limit as a module over the constant presheaf A. Sectionwise flat tensoring
   preserves kernels and finite products (including the empty product), hence finite
   limits. Apply `PresheafOfModules.isFlat_sheafification_obj` to obtain flatness over
   the constant ring sheaf. This does not require enough points or flatness over R(U).
3. Apply the finite tensor comparison to A/I^(n+1). The reduction hypotheses identify
   the target with the eventually constant system S_min(m,n), whose limit is S_n.
   The quotient-tensor equivalence sends b tensor a to the class of ab, so the resulting
   ring isomorphism is induced by the original projection.
4. Since A is Noetherian, I^(n+1) has finitely many generators. The cokernel of their
   action has presheaf sections B(U)/I^(n+1)B(U). The sectionwise quotient is already
   the sheaf S_n, so sheafification identifies this with the sheaf-module cokernel.
5. The quotient isomorphisms commute with every transition: both composites on a
   representative b give its n-th projection. Identity and composite transitions follow
   from the strict functor laws. -/
theorem sectionwise_adic_algebra_limit
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (S : ℕᵒᵖ ⥤ Under ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
    [∀ (n : ℕ) (U : Cᵒᵖ), Module (A ⧸ I ^ (n + 1)) (adicTerm J A S n U)]
    [∀ (n : ℕ) (U : Cᵒᵖ), IsScalarTower A (A ⧸ I ^ (n + 1)) (adicTerm J A S n U)]
    (hflat : ∀ (n : ℕ) (U : Cᵒᵖ),
      Module.Flat (A ⧸ I ^ (n + 1)) (adicTerm J A S n U))
    (hsurj : ∀ (n : ℕ) (U : Cᵒᵖ),
      Function.Surjective (adicTransition J A S (n + 1) n (Nat.le_succ n) U))
    (hred : ∀ (m n : ℕ) (U : Cᵒᵖ),
      ∃ e : TensorProduct A (adicTerm J A S m U) (A ⧸ I ^ (n + 1)) ≃ₗ[A]
        adicTerm J A S (min m n) U,
        ∀ (b : adicTerm J A S m U) (a : A),
          e (b ⊗ₜ[A] Ideal.Quotient.mk _ a) =
            a • adicTransition J A S m (min m n) (Nat.min_le_left m n) U b) :
    SheafOfModules.IsFlatOnSite
      ((SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map (limit S).hom)).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (limit S).right))) ∧
    (∀ (U : Cᵒᵖ) (F : Type w) [AddCommGroup F] [Module A F] [Module.Finite A F],
      Function.Injective (adicTensorComparison J A S U F) ∧
      (∀ x : ∀ n : ℕ, TensorProduct A (adicTerm J A S n U) F,
        (∀ n : ℕ,
          (adicTransition J A S (n + 1) n (Nat.le_succ n) U).toLinearMap.rTensor F
            (x (n + 1)) = x n) ↔
        ∃ y, adicTensorComparison J A S U F y = x)) ∧
    (∀ (U : Cᵒᵖ) (F G : Type w) [AddCommGroup F] [AddCommGroup G]
      [Module A F] [Module A G] [Module.Finite A F] [Module.Finite A G]
      (f : F →ₗ[A] G) (x : TensorProduct A (adicLimit J A S U) F) (n : ℕ),
      adicTensorComparison J A S U G (f.lTensor (adicLimit J A S U) x) n =
        f.lTensor (adicTerm J A S n U) (adicTensorComparison J A S U F x n)) ∧
    (∀ (F : Type w) [AddCommGroup F] [Module A F] [Module.Finite A F]
      (U V : Cᵒᵖ) (g : U ⟶ V),
      ∃ r : adicLimit J A S U →ₗ[A] adicLimit J A S V,
        ∃ t : ∀ n : ℕ, adicTerm J A S n U →ₗ[A] adicTerm J A S n V,
          (∀ b, r b = (limit S).right.obj.map g b) ∧
          (∀ n b, t n b = (S.obj (op n)).right.obj.map g b) ∧
          ∀ (x : TensorProduct A (adicLimit J A S U) F) (n : ℕ),
            adicTensorComparison J A S V F (r.rTensor F x) n =
              (t n).rTensor F (adicTensorComparison J A S U F x n)) ∧
    (∀ n : ℕ, ∃ q : adicUnderlyingModule J A (limit S) ⟶
        adicUnderlyingModule J A (S.obj (op n)),
      (∀ (U : Cᵒᵖ) (b : adicLimit J A S U),
        q.val.app U b = adicProjection J A S n U b) ∧
      ∀ (N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A))))
        (f : adicUnderlyingModule J A (limit S) ⟶ N),
        (∀ (U : Cᵒᵖ) (a : ↥(I ^ (n + 1))) (b : adicLimit J A S U),
          f.val.app U (algebraMap A (adicLimit J A S U) a * b) = 0) →
        ∃! g : adicUnderlyingModule J A (S.obj (op n)) ⟶ N, q ≫ g = f) ∧
    (∃ e : ∀ (n : ℕ) (U : Cᵒᵖ),
      (adicLimit J A S U ⧸ (I ^ (n + 1)).map
        (algebraMap A (adicLimit J A S U))) ≃+* adicTerm J A S n U,
      (∀ (n : ℕ) (U : Cᵒᵖ) (b : adicLimit J A S U),
        e n U (Ideal.Quotient.mk _ b) = adicProjection J A S n U b) ∧
      (∀ (n : ℕ) (U V : Cᵒᵖ) (g : U ⟶ V) (b : adicLimit J A S U),
        e n V (Ideal.Quotient.mk _ ((limit S).right.obj.map g b)) =
          (S.obj (op n)).right.obj.map g (e n U (Ideal.Quotient.mk _ b))) ∧
      ∀ (m n : ℕ) (h : n ≤ m) (U : Cᵒᵖ) (b : adicLimit J A S U),
        adicTransition J A S m n h U (e m U (Ideal.Quotient.mk _ b)) =
          e n U (Ideal.Quotient.mk _ b)) := by
  classical
  obtain ⟨hsection, htensor⟩ := adicSectionwiseFlatTensor J A I S hflat hsurj
  have hsurj' := adicProjection_surjective J A S hsurj
  have hker := adicProjection_mem_ker_iff J A I S
    (fun U n ↦ ((adicSectionwiseFlatTensor.{u, u} J A I S hflat hsurj).2 U
      (A ⧸ I ^ (n + 1))).1) hred
  refine ⟨adicSheafFlat J A (limit S) hsection, htensor, ?_, ?_, ?_, ?_⟩
  · intro U F G _ _ _ _ _ _ f x n
    induction x using TensorProduct.inductionOn with
    | tmul b f => rfl
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  · intro F _ _ _ U V g
    refine ⟨(adicRestriction J A (limit S) g).toLinearMap,
      fun n ↦ (adicRestriction J A (S.obj (op n)) g).toLinearMap,
      (fun b ↦ rfl), (fun n b ↦ rfl), ?_⟩
    intro x n
    induction x using TensorProduct.inductionOn with
    | tmul b f =>
      change adicProjection J A S n V ((adicRestriction J A (limit S) g) b) ⊗ₜ[A] f =
        (adicRestriction J A (S.obj (op n)) g) (adicProjection J A S n U b) ⊗ₜ[A] f
      exact congrArg (fun z : adicTerm J A S n V ↦ z ⊗ₜ[A] f)
        (adicProjection_restrict J A S n g b)
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  · intro n
    exact ⟨adicProjectionModule J A S n, fun U b ↦ rfl,
      fun N f hf ↦ adicModuleFactor J A I S n (hsurj' n) (hker n) N f hf⟩
  · have heq (n : ℕ) (U : Cᵒᵖ) :
        (I ^ (n + 1)).map (algebraMap A (adicLimit J A S U)) =
          RingHom.ker (adicProjection J A S n U).toRingHom := by
      ext b
      exact (hker n U b).symm
    let e (n : ℕ) (U : Cᵒᵖ) :=
      (Ideal.quotEquivOfEq (heq n U)).trans
        ((adicProjection J A S n U).toRingHom.quotientKerEquivOfSurjective (hsurj' n U))
    have he (n : ℕ) (U : Cᵒᵖ) (b : adicLimit J A S U) :
        e n U (Ideal.Quotient.mk _ b) = adicProjection J A S n U b := by
      exact RingHom.quotientKerEquivOfSurjective_apply_mk (hsurj' n U) b
    refine ⟨e, he, ?_, ?_⟩
    · intro n U V g b
      rw [he, he]
      exact adicProjection_restrict J A S n g b
    · intro m n h U b
      rw [he, he]
      exact adicProjection_transition J A S m n h U b

end CategoryTheory
