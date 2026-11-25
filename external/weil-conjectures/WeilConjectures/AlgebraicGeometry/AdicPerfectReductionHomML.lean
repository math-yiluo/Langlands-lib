/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.CofilteredSystem
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import WeilConjectures.AlgebraicGeometry.AdicPerfectHomCohomologyComparison
import WeilConjectures.CategoryTheory.FiniteTripleMittagLeffler
import Mathlib.Data.Int.Interval

/-! # Mittag-Leffler for perfect finite-reduction Hom

Source: Stacks Project, Tags 09C5 and 09C6.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

private theorem sequence_naturality
    {F : ℕᵒᵖ ⥤ Type u} {G : ℕᵒᵖ ⥤ Type v}
    (e : ∀ n : ℕ, F.obj (op n) → G.obj (op n))
    (he : ∀ (n : ℕ) (x : F.obj (op (n + 1))),
      e n (F.map (homOfLE (Nat.le_succ n)).op x) =
        G.map (homOfLE (Nat.le_succ n)).op (e (n + 1) x))
    {n m : ℕᵒᵖ} (f : m ⟶ n) (x : F.obj m) :
    e n.unop (F.map f x) = G.map f (e m.unop x) := by
  obtain ⟨n⟩ := n
  obtain ⟨m⟩ := m
  have hnm : n ≤ m := leOfHom f.unop
  obtain rfl : f = (homOfLE hnm).op := Subsingleton.elim _ _
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have hf : (homOfLE (hnm.trans (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
    simp only [hf, Functor.map_comp, types_comp_apply]
    rw [ih, he]

private theorem homTerm_finite
    {A : Type w} [CommRing A] [IsNoetherianRing A]
    (P : CochainComplex (ModuleCat.{w} A) ℤ) (c d : ℤ)
    (hc : P.IsStrictlyGE c) (hd : P.IsStrictlyLE d)
    (hp : ∀ i : ℤ, Module.Finite A (P.X i)) (q : ℤ) :
    Module.Finite A ((CochainComplex.moduleHomComplex P P).X q) := by
  classical
  let φ : CochainComplex.HomComplex.Cochain P P q →ₗ[A]
      (∀ i : Set.Icc c d, P.X i.val ⟶ P.X (i.val + q)) :=
    { toFun := fun z i ↦ z.v i.val (i.val + q) rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hinj : Function.Injective φ := by
    intro z w h
    apply CochainComplex.HomComplex.Cochain.ext
    intro i j hij
    subst j
    by_cases hi : i ∈ Set.Icc c d
    · exact congrFun h ⟨i, hi⟩
    · have hz : IsZero (P.X i) := by
        by_cases hil : i < c
        · exact P.isZero_of_isStrictlyGE c i hil
        · exact P.isZero_of_isStrictlyLE d i (by simp only [Set.mem_Icc] at hi; omega)
      exact hz.eq_of_src _ _
  have hfin : ∀ i : Set.Icc c d, Module.Finite A (P.X i.val ⟶ P.X (i.val + q)) := by
    intro i
    have := hp i.val
    have := hp (i.val + q)
    exact Module.Finite.equiv (ModuleCat.homLinearEquiv (S := A)).symm
  exact Module.Finite.of_injective φ hinj

private theorem functor_conjugate_id {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (Z : C) {W : D} (e : F.obj Z ≅ W) :
    e.inv ≫ F.map (𝟙 Z) ≫ e.hom = 𝟙 W := by
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

private theorem homStep_id
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (T : AdicResidueLocalDerived.{u, v} X J U) (n : ℕ) :
    adicResidueHomStep X J U T T n (𝟙 _) = 𝟙 _ := by
  let V := (coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U
  let τ := V.map (ConstantCompletion.transition
    (coefficientProEtaleModelTopology.{u, v} X) A J n)
  exact functor_conjugate_id (ConstantCompletion.extend τ)
    ((adicResidueLocalReduction X J U (n + 1)).obj T)
    ((adicResidueLocalReductionStep X J U n).app T)

private theorem homStep_comp
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (T M N : AdicResidueLocalDerived.{u, v} X J U) (n : ℕ)
    (a : (adicResidueLocalReduction X J U (n + 1)).obj T ⟶
      (adicResidueLocalReduction X J U (n + 1)).obj M)
    (b : (adicResidueLocalReduction X J U (n + 1)).obj M ⟶
      (adicResidueLocalReduction X J U (n + 1)).obj N) :
    adicResidueHomStep X J U T N n (a ≫ b) =
      adicResidueHomStep X J U T M n a ≫ adicResidueHomStep X J U M N n b := by
  simp [adicResidueHomStep, Category.assoc]

private theorem homTower_map_id
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (T : AdicResidueLocalDerived.{u, v} X J U)
    {n m : ℕᵒᵖ} (f : m ⟶ n) :
    (adicResidueHomTower X J U T T).map f (𝟙 _) = 𝟙 _ := by
  obtain ⟨n⟩ := n
  obtain ⟨m⟩ := m
  have hnm : n ≤ m := leOfHom f.unop
  obtain rfl : f = (homOfLE hnm).op := Subsingleton.elim _ _
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have he : (homOfLE (hnm.trans (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
    rw [he, Functor.map_comp]
    simp only [types_comp_apply]
    have hs : (adicResidueHomTower X J U T T).map
        (homOfLE (Nat.le_succ m)).op (𝟙 _) = 𝟙 _ := by
      dsimp only [adicResidueHomTower]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact homStep_id X J U T m
    rw [hs, ih]

private theorem homTower_map_comp
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (T M N : AdicResidueLocalDerived.{u, v} X J U)
    {n m : ℕᵒᵖ} (f : m ⟶ n)
    (a : (adicResidueHomTower X J U T M).obj m)
    (b : (adicResidueHomTower X J U M N).obj m) :
    (adicResidueHomTower X J U T N).map f (a ≫ b) =
      (adicResidueHomTower X J U T M).map f a ≫
        (adicResidueHomTower X J U M N).map f b := by
  obtain ⟨n⟩ := n
  obtain ⟨m⟩ := m
  have hnm : n ≤ m := leOfHom f.unop
  obtain rfl : f = (homOfLE hnm).op := Subsingleton.elim _ _
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have he : (homOfLE (hnm.trans (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
    simp only [he, Functor.map_comp, types_comp_apply]
    have hs : (adicResidueHomTower X J U T N).map
        (homOfLE (Nat.le_succ m)).op (a ≫ b) =
        (adicResidueHomTower X J U T M).map (homOfLE (Nat.le_succ m)).op a ≫
        (adicResidueHomTower X J U M N).map (homOfLE (Nat.le_succ m)).op b := by
      dsimp only [adicResidueHomTower]
      rw [Functor.ofOpSequence_map_homOfLE_succ,
        Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
      exact homStep_comp X J U T M N m a b
    rw [hs]
    exact ih _ _

private def homTower_mapIso
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (T M : AdicResidueLocalDerived.{u, v} X J U)
    {n m : ℕᵒᵖ} (f : m ⟶ n)
    (e : (adicResidueLocalReduction X J U m.unop).obj T ≅
      (adicResidueLocalReduction X J U m.unop).obj M) :
    (adicResidueLocalReduction X J U n.unop).obj T ≅
      (adicResidueLocalReduction X J U n.unop).obj M where
  hom := (adicResidueHomTower X J U T M).map f e.hom
  inv := (adicResidueHomTower X J U M T).map f e.inv
  hom_inv_id := by
    rw [← homTower_map_comp, e.hom_inv_id, homTower_map_id]
  inv_hom_id := by
    rw [← homTower_map_comp, e.inv_hom_id, homTower_map_id]

private theorem homTower_finiteComparison
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (T M : AdicResidueLocalDerived.{u, v} X J U)
    (he : ∀ n : ℕ, Nonempty ((adicResidueLocalReduction X J U n).obj T ≅
      (adicResidueLocalReduction X J U n).obj M)) :
    Functor.FiniteTripleRangeComparison (adicResidueHomTower X J U T M)
      (adicResidueHomTower X J U T T) := by
  intro n m t f g
  obtain ⟨e⟩ := he t.unop
  let em := homTower_mapIso X J U T M g e
  let en := homTower_mapIso X J U T M (g ≫ f) e
  have hbij : ∀ {n : ℕ} (a : (adicResidueLocalReduction X J U n).obj T ≅
      (adicResidueLocalReduction X J U n).obj M),
      Function.Bijective (fun x : (adicResidueHomTower X J U T M).obj (op n) ↦
        x ≫ a.inv) := by
    intro n a
    constructor
    · intro x y h
      have h' := congrArg (fun k ↦ k ≫ a.hom) h
      simpa only [Category.assoc, a.inv_hom_id, Category.comp_id] using h'
    · intro x
      refine ⟨x ≫ a.hom, ?_⟩
      simp only [Category.assoc, a.hom_inv_id, Category.comp_id]
  refine ⟨(fun x ↦ x ≫ en.inv), (fun x ↦ x ≫ em.inv), (fun x ↦ x ≫ e.inv),
    hbij en, hbij em, hbij e, ?_, ?_⟩
  · intro x
    rw [homTower_map_comp]
    change _ ≫ (adicResidueHomTower X J U M T).map (g ≫ f) e.inv =
      _ ≫ (adicResidueHomTower X J U M T).map f
        ((adicResidueHomTower X J U M T).map g e.inv)
    rw [Functor.map_comp]
    rfl
  · intro x
    exact (homTower_map_comp X J U T M T (g ≫ f) x e.inv).symm

/-- The finite-reduction Hom tower from a constant perfect local model is Mittag-Leffler.
Source: Stacks Project, proetale.tex, Tags 09C5 and 09C6, the dual-complex calculation.
(auxiliary; not a blueprint node).

Proof: at any triple of indices t >= m >= n, choose only a level-t isomorphism
from the fixed perfect model to M. Scalar extension and the prescribed conjugations
preserve identities and composition; reduce that isomorphism to m and n. Postcomposing
with its inverses identifies both Hom transition images with the endomorphism images
of the fixed model, using a common bijection at n. These finite markings require no
infinite compatible choice. The quotient Hom/cohomology comparison identifies the
model's endomorphism tower with constant-module sections of H^0 of the quotients of
its algebraic Hom complex. Its degree-one term is finite: restrict cochains to the
finite support interval of P and embed them in the finite product of finite linear-Hom
modules. Artin--Rees gives Mittag--Leffler for this quotient-cohomology tower, and exact
constant-module sections preserve it. Transfer stable images through the two finite
comparisons. Neither the affine hypothesis nor completeness of M is needed on this
route; the original statement and its hypotheses are retained. -/
theorem adicResidueHomTower_mittagLeffler
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (_hAffine : IsAffine
      ((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).obj U).left)
    (_hU : AdicResidueSliceWeaklyContractible.{u, v} X U)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) (c d : ℤ)
    (_hc : P.IsStrictlyGE c) (_hd : P.IsStrictlyLE d)
    (_hP : ∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q))
    (M : AdicResidueLocalDerived.{u, v} X J U)
    (_hM : CategoryTheory.ConstantCompletion.IsComplete
      (adicResidueLocalProjection.{u, v} X J U 0) M)
    (_hfinite : ∀ n : ℕ, Nonempty
      ((adicResidueLocalReduction.{u, v} X J U n).obj
        ((adicResidueRestriction
      (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X)
        A J) U).obj (adicResidueConstantPerfect.{u, v} X J P)) ≅
        (adicResidueLocalReduction.{u, v} X J U n).obj M)) :
    (adicResidueHomTower.{u, v} X J U
      ((adicResidueRestriction
      (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X)
        A J) U).obj (adicResidueConstantPerfect.{u, v} X J P)) M).IsMittagLeffler := by
  let T := (adicResidueRestriction
    (ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A J) U).obj
      (adicResidueConstantPerfect.{u, v} X J P)
  have hEnd : (adicResidueHomTower X J U T T).IsMittagLeffler := by
    obtain ⟨e, he⟩ := adicPerfectHomCohomologyComparison X J U _hU P P
      c d c d _hc _hd _hc _hd _hP _hP
    have hn : ∀ {n m : ℕᵒᵖ} (f : m ⟶ n)
        (x : (adicResidueHomTower X J U T T).obj m),
        e n.unop ((adicResidueHomTower X J U T T).map f x) =
          (adicPerfectHomCohomologyTower X J U P P).map f (e m.unop x) := by
      apply sequence_naturality (fun n ↦ (e n).toFun)
      intro n x
      dsimp only [adicResidueHomTower]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      change e n (adicResidueHomStep X J U T T n x) = _
      exact he n x
    apply Functor.isMittagLeffler_of_finiteTripleRangeComparison
      (U := adicPerfectHomCohomologyTower X J U P P)
    · intro n m t f g
      exact ⟨e n.unop, e m.unop, e t.unop, (e n.unop).bijective,
        (e m.unop).bijective, (e t.unop).bijective, hn f, hn (g ≫ f)⟩
    · let F := AdicCohomology.sections (R := A)
        ((coefficientProEtaleModelTopology.{u, v} X).over U) (Over.mk (𝟙 U))
      have : F.PreservesHomology := AdicCohomology.sections_preservesHomology _ _
      have : Module.Finite A ((CochainComplex.moduleHomComplex P P).sc 0).X₃ :=
        homTerm_finite P c d _hc _hd (fun i ↦ (_hP i).1) _
      exact AdicCohomology.map_isMittagLeffler _ F
        (AdicCohomology.isMittagLeffler J ((CochainComplex.moduleHomComplex P P).sc 0))
  exact Functor.isMittagLeffler_of_finiteTripleRangeComparison
    (homTower_finiteComparison X J U T M _hfinite) hEnd

end AlgebraicGeometry.Scheme
