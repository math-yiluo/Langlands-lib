/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.CommMonoidOperationsDescent

/-!
# Descent of the commutative monoid operations

Source: blueprint proposition-jacobian-over-ground-field--1, multiplication and unit step;
Stacks Project, Descent, Tag 02W0.
(blueprint: lem-pd-comm-monoid-operations-descent).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

private noncomputable def projectPoint
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X} {V₀ : Over Y}
    (qV : V.left ⟶ V₀.left) (hqV : IsPullback qV V.hom V₀.hom p)
    {T : Scheme.{u}} (f : T ⟶ X) (a : Over.mk f ⟶ V) : Over.mk (f ≫ p) ⟶ V₀ :=
  (Over.map p).map a ≫ Over.homMk qV hqV.w

private noncomputable def localPoint
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X} {V₀ : Over Y}
    (qV : V.left ⟶ V₀.left) (hqV : IsPullback qV V.hom V₀.hom p)
    (A : Over Y) (a : A ⟶ V₀) : Over.mk (pullback.snd A.hom p) ⟶ V :=
  Over.homMk (hqV.lift (pullback.fst A.hom p ≫ a.left) (pullback.snd A.hom p)
    (by rw [Category.assoc, Over.w a, pullback.condition]))
    (hqV.lift_snd _ _ _)

private theorem project_localPoint
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X} {V₀ : Over Y}
    (qV : V.left ⟶ V₀.left) (hqV : IsPullback qV V.hom V₀.hom p)
    (A : Over Y) (a : A ⟶ V₀) :
    projectPoint qV hqV _ (localPoint qV hqV A a) =
      (Over.homMk (pullback.fst A.hom p) pullback.condition :
        Over.mk (pullback.snd A.hom p ≫ p) ⟶ A) ≫ a := by
  apply Over.OverMorphism.ext
  exact hqV.lift_fst _ _ _

private theorem local_hom_ext
    {X Y : Scheme.{u}} (p : X ⟶ Y) [Flat p] [Surjective p] [QuasiCompact p]
    {A B : Over Y} (a b : A ⟶ B)
    (h : (Over.homMk (pullback.fst A.hom p) pullback.condition :
      Over.mk (pullback.snd A.hom p ≫ p) ⟶ A) ≫ a =
      (Over.homMk (pullback.fst A.hom p) pullback.condition :
      Over.mk (pullback.snd A.hom p ≫ p) ⟶ A) ≫ b) : a = b := by
  apply Over.OverMorphism.ext
  apply (cancel_epi (pullback.fst A.hom p)).mp
  exact congrArg (fun k => k.left) h

/-- Multiplication and the unit descend to a commutative monoid structure, before the
inverse is descended. Source: blueprint proposition-jacobian-over-ground-field--1, multiplication
and unit step; Stacks Project, Tag 02W0.
(blueprint: lem-pd-comm-monoid-operations-descent).

Proof: First descend multiplication and the unit as morphisms using
`exists_raw_monoid_operations_of_effective_projection`
(lem-pd-raw-monoid-operations-descent). For any Y-scheme A, the fpqc projection
A times_Y X to A is an epimorphism. The cartesian square hqV lifts each point of V₀
on this cover uniquely to V. Apply the two operation identities to these lifts:
associativity, the two unit laws, and commutativity on V give the corresponding
pointwise equations on V₀ after precomposition with the cover. Epimorphism
cancellation proves them on A. Specializing to the universal points of the products
constructs the three fields of MonObj and the commutativity field of IsCommMonObj.
The two requested identities are the factorization identities already proved for
the operations. No inverse is used. Empty schemes introduce no exception, since
all steps use pullback universal properties and epimorphism cancellation. -/
theorem exists_commMonObj_of_effective_projection
    {X Y : Scheme.{u}} {p : X ⟶ Y} [Flat p] [Surjective p] [QuasiCompact p]
    {V : Over X} [MonObj V] [IsCommMonObj V] (D : Over.DescentDatum p V)
    {V₀ : Over Y} (qV : V.left ⟶ V₀.left) (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
      (a : Over.mk f₁ ⟶ V), (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (hμ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
      (a b : Over.mk f₁ ⟶ V), D.transport f₁ f₂ h (lift a b ≫ μ[V]) =
        lift (D.transport f₁ f₂ h a) (D.transport f₁ f₂ h b) ≫ μ[V])
    (hη : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p),
      D.transport f₁ f₂ h (toUnit _ ≫ η[V]) = toUnit _ ≫ η[V]) :
    ∃ M : MonObj V₀, letI := M;
      IsCommMonObj V₀ ∧
      (∀ {T : Scheme.{u}} (f : T ⟶ X) (a b : Over.mk f ⟶ V),
        (lift a b ≫ μ[V]).left ≫ qV =
          (lift (Over.homMk (a.left ≫ qV) (by
            simp only [Over.mk_hom, Category.assoc, hqV.w]
            rw [← Category.assoc, Over.w a]
            rfl) : Over.mk (f ≫ p) ⟶ V₀)
            (Over.homMk (b.left ≫ qV) (by
            simp only [Over.mk_hom, Category.assoc, hqV.w]
            rw [← Category.assoc, Over.w b]
            rfl) : Over.mk (f ≫ p) ⟶ V₀) ≫ μ[V₀]).left) ∧
      (∀ {T : Scheme.{u}} (f : T ⟶ X),
        (toUnit (Over.mk f) ≫ η[V]).left ≫ qV =
          (toUnit (Over.mk (f ≫ p)) ≫ η[V₀]).left) := by
  obtain ⟨m, e, hm, he⟩ :=
    exists_raw_monoid_operations_of_effective_projection D qV hqV hDV hμ hη
  have hm' : ∀ {T : Scheme.{u}} (f : T ⟶ X) (a b : Over.mk f ⟶ V),
      projectPoint qV hqV f (lift a b ≫ μ[V]) =
        lift (projectPoint qV hqV f a) (projectPoint qV hqV f b) ≫ m := hm
  have he' : ∀ {T : Scheme.{u}} (f : T ⟶ X),
      projectPoint qV hqV f (toUnit _ ≫ η[V]) = toUnit _ ≫ e := he
  have ha : ∀ (A : Over Y) (a b c : A ⟶ V₀),
      lift (lift a b ≫ m) c ≫ m = lift a (lift b c ≫ m) ≫ m := by
    intro A a b c
    apply local_hom_ext p
    have h := congrArg (projectPoint qV hqV (pullback.snd A.hom p))
      (MonObj.lift_lift_assoc (localPoint qV hqV A a)
        (localPoint qV hqV A b) (localPoint qV hqV A c))
    simp only [hm', project_localPoint] at h
    simpa only [Category.assoc, comp_lift_assoc] using h
  have hl : ∀ (A : Over Y) (a : A ⟶ V₀), lift (toUnit A ≫ e) a ≫ m = a := by
    intro A a
    apply local_hom_ext p
    have h := congrArg (projectPoint qV hqV (pullback.snd A.hom p))
      (MonObj.lift_comp_one_left (toUnit _) (localPoint qV hqV A a))
    simp only [hm', he', project_localPoint] at h
    simpa only [Category.assoc, comp_lift_assoc, comp_toUnit_assoc] using h
  have hr : ∀ (A : Over Y) (a : A ⟶ V₀), lift a (toUnit A ≫ e) ≫ m = a := by
    intro A a
    apply local_hom_ext p
    have h := congrArg (projectPoint qV hqV (pullback.snd A.hom p))
      (MonObj.lift_comp_one_right (localPoint qV hqV A a) (toUnit _))
    simp only [hm', he', project_localPoint] at h
    simpa only [Category.assoc, comp_lift_assoc, comp_toUnit_assoc] using h
  have hc : ∀ (A : Over Y) (a b : A ⟶ V₀), lift a b ≫ m = lift b a ≫ m := by
    intro A a b
    apply local_hom_ext p
    have hab : lift (localPoint qV hqV A a) (localPoint qV hqV A b) ≫ μ[V] =
        lift (localPoint qV hqV A b) (localPoint qV hqV A a) ≫ μ[V] := by
      exact (lift_braiding_hom_assoc _ _ μ[V]).symm.trans
        (congrArg (fun k => lift (localPoint qV hqV A b)
          (localPoint qV hqV A a) ≫ k) (IsCommMonObj.mul_comm V))
    have h := congrArg (projectPoint qV hqV (pullback.snd A.hom p)) hab
    simp only [hm', project_localPoint] at h
    simpa only [Category.assoc, comp_lift_assoc] using h
  let M : MonObj V₀ :=
    { one := e
      mul := m
      one_mul := by
        rw [← Category.id_comp (e ▷ V₀ ≫ m), ← lift_fst_snd]
        simp only [lift_whiskerRight_assoc, leftUnitor_hom]
        simpa only [toUnit_unique (fst _ _) (toUnit _)] using hl _ (snd _ _)
      mul_one := by
        rw [← Category.id_comp (V₀ ◁ e ≫ m), ← lift_fst_snd]
        simp only [lift_whiskerLeft_assoc, rightUnitor_hom]
        simpa only [toUnit_unique (snd _ _) (toUnit _)] using hr _ (fst _ _)
      mul_assoc := by
        have h := ha ((V₀ ⊗ V₀) ⊗ V₀) (fst _ _ ≫ fst _ _)
          (fst _ _ ≫ snd _ _) (snd _ _)
        have hi : lift (lift (fst _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _)) (snd _ _) =
            𝟙 ((V₀ ⊗ V₀) ⊗ V₀) := by
          rw [← comp_lift, lift_fst_snd, Category.comp_id, lift_fst_snd]
        rw [← Category.id_comp (m ▷ V₀ ≫ m), ← Category.id_comp
          ((α_ V₀ V₀ V₀).hom ≫ V₀ ◁ m ≫ m), ← hi]
        simpa only [Category.assoc, lift_whiskerRight_assoc,
          lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc] using h }
  let _ := M
  refine ⟨M, ?_, ?_, ?_⟩
  · constructor
    change (β_ V₀ V₀).hom ≫ m = m
    have h := hc (V₀ ⊗ V₀) (snd _ _) (fst _ _)
    simpa only [← lift_braiding_hom_assoc, lift_fst_snd, Category.id_comp] using h
  · intro T f a b
    exact congrArg (fun k => k.left) (hm f a b)
  · intro T f
    exact congrArg (fun k => k.left) (he f)

end CategoryTheory.Over.DescentDatum
