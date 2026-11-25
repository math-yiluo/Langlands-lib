/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Data.Int.Interval

/-! # Finite source decomposition

Source: Stacks Project, Tags 08DQ and 08DM.
(blueprint: lem-pc-ordinary-evaluation-source-biproduct).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
attribute [local instance] localEvaluationPreadditive

private lemma localHom_isZero (X : Scheme.{u}) (U : X.Opens)
    (A B : localEvaluationModules X U) (h : IsZero A ∨ IsZero B) :
    IsZero (SheafOfModules.homObj (R := X.sheaf.over U) A B) := by
  rw [IsZero.iff_id_eq_zero]
  apply (SheafOfModules.tensorHomEquiv (R := X.sheaf.over U) A _ B).symm.injective
  rcases h with hA | hB
  · exact ((tensorRight _).map_isZero hA).eq_of_src _ _
  · exact hB.eq_of_tgt _ _

private lemma localDual_isZero (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ) (a b q : ℤ)
    (hbounded : ∀ r : ℤ, r < a ∨ b < r → IsZero (P.X r))
    (hq : -q < a ∨ b < -q) : IsZero ((localEvaluationDual X U P).X q) := by
  have hπ := (Classical.choose_spec
    (homComplex_projections_exists (R := X.sheaf.over U))).1 P
      (localEvaluationUnit X U) q
  rw [IsZero.iff_id_eq_zero]
  apply hπ.some.hom_ext
  intro j
  have hz : IsZero (SheafOfModules.homObj (R := X.sheaf.over U)
      (P.X j.as) ((localEvaluationUnit X U).X (j.as + q))) := by
    apply localHom_isZero
    by_cases hj : j.as + q = 0
    · left
      have he : j.as = -q := by omega
      exact hbounded j.as (by simpa only [he] using hq)
    · right
      exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (𝟙_ (localEvaluationModules X U)) (j.as + q) hj
  exact hz.eq_of_tgt _ _

private lemma biproduct_transport {C : Type*} [Category C] [HasZeroMorphisms C]
    {I : Type*} (S : I → C) [HasBiproduct S] {i j : I} (hij : i = j)
    (h : S i = S j) : eqToHom h ≫ biproduct.ι S j = biproduct.ι S i := by
  subst j
  simp

private lemma finiteTensorBiproduct {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasFiniteBiproducts C]
    (F D : CochainComplex C ℤ) [F.HasMapBifunctor D (curriedTensor C)]
    (a b n : ℤ) (hbounded : ∀ q : ℤ, -q < a ∨ b < -q → IsZero (D.X q)) :
    ∃ e : (⨁ fun r : ↥(Finset.Icc a b) ↦ F.X (r.val + n) ⊗ D.X (-r.val)) ≅
        (CochainComplex.mapBifunctor F D (curriedTensor C)).X n,
      ∀ r : ↥(Finset.Icc a b), biproduct.ι _ r ≫ e.hom =
        HomologicalComplex.ιMapBifunctor F D (curriedTensor C) (.up ℤ)
          (r.val + n) (-r.val) n (by change r.val + n + -r.val = n; omega) := by
  classical
  let S : ↥(Finset.Icc a b) → C := fun r ↦
    F.X (r.val + n) ⊗ D.X (-r.val)
  let inclusion : ∀ r, S r ⟶ (CochainComplex.mapBifunctor F D (curriedTensor C)).X n := fun r ↦
    HomologicalComplex.ιMapBifunctor F D
      (curriedTensor _) (.up ℤ) (r.val + n) (-r.val) n (by
        change r.val + n + -r.val = n
        omega)
  let toTotal : (⨁ S) ⟶ (CochainComplex.mapBifunctor F D (curriedTensor C)).X n :=
    biproduct.desc inclusion
  let component : ∀ (p q : ℤ) (_ : p + q = n),
      (F.X p ⊗ D.X q ⟶ ⨁ S) := fun p q hpq ↦
    if hq : -q ∈ Finset.Icc a b then
      eqToHom (by
        have hp : p = -q + n := by omega
        simp only [S, hp, neg_neg]) ≫ biproduct.ι S ⟨-q, hq⟩
    else 0
  let fromTotal : (CochainComplex.mapBifunctor F D (curriedTensor C)).X n ⟶ (⨁ S) :=
    HomologicalComplex.mapBifunctorDesc (K₁ := F) (K₂ := D)
      (F := curriedTensor _) (c := .up ℤ) component
  have hleft : toTotal ≫ fromTotal = 𝟙 _ := by
    apply biproduct.hom_ext'
    intro r
    dsimp only [toTotal]
    rw [biproduct.ι_desc_assoc]
    dsimp only [inclusion, fromTotal]
    rw [HomologicalComplex.ι_mapBifunctorDesc]
    dsimp only [component]
    rw [dite_eq_left (by simpa only [neg_neg] using r.property)]
    have hr : (⟨- -r.val, by simpa only [neg_neg] using r.property⟩ :
        ↥(Finset.Icc a b)) = r := by
      apply Subtype.ext
      exact neg_neg r.val
    simp only [Category.comp_id]
    exact biproduct_transport S hr.symm _
  have hright : fromTotal ≫ toTotal = 𝟙 _ := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    rw [← Category.assoc]
    dsimp only [fromTotal]
    rw [HomologicalComplex.ι_mapBifunctorDesc]
    change p + q = n at hpq
    dsimp only [component]
    by_cases hq : -q ∈ Finset.Icc a b
    · rw [dite_eq_left hq]
      have hp : p = -q + n := by omega
      subst p
      dsimp only [toTotal]
      rw [Category.assoc, biproduct.ι_desc]
      dsimp only [inclusion]
      simp only [Category.comp_id]
      have transport : ∀ (q' : ℤ) (_ : q = q')
          (hh : F.X (-q + n) ⊗ D.X q = F.X (-q + n) ⊗ D.X q')
          (h : -q + n + q' = n),
          eqToHom hh ≫ HomologicalComplex.ιMapBifunctor F D (curriedTensor C)
            (.up ℤ) (-q + n) q' n h =
          HomologicalComplex.ιMapBifunctor F D (curriedTensor C)
            (.up ℤ) (-q + n) q n hpq := by
        intro q' hq'
        subst q'
        intro hh h
        simp
      exact transport _ (neg_neg q).symm _ _
    · rw [dite_eq_right hq]
      have hzero : IsZero (D.X q) :=
        hbounded q (by
          simpa only [Finset.mem_Icc, not_and_or, not_le] using hq)
      exact ((tensorLeft (F.X p)).map_isZero hzero).eq_of_src _ _
  refine ⟨⟨toTotal, fromTotal, hleft, hright⟩, ?_⟩
  intro r
  exact biproduct.ι_desc inclusion r


/-- The total tensor degree is the finite biproduct of its possibly nonzero summands.
Source: Stacks Project, Tag 08DQ, proof of `lemma-dual-perfect-complex`, tensor sum.
(blueprint: lem-pc-ordinary-evaluation-source-biproduct).

Proof: the product projections of Hom(P,O[0]) identify degree q with
Hom(P^(-q),O): all factors except r=-q have zero target and hence are zero.
The projection followed by the degree-zero unit isomorphism is the identification.
Consequently this dual is zero outside [-b,-a]. Tensoring preserves zero objects,
so in total degree n all summands except p=r+n,q=-r with a<=r<=b vanish.
The coproduct universal property discards the zero summands and reindexes the
remaining ones by r. In an additive category a finite coproduct is a biproduct.
Its induced isomorphism has exactly the inclusion equations below; these equations
also determine it uniquely. If b<a, all summands vanish and the empty biproduct
is the zero object. No boundedness assumption on F is used. -/
theorem ordinaryEvaluation_source_biproduct (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ) (a b n : ℤ)
    (hbounded : ∀ r : ℤ, r < a ∨ b < r → IsZero (P.X r)) :
    ∃ e : (⨁ fun r : ↥(Finset.Icc a b) ↦
        F.X (r.val + n) ⊗ (localEvaluationDual X U P).X (-r.val)) ≅
          (localEvaluationTensor X U P F).X n,
      ∀ r : ↥(Finset.Icc a b),
        biproduct.ι _ r ≫ e.hom =
          HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
            (curriedTensor _) (.up ℤ) (r.val + n) (-r.val) n
            (by change r.val + n + -r.val = n; omega) := by
  exact finiteTensorBiproduct F (localEvaluationDual X U P) a b n
    (fun q hq ↦ localDual_isZero X U P a b q hbounded hq)

end AlgebraicGeometry
