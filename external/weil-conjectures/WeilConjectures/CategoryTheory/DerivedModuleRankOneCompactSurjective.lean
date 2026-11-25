/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.CompactObject
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums

/-!
# Rank-one comparison surjectivity

The finite-support calculation is carried out on chain maps before applying localization.
Source: Stacks Project, Tag 0F5X, first paragraph (rank-one compactness assertion).
-/

@[expose] public section

universe w vH
namespace CategoryTheory
open Limits DirectSum

private lemma rankOne_kProjective {S : Type w} [Ring S] :
    ((CochainComplex.singleFunctor (ModuleCat.{max w vH} S) 0).obj
      (ModuleCat.of S (ULift.{vH} S))).IsKProjective := by
  have (n : ℤ) : Projective
      (((CochainComplex.singleFunctor (ModuleCat.{max w vH} S) 0).obj
        (ModuleCat.of S (ULift.{vH} S))).X n) := by
    change Projective
      (((HomologicalComplex.single (ModuleCat.{max w vH} S) (.up ℤ) 0).obj
        (ModuleCat.of S (ULift.{vH} S))).X n)
    infer_instance
  exact CochainComplex.isKProjective_of_projective _ 0

private lemma rankOne_map_surjective
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    (L : CochainComplex (ModuleCat.{max w vH} S) ℤ) :
    Function.Surjective (DerivedCategory.Q.map :
      ((CochainComplex.singleFunctor (ModuleCat.{max w vH} S) 0).obj
        (ModuleCat.of S (ULift.{vH} S)) ⟶ L) → _) := by
  let K := (CochainComplex.singleFunctor (ModuleCat.{max w vH} S) 0).obj
    (ModuleCat.of S (ULift.{vH} S))
  let : K.IsKProjective := rankOne_kProjective
  intro f
  let e := DerivedCategory.quotientCompQhIso (ModuleCat.{max w vH} S)
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective
    K ((HomotopyCategory.quotient _ _).obj L)).surjective
    (e.hom.app K ≫ f ≫ e.inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨g, ?_⟩
  apply (cancel_mono (e.inv.app L)).1
  rw [DerivedCategory.quotientCompQhIso_inv_naturality, hg]
  simp [e, K]

private lemma rankOne_chain_finite_sum
    {S : Type w} [Ring S] (I : Type (max w vH))
    (K : I → CochainComplex (ModuleCat.{max w vH} S) ℤ)
    (f : (CochainComplex.singleFunctor (ModuleCat.{max w vH} S) 0).obj
      (ModuleCat.of S (ULift.{vH} S)) ⟶ ∐ K) :
    ∃ (s : Finset I) (g : ∀ i, (CochainComplex.singleFunctor
        (ModuleCat.{max w vH} S) 0).obj (ModuleCat.of S (ULift.{vH} S)) ⟶ K i),
      ∑ i ∈ s, g i ≫ Sigma.ι K i = f := by
  classical
  -- Coproduct projections give coordinate chain maps without choosing cycle lifts.
  let p (i : I) : ∐ K ⟶ K i :=
    Sigma.desc (fun j ↦ if h : j = i then eqToHom (congrArg K h) else 0)
  let X (i : I) := (K i).X 0
  let t : Cofan X := Cofan.mk ((∐ K).X 0) (fun i ↦ (Sigma.ι K i).f 0)
  have ht : IsColimit t := by
    exact isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{max w vH} S) (.up ℤ) 0) K
  let e := (ModuleCat.coproductCoconeIsColimit X).coconePointUniqueUpToIso ht
  have he (i : I) :
      ModuleCat.ofHom (DirectSum.lof S I (fun i ↦ X i) i) ≫ e.hom =
        (Sigma.ι K i).f 0 := by
    exact (ModuleCat.coproductCoconeIsColimit X).comp_coconePointUniqueUpToIso_hom ht ⟨i⟩
  -- Read the generator in degree zero through the canonical single-complex isomorphism.
  let a₀ := (HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (ModuleCat.of S (ULift.{vH} S))).inv
  let x := (a₀ ≫ f.f 0) (ULift.up (1 : S))
  let v : ⨁ i, X i := e.inv x
  have hp (i : I) (v : ⨁ j, X j) : (p i).f 0 (e.hom v) = v i := by
    induction v using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      have h := congrArg (fun a : ModuleCat.of S (X j) ⟶ (∐ K).X 0 ↦ a y) (he j)
      change e.hom (DirectSum.of (fun j ↦ X j) j y) = (Sigma.ι K j).f 0 y at h
      rw [h]
      change (((Sigma.ι K j) ≫ p i).f 0) y = _
      by_cases hji : j = i
      · subst j
        simp [p]
      · simp [p, hji, DirectSum.of_eq_of_ne, Ne.symm hji]
    | add a b ha hb => simp [ha, hb]
  have hx : e.hom v = x := by simp [v]
  refine ⟨v.support, fun i ↦ f ≫ p i, ?_⟩
  apply HomologicalComplex.from_single_hom_ext
  apply (cancel_epi a₀).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  -- A linear map out of the lifted regular module is determined by the lifted unit.
  have ha : a = a.down • (ULift.up (1 : S) : ULift.{vH} S) := by
    ext
    simp
  rw [ha]
  simp only [map_smul]
  congr 1
  rw [show (∑ i ∈ v.support, (f ≫ p i) ≫ Sigma.ι K i).f 0 =
    ∑ i ∈ v.support, ((f ≫ p i) ≫ Sigma.ι K i).f 0 from
      map_sum (HomologicalComplex.Hom.fAddMonoidHom 0) _ _]
  simp only [Preadditive.comp_sum, HomologicalComplex.comp_f,
    ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
  change ∑ i ∈ v.support, (Sigma.ι K i).f 0 ((p i).f 0 x) = x
  conv_rhs => rw [← hx, ← DirectSum.sum_support_of v]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hx, hp]
  exact (congrArg (fun a : ModuleCat.of S (X i) ⟶ (∐ K).X 0 ↦ a (v i)) (he i)).symm

open Classical in
/-- Surjectivity of the rank-one comparison map.

Proof in words: evaluation at the lifted unit identifies linear maps from ULift S with
vectors, and makes this module free of rank one, hence projective. Its degree-zero complex
is K-projective: a chain map into an acyclic complex is specified by a zero-cycle, which has
a preimage under the preceding differential, giving a null homotopy. Localization on maps
out of this complex thus identifies derived maps naturally and additively with H^0.
Choose complexes representing E i. By derivedModuleDirectSums their termwise coproduct,
with the canonical inclusions, represents the categorical coproduct. Every zero-cycle in
this termwise sum has finite support, and each coordinate is a zero-cycle. A given derived
map from P to the coproduct therefore has a zero-cycle representative with finite support.
Each coordinate determines a derived map P to E i under the preceding identification.
Put these maps into the algebraic direct sum. Naturality of the identification with H^0
shows that their image under the canonical comparison is the given map. This proves
surjectivity. The empty sum has zero H^0, so its only map has the zero preimage; for the zero
ring all modules are zero. No commutativity is used. Source: Stacks Project, Tag 0F5X,
first paragraph. (auxiliary; not a blueprint node)
-/
theorem derivedModule_rankOne_comparison_surjective
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    [HasCoproducts.{max w vH} (DerivedCategory (ModuleCat.{max w vH} S))]
    (I : Type (max w vH))
    (E : I → DerivedCategory (ModuleCat.{max w vH} S)) :
    let _ := Classical.decEq I
    let P := (DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
      (ModuleCat.of S (ULift.{vH} S))
    Function.Surjective
      (DirectSum.toAddMonoid (fun i : I => Preadditive.rightComp P (Sigma.ι E i)) :
        (⨁ i : I, (P ⟶ E i)) →+ (P ⟶ ∐ E)) := by
  classical
  dsimp
  let P := (DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
    (ModuleCat.of S (ULift.{vH} S))
  -- Use complexes representing the family and the termwise-sum coproduct theorem.
  let K (i : I) := DerivedCategory.Q.objPreimage (E i)
  let eK (i : I) : DerivedCategory.Q.obj (K i) ≅ E i :=
    DerivedCategory.Q.objObjPreimageIso (E i)
  let h := (derivedModuleDirectSums S I K).some
  let e₀ := h.coconePointUniqueUpToIso
    (coproductIsCoproduct (fun i ↦ DerivedCategory.Q.obj (K i)))
  let e : DerivedCategory.Q.obj (∐ K) ≅ ∐ E := e₀ ≪≫ Sigma.mapIso eK
  have he (i : I) : DerivedCategory.Q.map (Sigma.ι K i) ≫ e.hom =
      (eK i).hom ≫ Sigma.ι E i := by
    dsimp [e]
    rw [← Category.assoc]
    have he₀ : DerivedCategory.Q.map (Sigma.ι K i) ≫ e₀.hom =
        Sigma.ι (fun i ↦ DerivedCategory.Q.obj (K i)) i :=
      h.comp_coconePointUniqueUpToIso_hom
        (coproductIsCoproduct (fun i ↦ DerivedCategory.Q.obj (K i))) ⟨i⟩
    rw [he₀]
    exact Sigma.ι_mapIso_hom eK i
  intro f
  -- Lift to a chain map, take its finite support, and localize its coordinates.
  obtain ⟨a, ha⟩ := rankOne_map_surjective (∐ K) (f ≫ e.inv)
  obtain ⟨s, g, hg⟩ := rankOne_chain_finite_sum I K a
  refine ⟨∑ i ∈ s, DirectSum.of (fun i ↦ P ⟶ E i) i
    (DerivedCategory.Q.map (g i) ≫ (eK i).hom), ?_⟩
  simp only [P, map_sum, DirectSum.toAddMonoid_of]
  change (∑ i ∈ s, (DerivedCategory.Q.map (g i) ≫ (eK i).hom) ≫ Sigma.ι E i) = f
  calc
    ∑ i ∈ s, (DerivedCategory.Q.map (g i) ≫ (eK i).hom) ≫ Sigma.ι E i =
        ∑ i ∈ s, DerivedCategory.Q.map (g i ≫ Sigma.ι K i) ≫ e.hom := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Functor.map_comp, Category.assoc, he]
    _ = DerivedCategory.Q.map (∑ i ∈ s, g i ≫ Sigma.ι K i) ≫ e.hom := by
      rw [Functor.map_sum, Preadditive.sum_comp]
    _ = f := by rw [hg, ha]; simp

end CategoryTheory
