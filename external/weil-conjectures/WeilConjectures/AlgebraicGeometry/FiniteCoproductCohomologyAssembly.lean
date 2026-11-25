/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap
import WeilConjectures.AlgebraicGeometry.EtaleSheafClopenProduct
import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic

/-! # Cohomology of a finite coproduct is the product of component cohomologies

Source: literature/stacks-project/etale-cohomology.tex, first paragraph of the proof of
Lemma 0A5B (blueprint: lem-weil-pbc-finite-coproduct-cohomology-assembly)

The restriction maps along the coprojections of a finite disjoint coproduct identify
étale cohomology with the product of the component cohomology groups.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

-- The induction elaborates dependent products of Ext groups in two abelian categories.
private theorem mapExt_family_bijective
    {J : Type u} {A : Type (u + 2)} [Category.{u + 1} A] [Abelian A]
    [HasExt.{u + 1} A] [EnoughInjectives A]
    {B : J → Type (u + 2)} [∀ i, Category.{u + 1} (B i)] [∀ i, Abelian (B i)]
    [∀ i, HasExt.{u + 1} (B i)]
    (G : (i : J) → A ⥤ B i)
    [∀ i, (G i).Additive] [∀ i, PreservesFiniteLimits (G i)]
    [∀ i, PreservesFiniteColimits (G i)] [∀ i, (G i).PreservesInjectiveObjects]
    [(Functor.pi' G).Full] [(Functor.pi' G).Faithful] (M N : A) (q : ℕ) :
    Function.Bijective (fun x : Abelian.Ext M N q ↦ fun i ↦ x.mapExactFunctor (G i)) := by
  classical
  let Φ (N : A) (q : ℕ) := AddMonoidHom.pi (fun i ↦ (G i).mapExtAddHom M N q)
  change Function.Bijective (Φ N q)
  induction q generalizing N with
  | zero =>
      constructor
      · intro x y h
        obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective M N).2 x
        obtain ⟨g, rfl⟩ := (Abelian.Ext.mk₀_bijective M N).2 y
        have hfg : (Functor.pi' G).map f = (Functor.pi' G).map g := by
          funext i
          exact (Abelian.Ext.mk₀_bijective _ _).1 (by
            simpa [Φ, Abelian.Ext.mapExactFunctor_mk₀] using congrFun h i)
        exact congrArg Abelian.Ext.mk₀ ((Functor.pi' G).map_injective hfg)
      · intro x
        choose f hf using fun i ↦ (Abelian.Ext.mk₀_bijective _ _).2 (x i)
        obtain ⟨g, hg⟩ := (Functor.pi' G).map_surjective f
        refine ⟨Abelian.Ext.mk₀ g, ?_⟩
        funext i
        simpa [Φ, Abelian.Ext.mapExactFunctor_mk₀, ← congrFun hg i] using hf i
  | succ q ih =>
      let P : InjectivePresentation N := Classical.arbitrary _
      let S := ShortComplex.mk P.f (cokernel.π P.f) (cokernel.condition P.f)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel P.f }
      let a := (Abelian.Ext.mk₀ S.g).postcomp M (add_zero q)
      let b := hS.extClass.postcomp M (show q + 1 = q + 1 from rfl)
      let ai := AddMonoidHom.piMap (fun i ↦
        (Abelian.Ext.mk₀ ((G i).map S.g)).postcomp ((G i).obj M) (add_zero q))
      let bi := AddMonoidHom.piMap (fun i ↦
        (hS.map_of_exact (G i)).extClass.postcomp ((G i).obj M)
          (show q + 1 = q + 1 from rfl))
      refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
        a b ai bi (Φ S.X₂ q) (Φ S.X₃ q) (Φ S.X₁ (q + 1)) ?_ ?_ ?_ ?_
        (ih S.X₂).2 (ih S.X₃) ?_ ?_
      · ext x i
        change _ = (x.comp (Abelian.Ext.mk₀ S.g) (add_zero q)).mapExactFunctor (G i)
        symm
        exact (Abelian.Ext.mapExactFunctor_comp (G i) x (Abelian.Ext.mk₀ S.g)
          (add_zero q)).trans (by rw [Abelian.Ext.mapExactFunctor_mk₀]; rfl)
      · ext x i
        change _ = (x.comp hS.extClass rfl).mapExactFunctor (G i)
        symm
        exact (Abelian.Ext.mapExactFunctor_comp (G i) x hS.extClass rfl).trans
          (by rw [Abelian.Ext.mapExactFunctor_extClass]; rfl)
      · exact (ShortComplex.ab_exact_iff_function_exact _).1
          (Abelian.Ext.covariant_sequence_exact₃' M hS q (q + 1) rfl)
      · intro x
        constructor
        · intro hx
          have hx' (i : J) : bi x i = 0 := congrFun hx i
          choose y hy using fun i ↦ Abelian.Ext.covariant_sequence_exact₃
            ((G i).obj M) (hS.map_of_exact (G i)) (x i) rfl (hx' i)
          exact ⟨y, funext hy⟩
        · rintro ⟨y, rfl⟩
          funext i
          exact ((ShortComplex.ab_exact_iff_function_exact _).1
            (Abelian.Ext.covariant_sequence_exact₃' ((G i).obj M)
              (hS.map_of_exact (G i)) q (q + 1) rfl) _).2 ⟨y i, rfl⟩
      · intro x
        exact Abelian.Ext.covariant_sequence_exact₁ M hS x
          (Abelian.Ext.eq_zero_of_injective _) rfl
      · intro x
        have (i : J) : Injective ((S.map (G i)).X₂) :=
          (G i).injective_obj_of_injective P.injective
        choose y hy using fun i ↦ Abelian.Ext.covariant_sequence_exact₁
          ((G i).obj M) (hS.map_of_exact (G i)) (x i)
          (Abelian.Ext.eq_zero_of_injective _) rfl
        exact ⟨y, funext hy⟩

namespace AlgebraicGeometry.Etale

/-- For a finite coproduct of schemes, étale cohomology is the product of the
component cohomologies, via restriction along the coprojections.

Source: literature/stacks-project/etale-cohomology.tex, first paragraph of the proof of
Lemma 0A5B (blueprint: lem-weil-pbc-finite-coproduct-cohomology-assembly).
Proof:
1. By `lem-weil-pbc-scheme-coproduct-family`, the coprojections are disjoint clopen
   immersions covering the coproduct; every étale object restricts componentwise.
2. The sheaf condition gives the equivalence with the product of the component
   sheaf categories (`lem-weil-pbc-etale-sheaf-clopen-product`), using
   `def-weil-pbc-inverse-image` for restriction. Global sections become the product
   of component global sections.
3. The sheaf categories have enough injectives
   (`lem-weil-pbc-module-sheaves-enough-injectives`). Global sections are additive
   and left exact (`def-weil-pbc-global-sections-functor`). An injective resolution
   is bounded below and K-injective (`lem-weil-pbc-bounded-below-injectives-kinjective`),
   so `def-weil-pbc-etale-cohomology` is the right derived functor of global sections
   (`def-sp-left-exact-additive`). The equivalence carries injective resolutions
   componentwise; `lem-weil-pbc-derived-finite-product` computes their derived
   global sections as the product. The resulting isomorphism is induced by the
   restriction maps displayed here.
-/
theorem finiteCoproductCohomologyAssembly
    {I : Type u} [Finite I] (X : I → Scheme.{u}) (C : Scheme.{u})
    (ι : ∀ i : I, X i ⟶ C) (hc : IsColimit (Cofan.mk C ι))
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective
      (fun x : Sheaf.H F q =>
        fun i : I =>
          cohomologyMap (ι i) F q x) := by
  classical
  let G := fun i ↦ upperStar AddCommGrpCat.{u + 1} (ι i)
  have hR : (Functor.pi' G).IsEquivalence := (sheaf_clopen_product X ι hc).1
  have hi (i : I) : IsOpenImmersion (ι i) := by
    let e := (coproductIsCoproduct X).coconePointUniqueUpToIso hc
    have he : Sigma.ι X i ≫ e.hom = ι i := by
      exact (coproductIsCoproduct X).comp_coconePointUniqueUpToIso_hom hc (⟨i⟩)
    rw [← he]
    infer_instance
  have (i : I) : (G i).PreservesInjectiveObjects := by
    constructor
    intro J hJ
    have : Injective J := hJ
    exact injective_upperStar_obj_of_etale_addCommGrp (ι i) J
  have h := mapExt_family_bijective G
    ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ))) F q
  let e (i : I) := Abelian.Ext.precompAddEquiv
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (ι i)).symm.app
      (AddCommGrpCat.of (ULift ℤ))) ((G i).obj F) q
  exact (Equiv.piCongrRight (fun i ↦ (e i).toEquiv)).bijective.comp h

end AlgebraicGeometry.Etale
