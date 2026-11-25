/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Data.Int.Interval

/-! # Local algebraicity of maps between bounded constant module complexes -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type w) [CommRing R]
  [HasSheafify J (ModuleCat.{w} R)] [J.WEqualsLocallyBijective (ModuleCat.{w} R)]
  [∀ V : C, HasSheafify (J.over V) (ModuleCat.{w} R)]
  [∀ V : C, (J.over V).WEqualsLocallyBijective (ModuleCat.{w} R)]
  [∀ V : C, (J.over V).HasSheafCompose (forget (ModuleCat.{w} R))]
  [(constantSheaf J (ModuleCat.{w} R)).Additive]
  [∀ V : C, (constantSheaf (J.over V) (ModuleCat.{w} R)).Additive]
  [∀ V : C, (J.overPullback (ModuleCat.{w} R) V).Additive]

omit [J.WEqualsLocallyBijective (ModuleCat.{w} R)]
  [∀ V : C, (J.over V).WEqualsLocallyBijective (ModuleCat.{w} R)]
  [∀ V : C, (J.over V).HasSheafCompose (forget (ModuleCat.{w} R))]
  [(constantSheaf J (ModuleCat.{w} R)).Additive]
  [∀ V : C, (constantSheaf (J.over V) (ModuleCat.{w} R)).Additive]
  [∀ V : C, (J.overPullback (ModuleCat.{w} R) V).Additive] in
private theorem constantSlice_naturality (V : C) {M N : ModuleCat.{w} R} (f : M ⟶ N) :
    (constantSheaf (J.over V) (ModuleCat.{w} R)).map f ≫
        constantSheafOverHom J _ V N =
      constantSheafOverHom J _ V M ≫
        (J.overPullback (ModuleCat.{w} R) V).map
          ((constantSheaf J (ModuleCat.{w} R)).map f) := by
  apply ((constantSheafAdj (J.over V) _ Over.mkIdTerminal).homEquiv M _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    constantSheafAdj_homEquiv_constantSheafOverHom,
    constantSheafAdj_homEquiv_constantSheafOverHom]
  exact congr_app (toSheafify_naturality J ((Functor.const Cᵒᵖ).map f)) (op V)

omit [HasSheafify J (ModuleCat.{w} R)] [J.WEqualsLocallyBijective (ModuleCat.{w} R)]
  [∀ V : C, (J.over V).HasSheafCompose (forget (ModuleCat.{w} R))]
  [(constantSheaf J (ModuleCat.{w} R)).Additive]
  [∀ V : C, (constantSheaf (J.over V) (ModuleCat.{w} R)).Additive]
  [∀ V : C, (J.overPullback (ModuleCat.{w} R) V).Additive] in
private theorem constantSlice_map_injective (V : C) (hV : (⊥ : Sieve V) ∉ J V)
    {M N : ModuleCat.{w} R} (f g : M ⟶ N)
    (h : (constantSheaf (J.over V) (ModuleCat.{w} R)).map f =
      (constantSheaf (J.over V) (ModuleCat.{w} R)).map g) : f = g := by
  have hVV : (⊥ : Sieve (Over.mk (𝟙 V))) ∉ (J.over V) (Over.mk (𝟙 V)) := by
    intro hb
    apply hV
    have hh := (J.mem_over_iff _).mp hb
    rw [(Sieve.overEquiv (Over.mk (𝟙 V))).map_bot] at hh
    exact hh
  ext m
  apply (J.over V).toSheafify_const_app_injective N hVV
  have hf := congr_app
    (toSheafify_naturality (J.over V) ((Functor.const (Over V)ᵒᵖ).map f))
    (op (Over.mk (𝟙 V)))
  have hg := congr_app
    (toSheafify_naturality (J.over V) ((Functor.const (Over V)ᵒᵖ).map g))
    (op (Over.mk (𝟙 V)))
  change f ≫ _ = _ ≫ ((constantSheaf (J.over V) (ModuleCat.{w} R)).map f).hom.app _ at hf
  change g ≫ _ = _ ≫ ((constantSheaf (J.over V) (ModuleCat.{w} R)).map g).hom.app _ at hg
  exact ConcreteCategory.congr_hom (hf.trans ((congrArg (fun k ↦ _ ≫ k.hom.app _) h).trans
    hg.symm)) m

omit [∀ V : C, HasSheafify (J.over V) (ModuleCat.{w} R)]
  [HasSheafify J (ModuleCat.{w} R)] [J.WEqualsLocallyBijective (ModuleCat.{w} R)]
  [∀ V : C, (J.over V).WEqualsLocallyBijective (ModuleCat.{w} R)]
  [∀ V : C, (J.over V).HasSheafCompose (forget (ModuleCat.{w} R))]
  [(constantSheaf J (ModuleCat.{w} R)).Additive]
  [∀ V : C, (constantSheaf (J.over V) (ModuleCat.{w} R)).Additive]
  [∀ V : C, (J.overPullback (ModuleCat.{w} R) V).Additive] in
private theorem over_isZero (V : C) (hV : (⊥ : Sieve V) ∈ J V)
    (F : Sheaf (J.over V) (ModuleCat.{w} R)) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  apply (sheafToPresheaf (J.over V) (ModuleCat.{w} R)).map_injective
  apply NatTrans.ext
  funext W
  have hW : (⊥ : Sieve W.unop) ∈ (J.over V) W.unop := by
    rw [J.mem_over_iff]
    simpa using J.pullback_stable W.unop.hom hV
  exact (F.isTerminalOfBotCover W.unop hW).hom_ext _ _

/-- A chain map between constant complexes with bounded finite source is locally
algebraic, with equality after slice restriction.

Source: Stacks Project, Tag 09BE, finite-generator descent of chain maps.
(blueprint: lem-weil-pbc-bounded-constant-module-chain-map-local)

Proof: Lift the components in the finite support of the source through the constant
module morphism theorem, and intersect the resulting covering sieves. Away from the
support both maps are zero. On a member not covered by the empty sieve, the constant
section unit is injective and therefore reflects each chain equation of the lifted
components. These components define an algebraic chain map. Naturality of the canonical
constant-to-slice isomorphisms identifies its constant realization with the original
restricted chain map. On a member covered by the empty sieve all sheaves are zero,
so the zero chain map has the required realization. -/
theorem exists_bounded_constant_module_chain_map_local
    (F G : CochainComplex (ModuleCat.{w} R) ℤ)
    (hF : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero (F.X q))
    [∀ q : ℤ, Module.Finite R (F.X q)] (T : C)
    (a : ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℤ)).obj F ⟶
      ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℤ)).obj G) :
    ∃ S ∈ J T, ∀ (V : C) (f : V ⟶ T), S f → ∃ b : F ⟶ G,
      ((J.overPullback (ModuleCat.{w} R) V).mapHomologicalComplex (.up ℤ)).map a =
        ((J.overPullback (ModuleCat.{w} R) V).mapHomologicalComplex (.up ℤ)).map
          (((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℤ)).map b) := by
  classical
  obtain ⟨lo, hi, hzero⟩ := hF
  let I := {q : ℤ // q ∈ Finset.Icc lo hi}
  have hc (q : I) := exists_mem_forall_exists_constantSheafOverHom_comp_map_eq
    J (T := T) (F.X q.1) (G.X q.1) (a.f q.1)
  choose S hS h using hc
  refine ⟨⨅ q, S q, J.iInf_mem S hS, fun V f hf ↦ ?_⟩
  let c := constantSheaf (J.over V) (ModuleCat.{w} R)
  let p := J.overPullback (ModuleCat.{w} R) V
  let e (M : ModuleCat.{w} R) := constantSheafOverIso J (ModuleCat.{w} R) V M
  by_cases hV : (⊥ : Sieve V) ∈ J V
  · refine ⟨0, ?_⟩
    apply HomologicalComplex.hom_ext
    intro q
    exact (over_isZero J R V hV _).eq_of_src _ _
  · have hx (q : I) : ∃ b : F.X q.1 ⟶ G.X q.1,
        (e (F.X q.1)).hom ≫ p.map (a.f q.1) =
          c.map b ≫ (e (G.X q.1)).hom :=
      h q f ((iInf_le S q) _ hf) hV
    choose b hb using hx
    let d (q : ℤ) : F.X q ⟶ G.X q :=
      if hq : q ∈ Finset.Icc lo hi then b ⟨q, hq⟩ else 0
    have heq (q : ℤ) : (e (F.X q)).hom ≫ p.map (a.f q) =
        c.map (d q) ≫ (e (G.X q)).hom := by
      by_cases hq : q ∈ Finset.Icc lo hi
      · simpa only [d, dite_eq_left hq] using hb ⟨q, hq⟩
      · have hz : IsZero (F.X q) := hzero q (by
          simpa only [Finset.mem_Icc, not_and_or, not_le] using hq)
        exact (c.map_isZero hz).eq_of_src _ _
    have hd (i j : ℤ) : d i ≫ G.d i j = F.d i j ≫ d j := by
      apply constantSlice_map_injective J R V hV
      apply (cancel_mono (e (G.X j)).hom).mp
      have hnG : c.map (G.d i j) ≫ (e (G.X j)).hom =
          (e (G.X i)).hom ≫ p.map
            ((constantSheaf J (ModuleCat.{w} R)).map (G.d i j)) :=
        constantSlice_naturality J R V (G.d i j)
      have hnF : c.map (F.d i j) ≫ (e (F.X j)).hom =
          (e (F.X i)).hom ≫ p.map
            ((constantSheaf J (ModuleCat.{w} R)).map (F.d i j)) :=
        constantSlice_naturality J R V (F.d i j)
      have ha : a.f i ≫ (constantSheaf J (ModuleCat.{w} R)).map (G.d i j) =
          (constantSheaf J (ModuleCat.{w} R)).map (F.d i j) ≫ a.f j := a.comm i j
      rw [c.map_comp, c.map_comp, Category.assoc, hnG, ← Category.assoc, ← heq i,
        Category.assoc, ← p.map_comp, ha, p.map_comp,
        ← Category.assoc, ← hnF, Category.assoc, heq j, ← Category.assoc]
    let b' : F ⟶ G := { f := d, comm' := fun i j _ ↦ hd i j }
    refine ⟨b', ?_⟩
    apply HomologicalComplex.hom_ext
    intro q
    apply (cancel_epi (e (F.X q)).hom).mp
    exact (heq q).trans (constantSlice_naturality J R V (d q))

end CategoryTheory
