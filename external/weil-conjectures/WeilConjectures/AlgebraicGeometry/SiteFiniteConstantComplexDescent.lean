/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Data.Int.Interval
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # Descending the differentials of a bounded constant graded sheaf

Source: Stacks Project, Cohomology on Sites, Tag 094G, the last step of the
inductive construction of a constant complex.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (B : Type u) [CommRing B] {T U : C}

private noncomputable def constantOverMapIso (f : U ⟶ T) (M : ModuleCat.{u} B) :
    (constantSheaf (J.over U) (ModuleCat.{u} B)).obj M ≅
      (J.overMapPullback (ModuleCat.{u} B) f).obj
        ((constantSheaf (J.over T) (ModuleCat.{u} B)).obj M) :=
  constantSheafOverIso J (ModuleCat.{u} B) U M ≪≫
    (J.overMapPullback (ModuleCat.{u} B) f).mapIso
      (constantSheafOverIso J (ModuleCat.{u} B) T M).symm

set_option backward.isDefEq.respectTransparency false in
private theorem constantOverMapIso_unit (f : U ⟶ T) (M : ModuleCat.{u} B) :
    (toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj M)).app (op (Over.mk (𝟙 U))) ≫
      (constantOverMapIso J B f M).hom.hom.app (op (Over.mk (𝟙 U))) =
    (toSheafify (J.over T) ((Functor.const (Over T)ᵒᵖ).obj M)).app
      (op ((Over.map f).obj (Over.mk (𝟙 U)))) := by
  have hU := congrArg (fun α ↦ α.app (op (Over.mk (𝟙 U))))
    (toSheafify_constantSheafOverHom_hom J (ModuleCat.{u} B) U M)
  have hT := congrArg (fun α ↦ α.app (op ((Over.map f).obj (Over.mk (𝟙 U)))))
    (toSheafify_constantSheafOverHom_hom J (ModuleCat.{u} B) T M)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hU hT
  dsimp [constantOverMapIso, constantSheafOverIso]
  erw [← Category.assoc, hU, ← hT]
  have hi := congrArg
    (fun α ↦ α.hom.app (op ((Over.map f).obj (Over.mk (𝟙 U)))))
    (IsIso.hom_inv_id (constantSheafOverHom J (ModuleCat.{u} B) T M))
  change _ ≫ _ = 𝟙 _ at hi
  erw [Category.assoc, hi, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem constant_overMap_map_eq (f : U ⟶ T) (M N : ModuleCat.{u} B)
    (φ : (constantSheaf (J.over T) (ModuleCat.{u} B)).obj M ⟶
      (constantSheaf (J.over T) (ModuleCat.{u} B)).obj N)
    (v : M ⟶ N)
    (hv : ∀ m : M, φ.hom.app (op ((Over.map f).obj (Over.mk (𝟙 U))))
      ((toSheafify (J.over T) ((Functor.const (Over T)ᵒᵖ).obj M)).app
        (op ((Over.map f).obj (Over.mk (𝟙 U)))) m) =
      (toSheafify (J.over T) ((Functor.const (Over T)ᵒᵖ).obj N)).app
        (op ((Over.map f).obj (Over.mk (𝟙 U)))) (v m)) :
    (constantOverMapIso J B f M).hom ≫
        (J.overMapPullback (ModuleCat.{u} B) f).map φ =
      (constantSheaf (J.over U) (ModuleCat.{u} B)).map v ≫
        (constantOverMapIso J B f N).hom := by
  apply ((constantSheafAdj (J.over U) (ModuleCat.{u} B) Over.mkIdTerminal).homEquiv M
    _).injective
  rw [constantSheafAdj_homEquiv_apply, constantSheafAdj_homEquiv_apply]
  change _ ≫ (constantOverMapIso J B f M).hom.hom.app _ ≫ φ.hom.app _ =
    _ ≫ ((constantSheaf (J.over U) (ModuleCat.{u} B)).map v).hom.app _ ≫
      (constantOverMapIso J B f N).hom.hom.app _
  rw [← Category.assoc, constantOverMapIso_unit]
  have hn := congrArg (fun α ↦ α.app (op (Over.mk (𝟙 U))))
    (toSheafify_naturality (J := J.over U) ((Functor.const (Over U)ᵒᵖ).map v))
  change v ≫ _ = _ ≫
    ((constantSheaf (J.over U) (ModuleCat.{u} B)).map v).hom.app _ at hn
  rw [← Category.assoc, ← hn, Category.assoc, constantOverMapIso_unit]
  ext m
  exact hv m

private theorem constantSheaf_map_injective (V : C) (hV : (⊥ : Sieve V) ∉ J V)
    {M N : ModuleCat.{u} B} :
    Function.Injective ((constantSheaf J (ModuleCat.{u} B)).map (X := M) (Y := N)) := by
  intro f g h
  ext m
  apply J.toSheafify_const_app_injective N hV
  have hf := congrArg (fun α ↦ α.app (op V))
    (toSheafify_naturality (J := J) ((Functor.const Cᵒᵖ).map f))
  have hg := congrArg (fun α ↦ α.app (op V))
    (toSheafify_naturality (J := J) ((Functor.const Cᵒᵖ).map g))
  change f ≫ _ = _ ≫ ((constantSheaf J (ModuleCat.{u} B)).map f).hom.app (op V) at hf
  change g ≫ _ = _ ≫ ((constantSheaf J (ModuleCat.{u} B)).map g).hom.app (op V) at hg
  change (f ≫ _) m = (g ≫ _) m
  rw [hf, hg, h]

private theorem over_sheaf_isZero (V : C) (hV : (⊥ : Sieve V) ∈ J V)
    (F : Sheaf (J.over V) (ModuleCat.{u} B)) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  apply (sheafToPresheaf (J.over V) (ModuleCat.{u} B)).map_injective
  apply NatTrans.ext
  funext W
  have hW : (⊥ : Sieve W.unop) ∈ (J.over V) W.unop := by
    rw [J.mem_over_iff]
    simpa using J.pullback_stable W.unop.hom hV
  exact (F.isTerminalOfBotCover W.unop hW).hom_ext _ _

set_option backward.isDefEq.respectTransparency false in
private theorem exists_sieve_overMap_maps {ι : Type*} [Finite ι]
    (T : C) (M N : ι → ModuleCat.{u} B) [∀ i, Module.Finite B (M i)]
    (φ : ∀ i, (constantSheaf (J.over T) (ModuleCat.{u} B)).obj (M i) ⟶
      (constantSheaf (J.over T) (ModuleCat.{u} B)).obj (N i)) :
    ∃ S ∈ J T, ∀ ⦃U : C⦄ (f : U ⟶ T), S f → (⊥ : Sieve U) ∉ J U →
      ∀ i, ∃ v : M i ⟶ N i,
        (constantOverMapIso J B f (M i)).hom ≫
            (J.overMapPullback (ModuleCat.{u} B) f).map (φ i) =
          (constantSheaf (J.over U) (ModuleCat.{u} B)).map v ≫
            (constantOverMapIso J B f (N i)).hom := by
  classical
  choose S hS h using fun i ↦ exists_mem_forall_exists_linearMap
    (J.over T) (T := Over.mk (𝟙 T)) (M i) (N i) (φ i)
  refine ⟨Sieve.overEquiv (Over.mk (𝟙 T)) (⨅ i, S i), ?_, ?_⟩
  · exact ((J.over T).iInf_mem S hS)
  · intro U f hf hU i
    let g : Over.mk (f ≫ 𝟙 T) ⟶ Over.mk (𝟙 T) := Over.homMk f
    have hg : S i g :=
      (iInf_le S i) _ ((Sieve.overEquiv_iff (⨅ i, S i) f).mp hf)
    have hb : (⊥ : Sieve (Over.mk (f ≫ 𝟙 T))) ∉
        (J.over T) (Over.mk (f ≫ 𝟙 T)) := by
      intro hb
      apply hU
      have hh := (J.mem_over_iff _).mp hb
      rw [(Sieve.overEquiv (Over.mk (f ≫ 𝟙 T))).map_bot] at hh
      exact hh
    obtain ⟨v, hv⟩ := h i g hg hb
    refine ⟨v, constant_overMap_map_eq J B f (M i) (N i) (φ i) v ?_⟩
    intro m
    change (φ i).hom.app (op (Over.mk ((𝟙 U) ≫ f)))
      ((toSheafify (J.over T) ((Functor.const (Over T)ᵒᵖ).obj (M i))).app
        (op (Over.mk ((𝟙 U) ≫ f))) m) =
      (toSheafify (J.over T) ((Functor.const (Over T)ᵒᵖ).obj (N i))).app
        (op (Over.mk ((𝟙 U) ≫ f))) (v m)
    have hv' := hv m
    dsimp only [g] at hv'
    erw [Category.id_comp]
    erw [Category.comp_id] at hv'
    exact hv'

private theorem exists_complex_of_lifted_differentials
    {A : Type*} [Category A] [Preadditive A] [HasZeroObject A]
    (F : ModuleCat.{u} B ⥤ A) [F.Additive] [F.Faithful]
    (P : CochainComplex A ℤ) (M : ℤ → ModuleCat.{u} B)
    (e : ∀ q, F.obj (M q) ≅ P.X q) (v : ∀ q, M q ⟶ M (q + 1))
    (hv : ∀ q, F.map (v q) ≫ (e (q + 1)).hom = (e q).hom ≫ P.d q (q + 1)) :
    ∃ N : CochainComplex (ModuleCat.{u} B) ℤ,
      (∀ q, N.X q = M q) ∧ Nonempty ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N ≅ P) := by
  classical
  have hs (q : ℤ) : v q ≫ v (q + 1) = 0 := by
    apply F.map_injective
    rw [F.map_comp, F.map_zero]
    apply (cancel_mono (e (q + 1 + 1)).hom).mp
    rw [Category.assoc, hv (q + 1), ← Category.assoc, hv q, Category.assoc,
      P.d_comp_d, comp_zero, zero_comp]
  let N := CochainComplex.of M v hs
  refine ⟨N, fun _ ↦ rfl, ⟨HomologicalComplex.Hom.isoOfComponents e ?_⟩⟩
  intro i j hij
  change i + 1 = j at hij
  subst j
  simpa only [Functor.mapHomologicalComplex_obj_d, N, CochainComplex.of_d]
    using (hv i).symm

set_option backward.isDefEq.respectTransparency false in
/-- A bounded sheaf complex with constant finite graded terms is locally the
constant sheaf complex of an actual bounded complex of finite modules.

Source: Stacks Project, Cohomology on Sites, Tag 094G, proof of
`lemma-locally-constant`, descent of the finitely many differentials.
(auxiliary; not a blueprint node)

Proof: Conjugate each differential by the given term isomorphisms. Finite generation
makes each of these maps locally induced by a module map. Intersect the covering
sieves for the finitely many source degrees in [a,b]. On a nonempty slice, the unit
of constant-presheaf sheafification is injective, so the constant sheaf functor is
faithful. The lifted consecutive maps therefore compose to zero, and define the
required complex. Outside [a,b] its terms are the prescribed zero modules. The
term isomorphisms give a chain isomorphism. On an empty slice every sheaf is zero;
the same graded modules with zero differentials give a model there. -/
theorem exists_local_constant_complex_of_constant_terms
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Type u) [CommRing B]
    (T : C) (P : CochainComplex (Sheaf (J.over T) (ModuleCat.{u} B)) ℤ)
    (a b : ℤ) (M : ℤ → ModuleCat.{u} B)
    (hfinite : ∀ q, Module.Finite B (M q))
    (hzero : ∀ q, q < a ∨ b < q → IsZero (M q))
    (e : ∀ q, P.X q ≅ (constantSheaf (J.over T) (ModuleCat.{u} B)).obj (M q)) :
    ∃ S ∈ J T, ∀ ⦃U : C⦄ (f : U ⟶ T), S f →
      ∃ N : CochainComplex (ModuleCat.{u} B) ℤ,
        (∀ q, Module.Finite B (N.X q)) ∧
        (∀ q, q < a ∨ b < q → IsZero (N.X q)) ∧
        Nonempty (((J.overMapPullback (ModuleCat.{u} B) f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P ≅
          ((constantSheaf (J.over U) (ModuleCat.{u} B)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) := by
  classical
  let φ (q : ℤ) := (e q).inv ≫ P.d q (q + 1) ≫ (e (q + 1)).hom
  let ι := ↥(Finset.Icc a b)
  let (q : ι) : Module.Finite B (M q.1) := hfinite q.1
  obtain ⟨S, hS, h⟩ := exists_sieve_overMap_maps J B T
    (fun q : ι ↦ M q.1) (fun q : ι ↦ M (q.1 + 1)) (fun q ↦ φ q.1)
  refine ⟨S, hS, fun U f hf ↦ ?_⟩
  let R := J.overMapPullback (ModuleCat.{u} B) f
  let A := (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let F := constantSheaf (J.over U) (ModuleCat.{u} B)
  let ε (q : ℤ) : F.obj (M q) ≅ A.X q :=
    constantOverMapIso J B f (M q) ≪≫ R.mapIso (e q).symm
  by_cases hU : (⊥ : Sieve U) ∈ J U
  · let N := CochainComplex.of M (fun _ ↦ 0) (by intros; simp)
    refine ⟨N, hfinite, hzero, ⟨HomologicalComplex.Hom.isoOfComponents
      (fun q ↦ (ε q).symm) ?_⟩⟩
    intro q r _
    exact (over_sheaf_isZero J B U hU (A.X q)).eq_of_src _ _
  · have hUU : (⊥ : Sieve (Over.mk (𝟙 U))) ∉
        (J.over U) (Over.mk (𝟙 U)) := by
      intro hb
      apply hU
      have hh := (J.mem_over_iff _).mp hb
      rw [(Sieve.overEquiv (Over.mk (𝟙 U))).map_bot] at hh
      exact hh
    have : F.Faithful :=
      ⟨fun h ↦ constantSheaf_map_injective (J.over U) B (Over.mk (𝟙 U)) hUU h⟩
    have hv (q : ℤ) : ∃ v : M q ⟶ M (q + 1),
        F.map v ≫ (ε (q + 1)).hom = (ε q).hom ≫ A.d q (q + 1) := by
      by_cases hq : q ∈ Finset.Icc a b
      · obtain ⟨v, hv⟩ := h f hf hU ⟨q, hq⟩
        refine ⟨v, ?_⟩
        have hv' : F.map v = (constantOverMapIso J B f (M q)).hom ≫
            R.map (φ q) ≫ (constantOverMapIso J B f (M (q + 1))).inv := by
          apply (cancel_mono (constantOverMapIso J B f (M (q + 1))).hom).mp
          simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hv.symm
        rw [hv']
        dsimp only [ε, φ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
        simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
        change (constantOverMapIso J B f (M q)).hom ≫ R.map (e q).inv ≫
          R.map (P.d q (q + 1)) ≫ R.map (e (q + 1)).hom ≫ R.map (e (q + 1)).inv =
          (constantOverMapIso J B f (M q)).hom ≫ R.map (e q).inv ≫
            R.map (P.d q (q + 1))
        rw [Iso.hom_inv_id_map, Category.comp_id]
      · refine ⟨0, ?_⟩
        exact (F.map_isZero (hzero q (by simpa only [Finset.mem_Icc, not_and_or,
          not_le] using hq))).eq_of_src _ _
    choose v hv using hv
    obtain ⟨N, hN, ⟨eN⟩⟩ := exists_complex_of_lifted_differentials B F A M ε v hv
    refine ⟨N, ?_, ?_, ⟨eN.symm⟩⟩
    · intro q
      rw [hN q]
      exact hfinite q
    · intro q hq
      rw [hN q]
      exact hzero q hq

end CategoryTheory
