/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModel
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.Sheaves.Abelian

/-! # Exactness of Godement models -/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Evaluation of the product's coordinate at `x`, on stalks.
Source: Stacks, Tag 0FKR (blueprint: lem-sc-module-cup-godement-stalk-contraction). -/
private def moduleCup_godementStalkEval (X : Scheme.{u}) (F : X.Modules) (x : X) :
    (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (moduleCup_godementObject X F) ⟶
    (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F :=
  (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
    (Pi.π (fun y : X ↦ skyscraper y (F.presheaf.stalk y)) x) ≫
    ModuleCat.ofHom (skyscraperStalkEval x (F.presheaf.stalk x))

private theorem eval_unit (X : Scheme.{u}) (F : X.Modules) (x : X) :
    (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
        (moduleCup_godementUnit X F) ≫ moduleCup_godementStalkEval X F x = 𝟙 _ := by
  dsimp only [moduleCup_godementStalkEval]
  rw [← Functor.map_comp_assoc]
  simp only [moduleCup_godementUnit, Pi.lift_comp_π]
  ext m
  change (skyscraperStalkEval x (F.presheaf.stalk x))
    ((toSkyscraper (LinearMap.id : F.presheaf.stalk x →ₗ[X.presheaf.stalk x]
      F.presheaf.stalk x)).stalkLinearMap x m) = m
  exact LinearMap.congr_fun
    ((skyscraperHomEquiv x (F.presheaf.stalk x) F).left_inv LinearMap.id) m

private theorem eval_natural (X : Scheme.{u}) {F G : X.Modules} (f : F ⟶ G) (x : X) :
    (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map (moduleCup_godementMap X f) ≫
      moduleCup_godementStalkEval X G x =
    moduleCup_godementStalkEval X F x ≫
      (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map f := by
  dsimp only [moduleCup_godementStalkEval]
  rw [← Functor.map_comp_assoc]
  simp only [moduleCup_godementMap, Pi.lift_comp_π, Functor.map_comp, Category.assoc]
  have he :
      (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
        (toSkyscraper (f.stalkLinearMap x ∘ₗ skyscraperStalkEval x (F.presheaf.stalk x))) ≫
          ModuleCat.ofHom (skyscraperStalkEval x (G.presheaf.stalk x)) =
      ModuleCat.ofHom (skyscraperStalkEval x (F.presheaf.stalk x)) ≫
        (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map f := by
    ext m
    change skyscraperStalkEval x (G.presheaf.stalk x)
      ((toSkyscraper (f.stalkLinearMap x ∘ₗ
        skyscraperStalkEval x (F.presheaf.stalk x))).stalkLinearMap x m) = _
    exact LinearMap.congr_fun
      ((skyscraperHomEquiv x (G.presheaf.stalk x) (skyscraper x (F.presheaf.stalk x))).left_inv
        (f.stalkLinearMap x ∘ₗ skyscraperStalkEval x (F.presheaf.stalk x))) m
  rw [he]

private instance stalkAdditive (X : Scheme.{u}) (x : X) :
    (RingedSpace.moduleStalkFunctor X.toRingedSpace x).Additive where
  map_add := by
    intro M N f g
    ext m
    change (TopCat.Presheaf.stalkFunctor Ab x).map
      ((PresheafOfModules.toPresheaf _).map (f + g).val) m = _
    change (TopCat.Presheaf.stalkFunctor Ab x).map
      ((PresheafOfModules.toPresheaf _).map (f.val + g.val)) m = _
    rw [Functor.map_add, Functor.map_add]
    rfl

private theorem insert_zero (X : Scheme.{u}) (F : X.Modules) (n : ℕ) :
    moduleCup_godementInsert X F (n + 1) 0 =
      moduleCup_godementUnit X (moduleCup_godementIterate X F (n + 1)) := by
  simp [moduleCup_godementInsert]

private theorem insert_succ (X : Scheme.{u}) (F : X.Modules) (n : ℕ)
    (i : Fin (n + 1)) :
    moduleCup_godementInsert X F (n + 1) i.succ =
      moduleCup_godementMap X (moduleCup_godementInsert X F n i) := by
  rw [moduleCup_godementInsert]
  split_ifs with hi
  · simp only [Fin.val_succ] at hi
    omega
  · congr 2

private theorem insert_sum_eval (X : Scheme.{u}) (F : X.Modules) (x : X) (n : ℕ) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
        (moduleCup_godementInsert X F (n + 1) i)) ≫
      moduleCup_godementStalkEval X (moduleCup_godementIterate X F (n + 1)) x =
    𝟙 _ - moduleCup_godementStalkEval X (moduleCup_godementIterate X F n) x ≫
      (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
        (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
          (moduleCup_godementInsert X F n i)) := by
  rw [Fin.sum_univ_succ, Preadditive.add_comp]
  simp only [Fin.val_zero, pow_zero, one_zsmul, insert_zero, eval_unit,
    Preadditive.neg_comp, Preadditive.sum_comp, insert_succ, Preadditive.zsmul_comp, eval_natural,
    Fin.val_succ, pow_succ, mul_neg_one, neg_zsmul, Preadditive.comp_sum,
    Preadditive.comp_zsmul, sub_eq_add_neg, Finset.sum_neg_distrib]
  rfl

/-- The stalk complex of the extended alternating coface complex.
Source: Stacks, Tag 0FKR (blueprint: lem-sc-module-cup-godement-stalk-contraction). -/
private abbrev moduleCup_godementStalkComplex (X : Scheme.{u})
    (A : CosimplicialObject X.Modules) (x : X) :=
  ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
    (.up ℤ)).obj
    (((alternatingCofaceMapComplex X.Modules).obj A).extend
      ComplexShape.embeddingUpNat)

/-- The source complex of the stalk augmentation.
Source: Stacks, Tag 0FKR (blueprint: lem-sc-module-cup-godement-stalk-contraction). -/
private abbrev moduleCup_godementStalkSingle (X : Scheme.{u}) (F : X.Modules) (x : X) :=
  ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
    (.up ℤ)).obj ((CochainComplex.singleFunctor X.Modules 0).obj F)

/-- Transport from a nonnegative term to its specified Godement iterate.
Source: Stacks, Tag 0FKR (blueprint: lem-sc-module-cup-godement-stalk-contraction). -/
private def moduleCup_godementStalkTermIso (X : Scheme.{u}) (F : X.Modules)
    (A : CosimplicialObject X.Modules)
    (ht : ∀ n : ℕ, A.obj ⦋n⦌ = moduleCup_godementIterate X F (n + 1))
    (x : X) (n : ℕ) :
    (moduleCup_godementStalkComplex X A x).X (n : ℤ) ≅
      (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        (moduleCup_godementIterate X F (n + 1)) :=
  (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapIso
    ((((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
      ComplexShape.embeddingUpNat (i := n) rfl) ≪≫ eqToIso (ht n))

private theorem term_d (X : Scheme.{u}) (F : X.Modules)
    (A : CosimplicialObject X.Modules)
    (ht : ∀ n : ℕ, A.obj ⦋n⦌ = moduleCup_godementIterate X F (n + 1))
    (hc : ∀ (n : ℕ) (i : Fin (n + 2)),
      eqToHom (ht n) ≫ moduleCup_godementInsert X F (n + 1) i =
        A.map (SimplexCategory.δ i) ≫ eqToHom (ht (n + 1))) (x : X) (n : ℕ) :
    (moduleCup_godementStalkComplex X A x).d n (n + 1) =
      (moduleCup_godementStalkTermIso X F A ht x n).hom ≫
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
            (moduleCup_godementInsert X F (n + 1) i)) ≫
      (moduleCup_godementStalkTermIso X F A ht x (n + 1)).inv := by
  let D := (alternatingCofaceMapComplex X.Modules).obj A
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  have hd : D.d n (n + 1) ≫ eqToHom (ht (n + 1)) =
      eqToHom (ht n) ≫
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          moduleCup_godementInsert X F (n + 1) i := by
    dsimp only [D, alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj]
    rw [CochainComplex.of_d]
    change (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • A.map (SimplexCategory.δ i)) ≫
      eqToHom (ht (n + 1)) = _
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp,
      Preadditive.comp_sum, Preadditive.comp_zsmul, hc]
  have hd' : D.d n (n + 1) =
      eqToHom (ht n) ≫
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          moduleCup_godementInsert X F (n + 1) i) ≫ eqToHom (ht (n + 1)).symm := by
    rw [← Category.assoc, ← hd, Category.assoc, eqToHom_trans]
    simp
  change S.map ((D.extend ComplexShape.embeddingUpNat).d n (n + 1)) = _
  rw [D.extend_d_eq ComplexShape.embeddingUpNat (i := n) (j := n + 1)
    (i' := (n : ℤ)) (j' := (n : ℤ) + 1) rfl (by simp)]
  rw [hd']
  simp only [moduleCup_godementStalkTermIso, Functor.mapIso, Iso.trans_hom,
    Iso.trans_inv, eqToIso.hom, eqToIso.inv, Functor.map_comp, Functor.map_sum,
    Functor.map_zsmul, Category.assoc]
  rfl

/-- The degree-zero retraction, given by coordinate evaluation.
Source: Stacks, Tag 0FKR (blueprint: lem-sc-module-cup-godement-stalk-contraction). -/
private def moduleCup_godementStalkRetractionZero (X : Scheme.{u}) (F : X.Modules)
    (A : CosimplicialObject X.Modules)
    (ht : ∀ n : ℕ, A.obj ⦋n⦌ = moduleCup_godementIterate X F (n + 1)) (x : X) :
    (moduleCup_godementStalkComplex X A x).X 0 ⟶
      (moduleCup_godementStalkSingle X F x).X 0 :=
  (moduleCup_godementStalkTermIso X F A ht x 0).hom ≫
    moduleCup_godementStalkEval X F x ≫
    (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).inv

/-- The evaluation retraction as a chain map, zero away from degree zero.
Source: Stacks, Tag 0FKR (blueprint: lem-sc-module-cup-godement-stalk-contraction). -/
private def moduleCup_godementStalkRetraction (X : Scheme.{u}) (F : X.Modules)
    (A : CosimplicialObject X.Modules)
    (ht : ∀ n : ℕ, A.obj ⦋n⦌ = moduleCup_godementIterate X F (n + 1)) (x : X) :
    moduleCup_godementStalkComplex X A x ⟶ moduleCup_godementStalkSingle X F x where
  f i := if hi : i = 0 then
      ((moduleCup_godementStalkComplex X A x).XIsoOfEq hi).hom ≫
        moduleCup_godementStalkRetractionZero X F A ht x ≫
        ((moduleCup_godementStalkSingle X F x).XIsoOfEq hi).inv
    else 0
  comm' i j hij := by
    by_cases hj : j = 0
    · rcases hj with rfl
      have hi : i < 0 := by change i + 1 = 0 at hij; omega
      apply (Functor.map_isZero (RingedSpace.moduleStalkFunctor X.toRingedSpace x)
        (CochainComplex.isZero_of_isStrictlyGE
          (((alternatingCofaceMapComplex X.Modules).obj A).extend
            ComplexShape.embeddingUpNat) 0 i hi)).eq_of_src
    · apply (Functor.map_isZero (RingedSpace.moduleStalkFunctor X.toRingedSpace x)
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 F j hj)).eq_of_tgt

/-- The degree-lowering evaluation maps, extended by zero to negative degrees.
Source: Stacks, Tag 0FKR (blueprint: lem-sc-module-cup-godement-stalk-contraction). -/
private def moduleCup_godementStalkHom (X : Scheme.{u}) (F : X.Modules)
    (A : CosimplicialObject X.Modules)
    (ht : ∀ n : ℕ, A.obj ⦋n⦌ = moduleCup_godementIterate X F (n + 1)) (x : X)
    (i j : ℤ) :
    (moduleCup_godementStalkComplex X A x).X i ⟶
      (moduleCup_godementStalkComplex X A x).X j :=
  if hij : i = j + 1 then
    if hj : 0 ≤ j then
      ((moduleCup_godementStalkComplex X A x).XIsoOfEq
        (show i = (j.toNat + 1 : ℕ) by omega)).hom ≫
      (moduleCup_godementStalkTermIso X F A ht x (j.toNat + 1)).hom ≫
      moduleCup_godementStalkEval X (moduleCup_godementIterate X F (j.toNat + 1)) x ≫
      (moduleCup_godementStalkTermIso X F A ht x j.toNat).inv ≫
      ((moduleCup_godementStalkComplex X A x).XIsoOfEq
        (show j = (j.toNat : ℤ) by omega)).inv
    else 0
  else 0

private theorem hom_succ (X : Scheme.{u}) (F : X.Modules)
    (A : CosimplicialObject X.Modules)
    (ht : ∀ n : ℕ, A.obj ⦋n⦌ = moduleCup_godementIterate X F (n + 1))
    (x : X) (n : ℕ) :
    moduleCup_godementStalkHom X F A ht x ((n : ℤ) + 1) n =
      (moduleCup_godementStalkTermIso X F A ht x (n + 1)).hom ≫
      moduleCup_godementStalkEval X (moduleCup_godementIterate X F (n + 1)) x ≫
      (moduleCup_godementStalkTermIso X F A ht x n).inv := by
  simp [moduleCup_godementStalkHom]

/-- Alternating-coface cancellation for the explicitly constructed stalk evaluation maps.
Source: Stacks Project, Tag 0FKR, proof of Lemma 20.30.1 (0FKS), using the
adjunction contraction in Simplicial, Lemma 14.34.3.
(blueprint: lem-sc-module-cup-godement-stalk-contraction)
Proof: evaluation of the x-coordinate after the outer germ insertion is the
identity. Evaluation is natural in the module sheaf: composing the map of
products with evaluation equals evaluation followed by the original stalk map.
Hence evaluation after insertion at position i+1 equals insertion at i after
evaluation. Apply these identities to the cofaces specified by ht and hc.
In positive degrees the alternating sums cancel in pairs, leaving the identity.
In degree zero the missing last summand is evaluation followed by the germ
augmentation, which is exactly the degree-zero component of r followed by a
by ha. In negative degrees every term is zero. Transport via extendXIso and
ht, and use additivity of the stalk functor, to obtain the displayed identity.
This statement asserts only the differential calculation for fixed explicit
maps; it does not assert that the augmentation followed by r is the identity
or package either chain homotopy or a homotopy equivalence. -/
private theorem moduleCup_godement_stalk_identity (X : Scheme.{u}) (F : X.Modules)
    (A : CosimplicialObject X.Modules)
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
      (((alternatingCofaceMapComplex X.Modules).obj A).extend
        ComplexShape.embeddingUpNat))
    (ht : ∀ n : ℕ, A.obj ⦋n⦌ = moduleCup_godementIterate X F (n + 1))
    (hc : ∀ (n : ℕ) (i : Fin (n + 2)),
      eqToHom (ht n) ≫ moduleCup_godementInsert X F (n + 1) i =
        A.map (SimplexCategory.δ i) ≫ eqToHom (ht (n + 1)))
    (ha : a.f 0 ≫ (((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
      ComplexShape.embeddingUpNat (i := 0) rfl).hom ≫ eqToHom (ht 0) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).hom ≫ moduleCup_godementUnit X F)
    (x : X) (i : ℤ) :
    dNext i (moduleCup_godementStalkHom X F A ht x) +
      prevD i (moduleCup_godementStalkHom X F A ht x) =
    (HomologicalComplex.id (moduleCup_godementStalkComplex X A x)).f i -
      (moduleCup_godementStalkRetraction X F A ht x ≫
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (.up ℤ)).map a).f i := by
  let K := moduleCup_godementStalkComplex X A x
  let H := moduleCup_godementStalkHom X F A ht x
  let b := ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
    (.up ℤ)).map a
  let r := moduleCup_godementStalkRetraction X F A ht x
  change dNext i H + prevD i H = 𝟙 (K.X i) - (r.f i ≫ b.f i)
  cases i with
  | negSucc n =>
    apply (Functor.map_isZero (RingedSpace.moduleStalkFunctor X.toRingedSpace x)
      (CochainComplex.isZero_of_isStrictlyGE
        (((alternatingCofaceMapComplex X.Modules).obj A).extend
          ComplexShape.embeddingUpNat) 0 (Int.negSucc n) (by omega))).eq_of_src
  | ofNat n =>
    cases n with
    | zero =>
      erw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by rfl),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by rfl)]
      have hneg : moduleCup_godementStalkHom X F A ht x 0 (-1) = 0 := by
        dsimp only [moduleCup_godementStalkHom]
        rw [dite_eq_left (by omega), dite_eq_right (by omega)]
      have h01 := hom_succ X F A ht x 0
      have hd0 := term_d X F A ht hc x 0
      simp only [Int.natCast_zero] at h01 hd0
      dsimp only [H]
      erw [h01, hneg, zero_comp, add_zero, hd0]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
      let e := moduleCup_godementStalkTermIso X F A ht x 0
      have hab : b.f 0 ≫ e.hom =
          S.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).hom ≫
            S.map (moduleCup_godementUnit X F) := by
        change S.map (a.f 0) ≫
          S.map ((((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
            ComplexShape.embeddingUpNat (i := 0) rfl).hom ≫ eqToHom (ht 0)) = _
        rw [← Functor.map_comp, ha, Functor.map_comp]
      have hb : S.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).inv ≫ b.f 0 =
          S.map (moduleCup_godementUnit X F) ≫ e.inv := by
        apply (cancel_mono e.hom).mp
        rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, hab,
          ← Category.assoc, ← Functor.map_comp]
        simp
      have hr : r.f 0 = e.hom ≫ moduleCup_godementStalkEval X F x ≫
          S.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).inv := by
        rfl
      have hrb : r.f 0 ≫ b.f 0 =
          e.hom ≫ moduleCup_godementStalkEval X F x ≫
            S.map (moduleCup_godementUnit X F) ≫ e.inv := by
        rw [hr, Category.assoc, Category.assoc, hb]
      erw [hrb]
      have he0 := insert_sum_eval X F x 0
      erw [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_zsmul] at he0
      change e.hom ≫
          (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • S.map (moduleCup_godementInsert X F 1 i)) ≫
          moduleCup_godementStalkEval X (moduleCup_godementIterate X F 1) x ≫ e.inv =
        𝟙 (K.X 0) -
          e.hom ≫ moduleCup_godementStalkEval X F x ≫
            S.map (moduleCup_godementUnit X F) ≫ e.inv
      rw [← Category.assoc
        (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • S.map (moduleCup_godementInsert X F 1 i))]
      rw [he0]
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc]
      erw [Category.id_comp, Iso.hom_inv_id]
      rfl
    | succ n =>
      change dNext ((n : ℤ) + 1) H + prevD ((n : ℤ) + 1) H = _
      erw [dNext_eq (C := moduleCup_godementStalkComplex X A x)
          (D := moduleCup_godementStalkComplex X A x) _
          (show (ComplexShape.up ℤ).Rel ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) by rfl),
        prevD_eq (C := moduleCup_godementStalkComplex X A x)
          (D := moduleCup_godementStalkComplex X A x) _
          (show (ComplexShape.up ℤ).Rel (n : ℤ) ((n : ℤ) + 1) by rfl)]
      dsimp only [H]
      have hs := hom_succ X F A ht x (n + 1)
      have hd := term_d X F A ht hc x (n + 1)
      simp only [Int.natCast_add, Int.natCast_one] at hs hd
      erw [hs, hom_succ X F A ht x n, hd, term_d X F A ht hc x n]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      have hr : r.f (Int.ofNat (n + 1)) = 0 := by
        dsimp only [r, moduleCup_godementStalkRetraction]
        split_ifs with hi
        · norm_num at hi
          omega
        · rfl
      rw [hr, zero_comp, sub_zero, ← Preadditive.comp_add]
      simp only [← Category.assoc]
      rw [← Preadditive.add_comp, insert_sum_eval, sub_add_cancel]
      erw [Category.id_comp, Iso.hom_inv_id]
      rfl



/-- Each stalk of the actual Godement model has a contracting augmented complex.
Source: Stacks Project, Tag 0FKR, Lemma 20.30.1 (0FKS).
(blueprint: lem-sc-module-cup-godement-stalk-contraction)
Proof: fix x. Project T(H) to the skyscraper of H_x, apply the module stalk
functor at x, and then apply skyscraperStalkEval. This defines e_H:(T(H))_x to H_x.
The product germ unit followed by e_H is the identity, by the stalk-skyscraper
adjunction. Evaluation is natural in H, so for every inner unit-insertion face
e_H commutes with it with its index shifted down by one. For the outer face,
evaluation following insertion is the identity. Transport these equations
through the term equalities of ModuleCupGodementModel. Alternating the cofaces
then gives d h+h d=id in positive degrees. In degree zero it gives
h d=id-a r, where r is e_F after the degree-zero identifications. Also r a=id
and r is a chain map to F_x[0]. Set all maps in negative degrees to zero.
These equations supply a homotopy between a r and the identity, and the
identity r a supplies the other homotopy, thus a homotopy equivalence whose
forward map is the stalk augmentation. No global exactness or flasqueness
is assumed, and the assertion at a point is unused for the empty scheme. -/
theorem moduleCup_godement_stalk_contraction (X : Scheme.{u}) (F : X.Modules)
    (A : CosimplicialObject X.Modules)
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
      (((alternatingCofaceMapComplex X.Modules).obj A).extend
        ComplexShape.embeddingUpNat))
    (h : ModuleCupGodementModel X F A a) (x : X) :
    HomologicalComplex.homotopyEquivalences
      (ModuleCat.{u} (X.presheaf.stalk x)) (.up ℤ)
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
        (.up ℤ)).map a) := by
  obtain ⟨ht, hc, ha⟩ := h
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  let b := (S.mapHomologicalComplex (.up ℤ)).map a
  let r := moduleCup_godementStalkRetraction X F A ht x
  have hbr : b ≫ r = 𝟙 _ := by
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : i = 0
    · subst i
      change S.map (a.f 0) ≫ (r.f 0) = 𝟙 _
      change S.map (a.f 0) ≫ moduleCup_godementStalkRetractionZero X F A ht x = 𝟙 _
      dsimp only [moduleCup_godementStalkRetractionZero, moduleCup_godementStalkTermIso,
        Functor.mapIso, Iso.trans_hom, eqToIso.hom]
      rw [← Functor.map_comp_assoc, ha,
        Functor.map_comp, Category.assoc]
      rw [← Category.assoc (S.map (moduleCup_godementUnit X F)),
        eval_unit, Category.id_comp]
      exact S.map_comp _ _ |>.symm.trans (by simp)
    · apply (Functor.map_isZero S
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 F i hi)).eq_of_src
  have H : Homotopy (𝟙 (moduleCup_godementStalkComplex X A x)) (r ≫ b) :=
    { hom := moduleCup_godementStalkHom X F A ht x
      zero := by
        intro i j hij
        dsimp only [moduleCup_godementStalkHom]
        rw [dite_eq_right]
        simpa only [ComplexShape.up_Rel, eq_comm] using hij
      comm := by
        intro i
        rw [moduleCup_godement_stalk_identity X F A a ht hc ha x i]
        exact (sub_add_cancel _ _).symm }
  exact ⟨{ hom := b
           inv := r
           homotopyHomInvId := Homotopy.ofEq hbr
           homotopyInvHomId := H.symm }, rfl⟩

end
end AlgebraicGeometry.Scheme.Modules
