/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.PinnedSingleBaseChangeShift
import WeilConjectures.AlgebraicGeometry.IsomorphicSingleTensorCounit
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangePasting

/-! # Invariance of the pinned single comparison under an isomorphic apex
Source: Stacks Project, Tags 08HY and 08IB.
(blueprint: lem-pc-open-pinned-single-degree-zero-apex). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

private theorem assemble_apex
    {C : Type*} [Category C] {A B B' D E F G H : C}
    (b : A ⟶ B) (x : B ⟶ D) (k₁ : B ⟶ B') (k₂ : D ⟶ E)
    (d : B' ⟶ F) (c : F ⟶ B') (y : B' ⟶ E) (t : E ⟶ H)
    (b₀ : A ⟶ G) (u : G ⟶ F) (z : G ⟶ H)
    (hn : x ≫ k₂ = k₁ ≫ y) (hp : b ≫ k₁ ≫ d = b₀ ≫ u)
    (hd : d ≫ c = 𝟙 B') (hc : u ≫ c ≫ y ≫ t = z) :
    b ≫ x ≫ k₂ ≫ t = b₀ ≫ z := by
  calc
    _ = b ≫ k₁ ≫ y ≫ t := by rw [← Category.assoc x k₂, hn, Category.assoc]
    _ = b ≫ k₁ ≫ d ≫ c ≫ y ≫ t := by rw [← Category.assoc d c, hd, Category.id_comp]
    _ = b₀ ≫ u ≫ c ≫ y ≫ t := by rw [reassoc_of% hp]
    _ = _ := by rw [hc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Changing only the apex of a commutative square by an isomorphism preserves the
pinned single-complex comparison. This statement has no open-restriction data.
Source: Stacks Project, Tags 08HY and 08IB.
(blueprint: lem-pc-open-pinned-single-degree-zero-apex).
Proof: transport tensor pullback along the apex isomorphism, using uniqueness of
left adjoints to the composite pushforward. Tensor pullback along an isomorphism
is an exact equivalence. Its single-complex comparison is therefore invertible.
Derive the pushforward composition comparison and combine it with this single
comparison to construct v. Transpose base change under the pinned derived
adjunctions. The composition comparisons are pinned to the same counits; their
associativity identifies both transposes. The counit factorization equation then
identifies the final single tensor comparisons. Naturality assembles these
component equalities into the displayed functor isomorphism. No flatness,
properness or nonemptiness assumptions enter. -/
theorem open_pinned_single_degree_zero_apex
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X S Z P T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (j : Z ⟶ X) (r : Z ⟶ T) (p : P ⟶ X) (q : P ⟶ T)
    (h : j ≫ f = r ≫ g) (hP : p ≫ f = q ≫ g)
    (e : Z ≅ P) (hj : e.hom ≫ p = j) (hr : e.hom ≫ q = r) :
    ∃ v : singleDegreeBaseChangeTarget.{u, w} j r 0 ≅
        singleDegreeBaseChangeTarget.{u, w} p q 0,
      ∀ M : X.Modules,
        singleDegreeBaseChangeComposite f g j r h 0 M ≫ v.hom.app M =
          singleDegreeBaseChangeComposite f g p q hP 0 M := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  subst j
  subst r
  let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
  let a := fun {A B : Scheme.{u}} (s : A ⟶ B) ↦
    Classical.choose (exists_schemeDerivedAdjunction s
      (hAdd := (Classical.choose exists_derivedPullbackComposition) s)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) s)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) s))
  let k := conjugateIsoEquiv (a (e.hom ≫ q)) ((a q).comp (a e.hom)) (c e.hom q)
  obtain ⟨t, ht⟩ := exists_isomorphic_single_tensor_counit.{u, w} p e
  let v : singleDegreeBaseChangeTarget.{u, w} (e.hom ≫ p) (e.hom ≫ q) 0 ≅
      singleDegreeBaseChangeTarget.{u, w} p q 0 :=
    Functor.isoWhiskerLeft _ k ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight t (schemeDerivedDirectImage q)
  refine ⟨v, ?_⟩
  intro M
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
  have past := schemeDerivedBaseChange_pasting f g p q hP e.hom K
  have hc := ht M
  dsimp only at hc
  have hv : v.hom.app M = k.hom.app _ ≫ (schemeDerivedDirectImage q).map
      (t.hom.app M) := by
    simp only [v, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Iso.symm_hom, Functor.associator_inv_app, Category.id_comp]
  let Q := schemeDerivedDirectImage q
  let U := schemeDerivedDirectImage e.hom
  let cj := pinnedSingleTensorCounit (e.hom ≫ p) 0 M
  let cp := pinnedSingleTensorCounit p 0 M
  let b := schemeDerivedBaseChangeMap f (e.hom ≫ q) g (e.hom ≫ p) h K
  let b₀ := schemeDerivedBaseChangeMap f q g p hP K
  have hn : (schemeDerivedDirectImage (e.hom ≫ q)).map cj ≫ k.hom.app _ =
      k.hom.app _ ≫ Q.map (U.map cj) := k.hom.naturality cj
  have hp : b ≫ k.hom.app _ ≫ Q.map (U.map ((c e.hom p).inv.app K)) =
      b₀ ≫ Q.map ((a e.hom).unit.app ((derivedPullback p).obj K)) := past
  have hd : Q.map (U.map ((c e.hom p).inv.app K)) ≫
      Q.map (U.map ((c e.hom p).hom.app K)) = 𝟙 _ := by
    rw [← Q.map_comp, ← U.map_comp, Iso.inv_hom_id_app, U.map_id, Q.map_id]
  have hc' : Q.map ((a e.hom).unit.app ((derivedPullback p).obj K)) ≫
      Q.map (U.map ((c e.hom p).hom.app K)) ≫ Q.map (U.map cj) ≫
      Q.map (t.hom.app M) = Q.map cp := by
    simpa only [Functor.map_comp, Category.assoc] using congrArg Q.map hc
  have finish := assemble_apex b ((schemeDerivedDirectImage (e.hom ≫ q)).map cj)
    (k.hom.app _) (k.hom.app _) (Q.map (U.map ((c e.hom p).inv.app K)))
    (Q.map (U.map ((c e.hom p).hom.app K))) (Q.map (U.map cj))
    (Q.map (t.hom.app M)) b₀
    (Q.map ((a e.hom).unit.app ((derivedPullback p).obj K))) (Q.map cp) hn hp hd hc'
  change (b ≫ (schemeDerivedDirectImage (e.hom ≫ q)).map cj) ≫ v.hom.app M =
    b₀ ≫ Q.map cp
  rw [hv]
  simpa only [singleDegreeBaseChangeTarget, Functor.comp_obj, Category.assoc] using finish

end AlgebraicGeometry
