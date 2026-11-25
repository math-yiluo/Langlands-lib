/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.LimitResidueField
import WeilConjectures.AlgebraicGeometry.AffineFibreProductTransition
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-!
# Fibre products commute with limits along affine transition morphisms

Source: Stacks Project, Derived Categories, proof of Lemma 0G7X (line 8166),
with Categories Lemma 002M and Morphisms Lemmas 01SD, 01SC, 01SG
(blueprint: lem-weil-pbc-limit-fibre-products).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Fibre products and scheme-theoretic fibres commute with the given affine-transition
limits, including their canonical projections. Equalities of objects and `HEq` of maps
identify the chosen representatives without introducing extra isomorphism choices.

Source: Stacks Project, proof of Lemma 0G7X, the limit argument, and Tags 002M,
01SD, 01SC, 01SG (blueprint: lem-weil-pbc-limit-fibre-products).

Proof:
1. Form the pointwise pullback diagram with Mathlib's `PullbackCone.combine`.
   The projections from `pullback F G` to the stage pullbacks are `pullback.lift`
   applied to the given limit projections. For any cone over this diagram, its
   composites with the two pullback projections give cones over X and T. Their
   universal maps have equal composites to S by `hcS.hom_ext`, so `pullback.lift`
   defines the required map. The projection identities prove factorization;
   `pullback.hom_ext`, `hcX.hom_ext` and `hcT.hom_ext` prove uniqueness.
2. Each transition between stage pullbacks is affine by
   lem-weil-pbc-fibre-product-affine-transition: factor via the affine diagonal of
   the base transition and the base changes of the affine transitions on X and T.
   Use stability under base change and composition (01SD, 01SC, 01SG).
3. `exists_isColimit_residueField_of_isLimit` (lem-weil-pbc-limit-residue-field)
   identifies the residue-field point of s with the limit of its stage points.
   Apply steps 1 and 2 to X, S and these residue-field spectra. This gives the
   limiting fibre cone with affine transitions and the stated projections to X.
   `Functor.copyObj` transports the residue-field spectra to the exact stage
   objects. The theorem's canonical-map identities give a natural transformation
   to S and the specified limiting cone. Apply step 1 with these spectra as T;
   the resulting pullbacks are definitionally the required fibres. -/
theorem limit_fibre_products_of_affine_transition
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (X S T : Iᵒᵖ ⥤ Scheme.{u})
    (f : X ⟶ S) (g : T ⟶ S)
    [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (X.map h)]
    [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (S.map h)]
    [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (T.map h)]
    (cX : Cone X) (hcX : IsLimit cX)
    (cS : Cone S) (hcS : IsLimit cS)
    (cT : Cone T) (hcT : IsLimit cT)
    (F : cX.pt ⟶ cS.pt) (G : cT.pt ⟶ cS.pt)
    (hF : ∀ i : Iᵒᵖ, F ≫ cS.π.app i = cX.π.app i ≫ f.app i)
    (hG : ∀ i : Iᵒᵖ, G ≫ cS.π.app i = cT.π.app i ≫ g.app i) :
    (∃ (P : Iᵒᵖ ⥤ Scheme.{u}) (a : P ⟶ X) (b : P ⟶ T) (cP : Cone P),
      (∀ i : Iᵒᵖ, P.obj i = pullback (f.app i) (g.app i)) ∧
      (∀ i : Iᵒᵖ, HEq (a.app i) (pullback.fst (f.app i) (g.app i))) ∧
      (∀ i : Iᵒᵖ, HEq (b.app i) (pullback.snd (f.app i) (g.app i))) ∧
      (∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (P.map h)) ∧
      cP.pt = pullback F G ∧
      (∀ i : Iᵒᵖ, HEq (cP.π.app i ≫ a.app i)
        (pullback.fst F G ≫ cX.π.app i)) ∧
      (∀ i : Iᵒᵖ, HEq (cP.π.app i ≫ b.app i)
        (pullback.snd F G ≫ cT.π.app i)) ∧
      Nonempty (IsLimit cP)) ∧
    (∀ s : cS.pt, ∃ (Q : Iᵒᵖ ⥤ Scheme.{u}) (a : Q ⟶ X) (cQ : Cone Q),
      (∀ i : Iᵒᵖ, Q.obj i = (f.app i).fiber (cS.π.app i s)) ∧
      (∀ i : Iᵒᵖ, HEq (a.app i) ((f.app i).fiberι (cS.π.app i s))) ∧
      (∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (Q.map h)) ∧
      cQ.pt = F.fiber s ∧
      (∀ i : Iᵒᵖ, HEq (cQ.π.app i ≫ a.app i) (F.fiberι s ≫ cX.π.app i)) ∧
      Nonempty (IsLimit cQ)) := by
  -- First prove the pullback assertion uniformly, so it also applies to residue spectra.
  have hpb
      (X S T : Iᵒᵖ ⥤ Scheme.{u}) (f : X ⟶ S) (g : T ⟶ S)
      [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (X.map h)]
      [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (S.map h)]
      [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (T.map h)]
      (cX : Cone X) (hcX : IsLimit cX) (cS : Cone S) (hcS : IsLimit cS)
      (cT : Cone T) (hcT : IsLimit cT) (F : cX.pt ⟶ cS.pt) (G : cT.pt ⟶ cS.pt)
      (hF : ∀ i : Iᵒᵖ, F ≫ cS.π.app i = cX.π.app i ≫ f.app i)
      (hG : ∀ i : Iᵒᵖ, G ≫ cS.π.app i = cT.π.app i ≫ g.app i) :
      ∃ (P : Iᵒᵖ ⥤ Scheme.{u}) (a : P ⟶ X) (b : P ⟶ T) (cP : Cone P),
        (∀ i : Iᵒᵖ, P.obj i = pullback (f.app i) (g.app i)) ∧
        (∀ i : Iᵒᵖ, HEq (a.app i) (pullback.fst (f.app i) (g.app i))) ∧
        (∀ i : Iᵒᵖ, HEq (b.app i) (pullback.snd (f.app i) (g.app i))) ∧
        (∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (P.map h)) ∧ cP.pt = pullback F G ∧
        (∀ i : Iᵒᵖ, HEq (cP.π.app i ≫ a.app i) (pullback.fst F G ≫ cX.π.app i)) ∧
        (∀ i : Iᵒᵖ, HEq (cP.π.app i ≫ b.app i) (pullback.snd F G ≫ cT.π.app i)) ∧
        Nonempty (IsLimit cP) := by
    classical
    let d := PullbackCone.combine f g (fun i ↦ pullback.cone (f.app i) (g.app i))
      (fun i ↦ pullback.isLimit (f.app i) (g.app i))
    let P := d.pt
    let a := d.fst
    let b := d.snd
    have ha (i) : a.app i = pullback.fst (f.app i) (g.app i) := rfl
    have hb (i) : b.app i = pullback.snd (f.app i) (g.app i) := rfl
    have hab (i) : a.app i ≫ f.app i = b.app i ≫ g.app i := pullback.condition
    have hm {i j} (h : i ⟶ j) : P.map h =
        pullback.map (f.app i) (g.app i) (f.app j) (g.app j)
          (X.map h) (T.map h) (S.map h) (f.naturality h).symm (g.naturality h).symm := by
      apply pullback.hom_ext
      · simpa only [ha, pullback.lift_fst] using a.naturality h
      · simpa only [hb, pullback.lift_snd] using b.naturality h
    let cP : Cone P := {
      pt := pullback F G
      π := {
        app i := pullback.lift (pullback.fst F G ≫ cX.π.app i)
          (pullback.snd F G ≫ cT.π.app i) (by
            rw [Category.assoc, ← hF, ← Category.assoc, pullback.condition,
              Category.assoc, hG, Category.assoc])
        naturality i j h := by
          dsimp
          apply pullback.hom_ext
          · simp [hm, Category.assoc]
          · simp [hm, Category.assoc] } }
    have hlim : IsLimit cP := {
      lift q := pullback.lift (hcX.map q a) (hcT.map q b) (by
        apply hcS.hom_ext
        intro i
        simp only [Category.assoc, hF, hG, IsLimit.map_π_assoc]
        exact congrArg (q.π.app i ≫ ·) (hab i))
      fac q i := by
        apply pullback.hom_ext <;> simp [cP, ha, hb, Category.assoc]
      uniq q m hm' := by
        apply pullback.hom_ext
        · apply hcX.hom_ext
          intro i
          have hh := congrArg (· ≫ a.app i) (hm' i)
          simpa [cP, a, ha, Category.assoc] using hh
        · apply hcT.hom_ext
          intro i
          have hh := congrArg (· ≫ b.app i) (hm' i)
          simpa [cP, b, hb, Category.assoc] using hh }
    refine ⟨P, a, b, cP, (fun _ ↦ rfl), (fun _ ↦ HEq.rfl),
      (fun _ ↦ HEq.rfl), ?_, rfl, ?_, ?_, ⟨hlim⟩⟩
    · intro i j h
      rw [hm]
      exact isAffineHom_pullback_map _ _ _ _ _ _ _ _ _
    · intro i
      exact heq_of_eq (pullback.lift_fst _ _ _)
    · intro i
      exact heq_of_eq (pullback.lift_snd _ _ _)
  constructor
  · exact hpb X S T f g cX hcX cS hcS cT hcT F G hF hG
  · intro s
    obtain ⟨R, r, hR, hRm, hr, hri, hrlim, ⟨t, ht, htp, ⟨htlim⟩, htAff⟩, hproj, hnat⟩ :=
      exists_isColimit_residueField_of_isLimit S cS hcS s
    let D := R.op ⋙ Scheme.Spec
    let e (i : Iᵒᵖ) : D.obj i ≅ Spec ((S.obj i).residueField (cS.π.app i s)) :=
      eqToIso (congrArg Spec (hR i.unop))
    let E := D.copyObj (fun i ↦ Spec ((S.obj i).residueField (cS.π.app i s))) e
    let isoE : D ≅ E := D.isoCopyObj _ e
    have hp {i j : Iᵒᵖ} (h : i ⟶ j) :
        S.map h (cS.π.app i s) = cS.π.app j s := by
      exact congrArg (fun k : cS.pt ⟶ S.obj j ↦ k s) (cS.w h)
    have hmap {i j : Iᵒᵖ} (h : i ⟶ j) :
        HEq (E.map h) (Spec.map ((S.map h).residueFieldMap (cS.π.app i s))) := by
      dsimp [E, Functor.copyObj, e, eqToIso]
      simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
      have hh := hRm j.unop i.unop h.unop
      have hdom : R.obj j.unop =
          (S.obj j).residueField (S.map h (cS.π.app i s)) := by
        rw [hp h]
        exact hR j.unop
      have hcod := hR i.unop
      have hspec {A B A' B' : CommRingCat.{u}}
          (ha : A = A') (hb : B = B') (m : A ⟶ B) (m' : A' ⟶ B')
          (hm : HEq m m') : HEq (Spec.map m) (Spec.map m') := by
        cases ha
        cases hb
        cases hm
        rfl
      exact hspec hdom hcod _ _ hh
    let gE : E ⟶ S := {
      app i := (S.obj i).fromSpecResidueField (cS.π.app i s)
      naturality i j h := by
        have hh := hnat j.unop i.unop h.unop
        have hfrom : HEq ((S.obj j).fromSpecResidueField (cS.π.app j s))
            ((S.obj j).fromSpecResidueField (S.map h (cS.π.app i s))) := by
          exact congr_arg_heq (S.obj j).fromSpecResidueField (hp h).symm
        have hh' := heq_comp rfl
          (congrArg (fun x ↦ Spec ((S.obj j).residueField x)) (hp h).symm) rfl
          (hmap h) hfrom
        exact eq_of_heq (hh'.trans (heq_of_eq hh)) }
    let cE : Cone E :=
      ((Cone.postcompose isoE.hom).obj t).extend (eqToHom ht.symm)
    have hcE : IsLimit cE :=
      IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv isoE t).symm htlim)
        (Cone.extendIso ((Cone.postcompose isoE.hom).obj t) (eqToIso ht))
    have hEπ (i : Iᵒᵖ) : cE.π.app i =
        Spec.map ((cS.π.app i).residueFieldMap s) := by
      apply eq_of_heq
      dsimp [cE, Cone.extend, Cone.postcompose, isoE, Functor.isoCopyObj, e, eqToIso]
      simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
      exact htp i.unop
    have hE (i : Iᵒᵖ) :
        cS.pt.fromSpecResidueField s ≫ cS.π.app i = cE.π.app i ≫ gE.app i := by
      rw [hEπ]
      exact (hproj i.unop).symm
    have instE {i j : Iᵒᵖ} (h : i ⟶ j) : IsAffineHom (E.map h) := by
      dsimp [E, Functor.copyObj]
      have : IsAffineHom (D.map h) := htAff h
      infer_instance
    obtain ⟨Q, a, b, cQ, hQ, ha, hb, hQa, hpt, hπ, hπb, hlim⟩ :=
      hpb X S E f gE cX hcX cS hcS cE hcE F
        (cS.pt.fromSpecResidueField s) hF hE
    exact ⟨Q, a, cQ, hQ, ha, hQa, hpt, hπ, hlim⟩

end AlgebraicGeometry
