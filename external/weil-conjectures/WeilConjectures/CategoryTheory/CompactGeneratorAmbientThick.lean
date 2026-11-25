/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

import WeilConjectures.CategoryTheory.CompactHomHocolim
import WeilConjectures.CategoryTheory.CompactFactorThroughThick
import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Compact objects lie in the ambient thick envelope of a compact generator

Source: Stacks Project, Tags 09SN, 09SP and 094A.
(blueprint: lem-sc-compact-generator-ambient-thick).
-/

@[expose] public section

universe u v w

open CategoryTheory.Limits

namespace CategoryTheory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ambient_telescope_factor
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C]
    (A : ObjectProperty C) [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    [HasCoproducts.{w} A.FullSubcategory]
    [∀ I : Type w, A.IsClosedUnderColimitsOfShape (Discrete I)]
    (P : A.FullSubcategory) (hP : IsCompactObject P)
    (X : ℕ → A.FullSubcategory) (t : ∀ n : ℕ, (X n).obj ⟶ (X (n + 1)).obj)
    (S : Cofan (fun n : ℕ ↦ (X n).obj)) (hS : IsColimit S)
    (s : S.pt ⟶ S.pt) (q : S.pt ⟶ P.obj) (r : P.obj ⟶ S.pt⟦(1 : ℤ)⟧)
    (hs : ∀ n : ℕ, S.inj n ≫ s = t n ≫ S.inj (n + 1))
    (hT : Pretriangulated.Triangle.mk (𝟙 S.pt - s) q r ∈ distTriang C) :
    ∃ (n : ℕ) (a : P.obj ⟶ (X n).obj), a ≫ S.inj n ≫ q = 𝟙 P.obj := by
  classical
  -- The ambient cofan restricts to A after raising its index universe.
  let Y : ULift.{w} ℕ → A.FullSubcategory := fun n ↦ X n.down
  let c : Cofan (fun n : ULift.{w} ℕ ↦ (X n.down).obj) :=
    Cofan.mk S.pt (fun n ↦ S.inj n.down)
  have hc : IsColimit c :=
    (Cofan.isColimitEquivOfEquiv (Equiv.ulift : ULift.{w} ℕ ≃ ℕ) S) hS
  have hAS : A S.pt := A.prop_of_isColimit (c := c) hc (fun n ↦ (X n.as.down).property)
  let Z : A.FullSubcategory := ⟨S.pt, hAS⟩
  let cA : Cofan Y := Cofan.mk Z (fun n ↦ ObjectProperty.homMk (S.inj n.down))
  have hcA : IsColimit cA := by
    refine Cofan.IsColimit.mk _ (fun d ↦ ObjectProperty.homMk
      (hc.desc (Cofan.mk d.pt.obj (fun n ↦ (d.inj n).hom)))) ?_ ?_
    · intro d n
      apply ObjectProperty.hom_ext
      exact hc.fac _ ⟨n⟩
    · intro d m hm
      apply ObjectProperty.hom_ext
      apply hc.hom_ext
      intro n
      exact (congrArg InducedCategory.Hom.hom (hm n.as)).trans
        (hc.fac (Cofan.mk d.pt.obj (fun n ↦ (d.inj n).hom)) n).symm
  let e : (∐ Y) ≅ Z := (coproductIsCoproduct Y).coconePointUniqueUpToIso hcA
  have he (n : ULift.{w} ℕ) : Sigma.ι Y n ≫ e.hom = cA.inj n :=
    (coproductIsCoproduct Y).comp_coconePointUniqueUpToIso_hom hcA ⟨n⟩
  let tA : ∀ n : ℕ, X n ⟶ X (n + 1) := fun n ↦ ObjectProperty.homMk (t n)
  let F := Functor.ofSequence tA
  let d : (∐ Y) ⟶ ∐ Y := 𝟙 _ - Sigma.desc
    (fun n : ULift.{w} ℕ ↦ tA n.down ≫ Sigma.ι Y ⟨n.down + 1⟩)
  let sA : Z ⟶ Z := ObjectProperty.homMk s
  have hde : d ≫ e.hom = e.hom ≫ (𝟙 Z - sA) := by
    apply Sigma.hom_ext
    intro n
    dsimp only [d]
    rw [← Category.assoc]
    rw [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp, Sigma.ι_comp_desc,
      Category.assoc (tA n.down), he,
      ← Category.assoc (Sigma.ι Y n), he, Preadditive.comp_sub, Category.comp_id]
    simp only [he]
    congr 1
    apply ObjectProperty.hom_ext
    exact (hs n.down).symm
  let qA : Z ⟶ P := ObjectProperty.homMk q
  let rA : P ⟶ Z⟦(1 : ℤ)⟧ := ObjectProperty.homMk
    (r ≫ (A.ι.commShiftIso (1 : ℤ)).inv.app Z)
  have hTA : Pretriangulated.Triangle.mk (𝟙 Z - sA) qA rA ∈
      distTriang A.FullSubcategory := by
    change A.ι.mapTriangle.obj _ ∈ distTriang C
    have hmap : A.ι.map (𝟙 Z - sA) = 𝟙 S.pt - s := by
      rw [Functor.map_sub, Functor.map_id]
      rfl
    change Pretriangulated.Triangle.mk (A.ι.map (𝟙 Z - sA)) q
      ((r ≫ (A.ι.commShiftIso (1 : ℤ)).inv.app Z) ≫
        (A.ι.commShiftIso (1 : ℤ)).hom.app Z) ∈ distTriang C
    rw [hmap, Category.assoc, Iso.inv_hom_id_app]
    change Pretriangulated.Triangle.mk (𝟙 S.pt - s) q (r ≫ 𝟙 _) ∈ distTriang C
    rw [Category.comp_id]
    exact hT
  have hT' : Pretriangulated.Triangle.mk d (e.hom ≫ qA)
      (rA ≫ (shiftFunctor A.FullSubcategory (1 : ℤ)).map e.inv) ∈
      distTriang A.FullSubcategory := by
    apply Pretriangulated.isomorphic_distinguished _ hTA
    exact Pretriangulated.Triangle.isoMk _ _ e e (Iso.refl P)
      hde (by simp only [Pretriangulated.Triangle.mk, Category.comp_id, Iso.refl_hom])
      (by simp only [Pretriangulated.Triangle.mk, Category.assoc, ← Functor.map_comp,
        e.inv_hom_id, Functor.map_id, Category.comp_id, Iso.refl_hom, Category.id_comp])
  have hTF : Pretriangulated.Triangle.mk
      (𝟙 (∐ fun n : ULift.{w} ℕ ↦ F.obj n.down) -
        Sigma.desc (fun n : ULift.{w} ℕ ↦
          F.map (homOfLE (Nat.le_succ n.down)) ≫
            Sigma.ι (fun k : ULift.{w} ℕ ↦ F.obj k.down) ⟨n.down + 1⟩))
      (e.hom ≫ qA) (rA ≫ (shiftFunctor A.FullSubcategory (1 : ℤ)).map e.inv) ∈
      distTriang A.FullSubcategory := by
    simpa [F, Functor.ofSequence, Functor.OfSequence.map_le_succ, d, Y] using hT'
  -- Surjectivity on compact Hom puts the identity at a single finite stage.
  obtain ⟨φ, hφ, hbij⟩ := compact_hom_hocolim P hP F P _ _ hTF
  obtain ⟨z, hz⟩ := hbij.2 (𝟙 P)
  obtain ⟨n, a, ha⟩ := Types.jointly_surjective' z
  have hf : a ≫ Sigma.ι Y ⟨n⟩ ≫ e.hom ≫ qA = 𝟙 P := by
    rw [← hz, ← ha, hφ]
    rfl
  refine ⟨n, a.hom, ?_⟩
  have hf' : a ≫ cA.inj ⟨n⟩ ≫ qA = 𝟙 P := by
    simpa only [← Category.assoc, he] using hf
  exact congrArg InducedCategory.Hom.hom hf'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ambient_shift_coproduct_iso
    {C : Type u} [Category.{v} C] [HasShift C ℤ]
    (A : ObjectProperty C) [A.IsStableUnderShift ℤ]
    [HasCoproducts.{w} A.FullSubcategory]
    (G : A.FullSubcategory) {I : Type w} (m : I → ℤ)
    (B : Cofan (fun i : I ↦ G.obj⟦m i⟧)) (hB : IsColimit B) (hAB : A B.pt) :
    Nonempty ((⟨B.pt, hAB⟩ : A.FullSubcategory) ≅ ∐ fun i : I ↦ G⟦m i⟧) := by
  let Y : I → A.FullSubcategory := fun i ↦ G⟦m i⟧
  let e (i : I) : (Y i).obj ≅ G.obj⟦m i⟧ := (A.ι.commShiftIso (m i)).app G
  let c : Cofan Y := Cofan.mk ⟨B.pt, hAB⟩
    (fun i ↦ ObjectProperty.homMk ((e i).hom ≫ B.inj i))
  let dC (d : Cofan Y) : Cofan (fun i : I ↦ G.obj⟦m i⟧) :=
    Cofan.mk d.pt.obj (fun i ↦ (e i).inv ≫ (d.inj i).hom)
  have hc : IsColimit c := by
    refine Cofan.IsColimit.mk _ (fun d ↦ ObjectProperty.homMk (hB.desc (dC d))) ?_ ?_
    · intro d i
      apply ObjectProperty.hom_ext
      change ((e i).hom ≫ B.inj i) ≫ hB.desc (dC d) = (d.inj i).hom
      calc
        _ = (e i).hom ≫ (B.inj i ≫ hB.desc (dC d)) := Category.assoc _ _ _
        _ = (e i).hom ≫ (dC d).inj i :=
          congrArg (fun f ↦ (e i).hom ≫ f) (hB.fac (dC d) ⟨i⟩)
        _ = (d.inj i).hom := Iso.hom_inv_id_assoc (e i) _
    · intro d f hf
      apply ObjectProperty.hom_ext
      apply hB.hom_ext
      intro i
      have hi := congrArg InducedCategory.Hom.hom (hf i.as)
      change ((e i.as).hom ≫ B.inj i.as) ≫ f.hom = (d.inj i.as).hom at hi
      change B.inj i.as ≫ f.hom = B.inj i.as ≫
        hB.desc (dC d)
      apply Eq.trans ?_ (hB.fac (dC d) i).symm
      change B.inj i.as ≫ f.hom = (e i.as).inv ≫ (d.inj i.as).hom
      apply (cancel_epi (e i.as).hom).1
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hi
  exact ⟨hc.coconePointUniqueUpToIso (coproductIsCoproduct Y)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- A compact object presented by a generator telescope lies in its ambient thick envelope.
Source: Stacks Project, Tags 09SP (lemma-factor-through) and 094A
(lemma-commutes-with-countable-direct-sums), applied to the tower of 09SN.
(blueprint: lem-sc-compact-generator-ambient-thick).

Proof: Lift the supplied tower to A.FullSubcategory. Each attaching coproduct belongs to A by
the triangle and the two adjacent tower terms; the final sum belongs to A by closure under
universe-w coproducts after reindexing its countable family. Their ambient colimit universal
properties restrict to the full subcategory. The inclusion respects shifts and distinguished
triangles. Reindex the countable coproduct by ULift ℕ in universe w. By 094A, compact Hom
commutes with the sequential homotopy colimit, so the identity of P factors through a finite
stage. If this stage is zero, the identity of P factors through zero, hence P is zero.
Otherwise use the tail starting at X 1. Its initial term is isomorphic to B 0 because X 0 is
zero. For each later transition, inverse rotation gives the attaching term B n[-1]; shifting
a colimiting cofan by the shift equivalence gives a coproduct of the corresponding shifts
of G. These are the initial-term and transition hypotheses of 09SP. Apply 09SP to the
map from P into the selected stage. It factors through an object in the thick envelope of a
finite sum of copies of G. Finite sums of G lie in its singleton envelope, and the composite
back to P is its identity. Thus P is a retract of an object in that envelope. The inclusion
preserves shifts, finite sums, triangles and retract equations, so this internal construction
lies in the ambient singleton envelope. Retract closure gives the claim. No coproduct larger
than universe w is used and no infinite coproduct is required to be preserved by the inclusion
beyond those explicitly supplied. The zero initial stage or an empty attaching sum gives a zero
factorization; the zero object lies in the envelope of G even when G is zero. -/
theorem compact_generator_ambient_thick
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C]
    (A : ObjectProperty C) [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    [HasCoproducts.{w} A.FullSubcategory]
    [∀ I : Type w, A.IsClosedUnderColimitsOfShape (Discrete I)]
    (G : A.FullSubcategory) (hG : IsCompactObject G)
    (P : A.FullSubcategory) (hP : IsCompactObject P)
    (X : ℕ → A.FullSubcategory) (t : ∀ n : ℕ, (X n).obj ⟶ (X (n + 1)).obj)
    (hzero : IsZero (X 0).obj)
    (hsteps : ∀ n : ℕ, ∃ (I : Type w) (m : I → ℤ)
      (B : Cofan (fun i : I ↦ G.obj⟦m i⟧)), Nonempty (IsColimit B) ∧
      ∃ (a : (X (n + 1)).obj ⟶ B.pt) (b : B.pt ⟶ (X n).obj⟦(1 : ℤ)⟧),
        Pretriangulated.Triangle.mk (t n) a b ∈ distTriang C)
    (S : Cofan (fun n : ℕ ↦ (X n).obj)) (hS : IsColimit S)
    (s : S.pt ⟶ S.pt) (q : S.pt ⟶ P.obj) (r : P.obj ⟶ S.pt⟦(1 : ℤ)⟧)
    (hs : ∀ n : ℕ, S.inj n ≫ s = t n ≫ S.inj (n + 1))
    (hT : Pretriangulated.Triangle.mk (𝟙 S.pt - s) q r ∈ distTriang C) :
    (ObjectProperty.singleton G.obj).triangEnvelope P.obj := by
  classical
  obtain ⟨n, f, hf⟩ := ambient_telescope_factor A P hP X t S hS s q r hs hT
  let tA : ∀ n : ℕ, X n ⟶ X (n + 1) := fun n ↦ ObjectProperty.homMk (t n)
  -- An empty coproduct supplies the initial stage, including the zero-stage case.
  have hinitial : ∃ (J : Type w) (i : J → PUnit.{w + 1}) (m : J → ℤ),
      Nonempty (X 0 ≅ ∐ fun j : J ↦ G⟦m j⟧) := by
    refine ⟨PEmpty.{w + 1}, PEmpty.elim, PEmpty.elim, ?_⟩
    have hz : IsZero (X 0) := .of_full_of_faithful_of_isZero A.ι _ hzero
    have hz' : IsZero (∐ fun j : PEmpty.{w + 1} ↦ G⟦(PEmpty.elim j : ℤ)⟧) := by
      rw [IsZero.iff_id_eq_zero]
      apply Sigma.hom_ext
      intro j
      exact j.elim
    exact ⟨hz.iso hz'⟩
  choose I m B hB a b hdist using hsteps
  have hAB (k : ℕ) : A (B k).pt :=
    A.ext_of_isTriangulatedClosed₃ _ (hdist k) (X k).property (X (k + 1)).property
  let B' (k : ℕ) : A.FullSubcategory := ⟨(B k).pt, hAB k⟩
  let T (k : ℕ) : Pretriangulated.Triangle A.FullSubcategory :=
    Pretriangulated.Triangle.mk (tA k)
      (ObjectProperty.homMk (a k) : X (k + 1) ⟶ B' k)
      (ObjectProperty.homMk (b k ≫ (A.ι.commShiftIso (1 : ℤ)).inv.app (X k)) :
        B' k ⟶ (X k)⟦(1 : ℤ)⟧)
  have hTA (k : ℕ) : T k ∈ distTriang A.FullSubcategory := by
    change A.ι.mapTriangle.obj _ ∈ distTriang C
    change Pretriangulated.Triangle.mk (t k) (a k)
      ((b k ≫ (A.ι.commShiftIso (1 : ℤ)).inv.app (X k)) ≫
        (A.ι.commShiftIso (1 : ℤ)).hom.app (X k)) ∈ distTriang C
    rw [Category.assoc, Iso.inv_hom_id_app]
    change Pretriangulated.Triangle.mk (t k) (a k) (b k ≫ 𝟙 _) ∈ distTriang C
    rw [Category.comp_id]
    exact hdist k
  have hstages : ∃ (Z : ℕ → A.FullSubcategory) (a : ∀ k : ℕ, Z k ⟶ X k)
      (b : ∀ k : ℕ, X (k + 1) ⟶ (Z k)⟦(1 : ℤ)⟧),
      (∀ k : ℕ, ∃ (J : Type w) (i : J → PUnit.{w + 1}) (m : J → ℤ),
        Nonempty (Z k ≅ ∐ fun j : J ↦ G⟦m j⟧)) ∧
      ∀ k : ℕ, Pretriangulated.Triangle.mk (a k) (tA k) (b k) ∈
        distTriang A.FullSubcategory := by
    refine ⟨fun k ↦ (T k).invRotate.obj₁, fun k ↦ (T k).invRotate.mor₁,
      fun k ↦ (T k).invRotate.mor₃, ?_, ?_⟩
    · intro k
      obtain ⟨e⟩ := ambient_shift_coproduct_iso A G (m k) (B k) (hB k).some (hAB k)
      refine ⟨I k, fun _ ↦ PUnit.unit, fun j ↦ m k j + -1, ⟨?_⟩⟩
      exact (shiftFunctor A.FullSubcategory (-1 : ℤ)).mapIso e ≪≫
        (asIso (sigmaComparison (shiftFunctor A.FullSubcategory (-1 : ℤ))
          (fun j : I k ↦ G⟦m k j⟧))).symm ≪≫
        Sigma.mapIso (fun j ↦ ((shiftFunctorAdd A.FullSubcategory (m k j) (-1)).app G).symm)
    · intro k
      exact Pretriangulated.inv_rot_of_distTriang _ (hTA k)
  obtain ⟨J, Q, α, β, hQ, hαβ⟩ := compact_factorThrough_thickClosure
    (fun _ : PUnit.{w + 1} ↦ G) (fun _ ↦ hG) X tA hinitial hstages P hP n
    (ObjectProperty.homMk f)
  -- Pull back the ambient thick envelope and use its internal universal property.
  let R : ObjectProperty A.FullSubcategory :=
    ((ObjectProperty.singleton G.obj).triangEnvelope).inverseImage A.ι
  let : R.IsStableUnderRetracts := ⟨fun r h ↦
    ((ObjectProperty.singleton G.obj).triangEnvelope).prop_of_retract (r.map A.ι) h⟩
  have hG' : R G := (ObjectProperty.singleton G.obj).le_triangEnvelope _
    ((ObjectProperty.singleton_iff _ _).2 rfl)
  have hsum : R (∐ fun i : {i : PUnit.{w + 1} // i ∈ J} ↦ G) := by
    let E := fun _ : {i : PUnit.{w + 1} // i ∈ J} ↦ G
    have : HasFiniteCoproducts A.FullSubcategory := hasFiniteCoproducts_of_hasCoproducts _
    have : HasFiniteBiproducts A.FullSubcategory := HasFiniteBiproducts.of_hasFiniteCoproducts
    apply R.prop_of_iso ((biproduct.isoCoproduct E).symm ≪≫ biproduct.isoProduct E).symm
    exact R.prop_product (fun _ ↦ hG')
  have hQR : R Q := ((ObjectProperty.triangEnvelope_le_iff _).mpr
    (ObjectProperty.singleton_le_iff.mpr hsum)) Q hQ
  apply ((ObjectProperty.singleton G.obj).triangEnvelope).prop_of_retract
    (⟨α.hom, β.hom ≫ S.inj n ≫ q, ?_⟩ : Retract P.obj Q.obj) hQR
  rw [← Category.assoc α.hom β.hom]
  rw [show α.hom ≫ β.hom = f from congrArg InducedCategory.Hom.hom hαβ]
  exact hf

end CategoryTheory
