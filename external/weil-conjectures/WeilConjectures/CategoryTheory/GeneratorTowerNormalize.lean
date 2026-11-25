/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Rotating, mapping and prepending zero to a generator tower

Source: Stacks Project, derived.tex, lemma-write-as-colimit (Tag 09SN), and
duality.tex, lemma-when-sheafy, proof of (3), Section Tag 0E4G.
(blueprint: lem-sc-generator-tower-normalize).
-/

@[expose] public section

universe u v c d

open CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace CategoryTheory

private noncomputable def cofan_change_sources
    {D : Type d} [Category.{v} D] {J : Type u} {g h : J → D}
    (B : Cofan g) (hB : IsColimit B) (k : ∀ j, h j ≅ g j) :
    IsColimit (Cofan.mk B.pt (fun j ↦ (k j).hom ≫ B.inj j)) := by
  refine Cofan.IsColimit.mk _
    (fun T ↦ hB.desc (Cofan.mk T.pt (fun j ↦ (k j).inv ≫ T.inj j))) ?_ ?_
  · intro T j
    change ((k j).hom ≫ B.inj j) ≫ hB.desc (Cofan.mk T.pt (fun j ↦ (k j).inv ≫ T.inj j)) = T.inj j
    rw [Category.assoc, Cofan.IsColimit.inj_desc]
    simp
  · intro T f hf
    apply hB.hom_ext
    rintro ⟨j⟩
    rw [hB.fac]
    simpa only [Cofan.mk_ι_app, Cofan.inj, Category.assoc, Iso.inv_hom_id_assoc]
      using congrArg (fun a ↦ (k j).inv ≫ a) (hf j)

private noncomputable def mapped_sum_cofan
    {C : Type c} {D : Type d} [Category.{u} C] [Category.{v} D]
    {J : Type u} (G : C ⥤ D) [PreservesColimitsOfShape (Discrete J) G]
    (g : J → C) [HasCoproduct g] {A : C} (hA : A ≅ ∐ g)
    (h : J → D) (k : ∀ j, h j ≅ G.obj (g j)) :
    IsColimit (Cofan.mk (G.obj A)
      (fun j ↦ (k j).hom ≫ G.map (Sigma.ι g j ≫ hA.inv))) := by
  let B : Cofan g := Cofan.mk A (fun j ↦ Sigma.ι g j ≫ hA.inv)
  have hB : IsColimit B :=
    IsColimit.ofIsoColimit (coproductIsCoproduct g)
      (Cofan.ext hA.symm (fun j ↦ by simp [B]))
  have hmap : IsColimit (Cofan.mk (G.obj A) (fun j ↦ G.map (B.inj j))) :=
    (Cofan.isColimitMapCoconeEquiv G g B) (isColimitOfPreserves G hB)
  exact cofan_change_sources _ hmap k

/-- Normalize an already constructed telescope under an exact coproduct-preserving
functor. This assertion uses no compactness or generation assumption.
Source: Stacks Project, derived.tex, lemma-write-as-colimit (Tag 09SN), and
duality.tex, lemma-when-sheafy, proof of (3), Section Tag 0E4G.
(blueprint: lem-sc-generator-tower-normalize).

Proof: Rotate Z_n -> A_n -> A_(n+1) -> Z_n[1] once. Shifts preserve coproducts,
so Z_n[1] is a coproduct of the shifts e[m+1]. Prepend the zero object: set
X_0 = 0 and X_(n+1) = A_n, with zero first transition and the given subsequent
transitions. The first distinguished triangle is the inverse rotation of the
contractible triangle on A_0; its third object is A_0, a sum of shifts by hstart.
The canonical coproduct isomorphism deleting the zero summand sends each successor
coprojection to the corresponding old coprojection. Check on coprojections that
it conjugates the new transition endomorphism to the old one. The zero component
is zero on both sides. Additivity also conjugates identity minus these maps.
Transport the given telescope triangle along this isomorphism. Map all triangles
by F. Its shift comparison identifies mapped shifts, and preservation of coproducts
maps each colimiting cofan to an ambient colimiting cofan. Replace F(e) by E and
F(q) by Q using the given isomorphisms, transporting triangles along triangle
isomorphisms. Reindex the ULift-indexed countable cofan along n -> ULift.up n.
This yields the stated sequence and cofan equations. Empty summand sets and zero
objects require no special choices and satisfy the same universal properties. -/
theorem generator_tower_normalize
    {C : Type c} {D : Type d} [Category.{u} C] [Category.{v} D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] [IsTriangulated C] [IsTriangulated D]
    [HasCoproducts.{u} C]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Additive]
    (hF : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) F)
    (e q : C) (E Q : D) (he : F.obj e ≅ E) (hq : F.obj q ≅ Q)
    (A : ℕ → C) (t : ∀ n : ℕ, A n ⟶ A (n + 1))
    (hstart : ∃ (J : Type u) (m : J → ℤ),
      Nonempty (A 0 ≅ ∐ fun j : J ↦ e⟦m j⟧))
    (hsteps : ∃ (Z : ℕ → C) (a : ∀ n : ℕ, Z n ⟶ A n)
      (b : ∀ n : ℕ, A (n + 1) ⟶ (Z n)⟦(1 : ℤ)⟧),
      (∀ n : ℕ, ∃ (J : Type u) (m : J → ℤ),
        Nonempty (Z n ≅ ∐ fun j : J ↦ e⟦m j⟧)) ∧
      ∀ n : ℕ, Triangle.mk (a n) (t n) (b n) ∈ distTriang C)
    (qA : (∐ fun n : ULift.{u} ℕ ↦ A n.down) ⟶ q)
    (rA : q ⟶ (∐ fun n : ULift.{u} ℕ ↦ A n.down)⟦(1 : ℤ)⟧)
    (htelescope : Triangle.mk
      (𝟙 (∐ fun n : ULift.{u} ℕ ↦ A n.down) -
        Sigma.desc (fun n : ULift.{u} ℕ ↦
          t n.down ≫ Sigma.ι (fun k : ULift.{u} ℕ ↦ A k.down) ⟨n.down + 1⟩))
      qA rA ∈ distTriang C) :
    ∃ (X : ℕ → C) (tX : ∀ n : ℕ, F.obj (X n) ⟶ F.obj (X (n + 1))),
      IsZero (F.obj (X 0)) ∧
      (∀ n : ℕ, ∃ (I : Type u) (m : I → ℤ)
        (B : Cofan (fun i : I ↦ E⟦m i⟧)), Nonempty (IsColimit B) ∧
        ∃ (a : F.obj (X (n + 1)) ⟶ B.pt)
          (b : B.pt ⟶ (F.obj (X n))⟦(1 : ℤ)⟧),
          Triangle.mk (tX n) a b ∈ distTriang D) ∧
      ∃ (S : Cofan (fun n : ℕ ↦ F.obj (X n))), Nonempty (IsColimit S) ∧
        ∃ (s : S.pt ⟶ S.pt) (qS : S.pt ⟶ Q) (rS : Q ⟶ S.pt⟦(1 : ℤ)⟧),
          (∀ n : ℕ, S.inj n ≫ s = tX n ≫ S.inj (n + 1)) ∧
          Triangle.mk (𝟙 S.pt - s) qS rS ∈ distTriang D := by
  classical
  let X : ℕ → C := fun n ↦ match n with
    | 0 => (0 : C)
    | n + 1 => A n
  let tC : ∀ n : ℕ, X n ⟶ X (n + 1) := fun n ↦ match n with
    | 0 => 0
    | n + 1 => t n
  refine ⟨X, fun n ↦ F.map (tC n), ?_, ?_, ?_⟩
  · exact F.map_isZero (isZero_zero C)
  · intro n
    cases n with
    | zero =>
      obtain ⟨J, m, ⟨hA⟩⟩ := hstart
      let := hF J
      let k : ∀ j : J, E⟦m j⟧ ≅ F.obj (e⟦m j⟧) := fun j ↦
        (shiftFunctor D (m j)).mapIso he.symm ≪≫ (F.commShiftIso (m j)).symm.app e
      refine ⟨J, m, Cofan.mk (F.obj (A 0))
        (fun j ↦ (k j).hom ≫ F.map (Sigma.ι (fun j ↦ e⟦m j⟧) j ≫ hA.inv)),
        ⟨mapped_sum_cofan F _ hA _ k⟩, 𝟙 _, 0, ?_⟩
      have hd := F.map_distinguished _ (contractible_distinguished₁ (A 0))
      dsimp only [Functor.mapTriangle, Triangle.mk] at hd
      dsimp only [X, tC, Triangle.mk]
      simpa only [Functor.map_zero, Functor.map_id, Cofan.mk_pt, Limits.zero_comp] using hd
    | succ n =>
      obtain ⟨Z, a, b, hZ, hdist⟩ := hsteps
      obtain ⟨J, m, ⟨hZiso⟩⟩ := hZ n
      let := hF J
      let G := shiftFunctor C (1 : ℤ) ⋙ F
      let k : ∀ j : J, E⟦m j + 1⟧ ≅ G.obj (e⟦m j⟧) := fun j ↦
        (shiftFunctor D (m j + 1)).mapIso he.symm ≪≫
          (F.commShiftIso (m j + 1)).symm.app e ≪≫
          F.mapIso ((shiftFunctorAdd C (m j) (1 : ℤ)).app e)
      refine ⟨J, fun j ↦ m j + 1, Cofan.mk (G.obj (Z n))
        (fun j ↦ (k j).hom ≫ G.map
          (Sigma.ι (fun j ↦ e⟦m j⟧) j ≫ hZiso.inv)),
        ⟨mapped_sum_cofan G _ hZiso _ k⟩,
        F.map (b n),
        F.map (-(a n)⟦(1 : ℤ)⟧') ≫ (F.commShiftIso (1 : ℤ)).hom.app (A n), ?_⟩
      exact F.map_distinguished _ (rot_of_distTriang _ (hdist n))
  · let B := fun n : ULift.{u} ℕ ↦ A n.down
    let j : ∀ n : ℕ, X n ⟶ ∐ B := fun n ↦ match n with
      | 0 => 0
      | n + 1 => Sigma.ι B ⟨n⟩
    let S : Cofan X := Cofan.mk (∐ B) j
    have hS : IsColimit S := by
      refine Cofan.IsColimit.mk S
        (fun T ↦ Sigma.desc (fun n : ULift.{u} ℕ ↦ T.inj (n.down + 1))) ?_ ?_
      · intro T n
        cases n with
        | zero =>
          exact (isZero_zero C).eq_of_src _ _
        | succ n =>
          change Sigma.ι B ⟨n⟩ ≫ Sigma.desc _ = _
          exact Sigma.ι_comp_desc _ _
      · intro T f hf
        apply Sigma.hom_ext (f := B)
        intro n
        rw [Sigma.ι_comp_desc]
        simpa [S, j, B] using hf (n.down + 1)
    let s : (∐ B) ⟶ ∐ B := Sigma.desc (fun n : ULift.{u} ℕ ↦
      t n.down ≫ Sigma.ι B ⟨n.down + 1⟩)
    have hs (n : ℕ) : S.inj n ≫ s = tC n ≫ S.inj (n + 1) := by
      cases n with
      | zero => simp [S, j, tC]
      | succ n => simp [S, j, tC, s, B]
    have hSmap : IsColimit (Cofan.mk (F.obj (∐ B)) (fun n ↦ F.map (S.inj n))) := by
      let := hF (ULift.{u} ℕ)
      have hS' : IsColimit (Cofan.mk (∐ B) (fun n : ULift.{u} ℕ ↦ S.inj n.down)) :=
        (Cofan.isColimitEquivOfEquiv (Equiv.ulift : ULift.{u} ℕ ≃ ℕ) S) hS
      have hmap := (Cofan.isColimitMapCoconeEquiv F _ _)
        (isColimitOfPreserves F hS')
      exact (Cofan.isColimitEquivOfEquiv (Equiv.ulift.symm : ℕ ≃ ULift.{u} ℕ) _) hmap
    refine ⟨Cofan.mk (F.obj (∐ B)) (fun n ↦ F.map (S.inj n)), ⟨hSmap⟩,
      F.map s, F.map qA ≫ hq.hom,
      hq.inv ≫ F.map rA ≫ (F.commShiftIso (1 : ℤ)).hom.app (∐ B), ?_, ?_⟩
    · intro n
      simpa only [Cofan.inj, Cofan.mk_ι_app, ← F.map_comp] using congrArg F.map (hs n)
    · have hmap := F.map_distinguished _ htelescope
      refine isomorphic_distinguished _ hmap _ ?_
      refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) hq.symm ?_ ?_ ?_
      · dsimp [Functor.mapTriangle, Triangle.mk, B, s]
        simp
      · dsimp [Functor.mapTriangle, Triangle.mk, B]
        simp
      · dsimp [Functor.mapTriangle, Triangle.mk, B]
        simp


end CategoryTheory
