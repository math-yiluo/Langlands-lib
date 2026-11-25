/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Finite cohomology cone witnesses
Source: Stacks Project, Derived Categories, Tags 08J5 and 0118; the Complexes paragraph
of blueprint sk-cor-coefficient-heart-ii-generation.
(blueprint: lem-sfb-bounded-cohomology-cone-witness)
-/

@[expose] public section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace DerivedCategory

open CategoryTheory.Pretriangulated

private def constructionValid {C : Type*} (G : C → Prop) (R : C → C → C → Prop)
    {n : ℕ} (F : Fin n → C) : Prop :=
  ∀ r, G (F r) ∨ ∃ i j, i < r ∧ j < r ∧ R (F i) (F j) (F r)

private def constructionWitness {C : Type*} (G : C → Prop) (R : C → C → C → Prop)
    (K : C) : Prop :=
  ∃ (N : ℕ) (F : Fin (N + 1) → C), F (Fin.last N) = K ∧ constructionValid G R F

private theorem constructionValid_append {C : Type*} {G : C → Prop}
    {R : C → C → C → Prop} {m n : ℕ} {F : Fin m → C} {H : Fin n → C}
    (hF : constructionValid G R F) (hH : constructionValid G R H) :
    constructionValid G R (Fin.append F H) := by
  intro r
  refine Fin.addCases (fun r ↦ ?_) (fun r ↦ ?_) r
  · rcases hF r with h | ⟨i, j, hi, hj, h⟩
    · exact Or.inl (by simpa using h)
    · right
      refine ⟨i.castAdd n, j.castAdd n, ?_, ?_, ?_⟩
      · exact hi
      · exact hj
      · simpa using h
  · rcases hH r with h | ⟨i, j, hi, hj, h⟩
    · exact Or.inl (by simpa using h)
    · right
      refine ⟨i.natAdd m, j.natAdd m, ?_, ?_, ?_⟩
      · simpa using hi
      · simpa using hj
      · simpa using h

private theorem constructionWitness_generator {C : Type*} {G : C → Prop}
    {R : C → C → C → Prop} {K : C} (hK : G K) : constructionWitness G R K := by
  exact ⟨0, fun _ ↦ K, rfl, fun _ ↦ Or.inl hK⟩

private theorem constructionWitness_step {C : Type*} {G : C → Prop}
    {R : C → C → C → Prop} {A B K : C}
    (hA : constructionWitness G R A) (hB : constructionWitness G R B)
    (hK : R A B K) : constructionWitness G R K := by
  obtain ⟨m, F, hF, hvF⟩ := hA
  obtain ⟨n, H, hH, hvH⟩ := hB
  refine ⟨(m + 1) + (n + 1), Fin.snoc (Fin.append F H) K, by simp, ?_⟩
  intro r
  refine Fin.lastCases ?_ (fun r ↦ ?_) r
  · right
    refine ⟨((Fin.last m).castAdd (n + 1)).castSucc,
      ((Fin.last n).natAdd (m + 1)).castSucc, ?_, ?_, ?_⟩
    · exact Fin.castSucc_lt_last _
    · exact Fin.castSucc_lt_last _
    · simpa only [Fin.snoc_last, Fin.snoc_castSucc, Fin.append_left,
        Fin.append_right, hF, hH] using hK
  · rcases constructionValid_append hvF hvH r with h | ⟨i, j, hi, hj, h⟩
    · exact Or.inl (by simpa using h)
    · exact Or.inr ⟨i.castSucc, j.castSucc, hi, hj, by simpa using h⟩

/-- A bounded derived object has a finite cone witness with leaves shifts of its own
cohomology objects, placed in degree zero. This is independent of any constructibility
condition or coefficient field.

Source: Stacks Project, Derived Categories, Tags 08J5 and 0118; blueprint generation,
Complexes paragraph (blueprint: lem-sfb-bounded-cohomology-cone-witness).

Proof: choose bounds a,b for the canonical t-structure and a complex representing K.
The upper truncations at a-1 and b are respectively zero and isomorphic to K. For each
integer q from a through b, the successive truncation triangle has third vertex
H^q(K)[-q]. Inverse rotation expresses the next truncation as the cone of a morphism
from H^q(K)[-q-1] to the previous truncation. Begin with zero, which is isomorphic to
H^(a-1)(K)[0], concatenate the finitely many leaves and append those cones. Transport
the final triangle by the isomorphism from the last truncation to K, so the final entry
is literally K. The same zero-base construction handles acyclic objects and crossed
bounds. No retract or infinite construction is used. -/
theorem bounded_cohomology_cone_witness (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (K : DerivedCategory A)
    (hK : TStructure.t.bounded K) :
    ∃ (N : ℕ) (F : Fin (N + 1) → DerivedCategory A),
      F (Fin.last N) = K ∧ ∀ r : Fin (N + 1),
        (∃ q n : ℤ, Nonempty (F r ≅
          ((singleFunctor A 0).obj ((homologyFunctor A q).obj K))⟦n⟧)) ∨
        (∃ (i j : Fin (N + 1)), i < r ∧ j < r ∧
          ∃ (n : ℤ) (f : F i ⟶ F j) (g : F j ⟶ (F r)⟦n⟧)
            (h : (F r)⟦n⟧ ⟶ (F i)⟦(1 : ℤ)⟧),
            Pretriangulated.Triangle.mk f g h ∈ distTriang _) := by
  let G : DerivedCategory A → Prop := fun W ↦ ∃ q n : ℤ,
    Nonempty (W ≅ ((singleFunctor A 0).obj ((homologyFunctor A q).obj K))⟦n⟧)
  let R : DerivedCategory A → DerivedCategory A → DerivedCategory A → Prop :=
    fun U V W ↦ ∃ (n : ℤ) (f : U ⟶ V) (g : V ⟶ W⟦n⟧)
      (h : W⟦n⟧ ⟶ U⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang _
  change constructionWitness G R K
  have step (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _)
      (h₁ : constructionWitness G R T.obj₁) (h₂ : constructionWitness G R T.obj₂) :
      constructionWitness G R T.obj₃ := by
    apply constructionWitness_step h₁ h₂
    let e := (shiftFunctorZero (DerivedCategory A) ℤ).app T.obj₃
    refine ⟨0, T.mor₁, T.mor₂ ≫ e.inv, e.hom ≫ T.mor₃, ?_⟩
    apply isomorphic_distinguished _ hT
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e
      (by simp) (by simp) (by simp)
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK
  have : K.IsGE a := ha
  have : K.IsLE b := hb
  have hzH : IsZero ((homologyFunctor A (a - 1)).obj K) :=
    isZero_of_isGE K a (a - 1) (by omega)
  have zero_witness (Z : DerivedCategory A) (hz : IsZero Z) :
      constructionWitness G R Z := by
    apply constructionWitness_generator
    refine ⟨a - 1, 0, ⟨?_⟩⟩
    exact hz.iso ((shiftFunctor _ (0 : ℤ)).map_isZero
      ((singleFunctor A 0).map_isZero hzH))
  have iso_witness {U V : DerivedCategory A} (e : U ≅ V)
      (hU : constructionWitness G R U) : constructionWitness G R V := by
    let T := Triangle.mk (0 : 0 ⟶ U) e.hom 0
    have hT : T ∈ distTriang _ := by
      apply isomorphic_distinguished _ (contractible_distinguished₁ U)
      exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
        (by simp [T]) (by change e.hom ≫ e.inv = 𝟙 U ≫ 𝟙 U; simp) (by simp [T])
    exact step T hT (zero_witness _ (isZero_zero _)) hU
  let C := Q.objPreimage K
  let eK : Q.obj C ≅ K := Q.objObjPreimageIso K
  have : C.IsGE a := (isGE_Q_obj_iff C a).1 (TStructure.t.isGE_of_iso eK.symm a)
  have : C.IsLE b := (isLE_Q_obj_iff C b).1 (TStructure.t.isLE_of_iso eK.symm b)
  have eH (q : ℤ) : C.homology q ≅ (homologyFunctor A q).obj K :=
    ((homologyFunctorFactors A q).app C).symm ≪≫ (homologyFunctor A q).mapIso eK
  have leaf (q : ℤ) : constructionWitness G R
      ((Q.obj ((CochainComplex.singleFunctor A q).obj (C.homology q)))⟦(-1 : ℤ)⟧) := by
    apply constructionWitness_generator
    refine ⟨q, -q + -1, ⟨?_⟩⟩
    exact (shiftFunctor _ (-1 : ℤ)).mapIso
        ((singleFunctor A q).mapIso (eH q) ≪≫
          ((singleFunctors A).shiftIso (-q) q 0 (by omega)).symm.app _) ≪≫
      (shiftFunctorAdd _ (-q) (-1 : ℤ)).symm.app _
  have hbase : IsZero (Q.obj (C.truncLE (a - 1))) := by
    apply isZero_of_forall_isZero_homology
    intro q
    apply IsZero.of_iso _ ((homologyFunctorFactors A q).app _)
    change IsZero ((C.truncLE (a - 1)).homology q)
    by_cases hq : q ≤ a - 1
    · have := C.quasiIsoAt_ιTruncLE (a - 1) q hq
      exact (C.isZero_of_isGE a q (by omega)).of_iso
        (asIso (HomologicalComplex.homologyMap (C.ιTruncLE (a - 1)) q))
    · exact (C.truncLE (a - 1)).isZero_of_isLE (a - 1) q (by omega)
  have tower (n : ℕ) : constructionWitness G R (Q.obj (C.truncLE (a - 1 + n))) := by
    induction n with
    | zero => simpa using zero_witness _ hbase
    | succ n ih =>
      let q : ℤ := a - 1 + (n + 1 : ℕ)
      obtain ⟨i, j, _, _, k, hk, _⟩ := (truncation_triangle A q).1 C
      let T := Triangle.mk (Q.map i) (Q.map j) k
      have hT : T ∈ distTriang _ := hk
      apply step T.invRotate (inv_rot_of_distTriang T hT) (leaf q)
      have hq : q - 1 = a - 1 + (n : ℤ) := by dsimp [q]; omega
      change constructionWitness G R (Q.obj (C.truncLE (q - 1)))
      rw [hq]
      exact ih
  let n : ℕ := (b - (a - 1)).toNat
  have hbn : b ≤ a - 1 + n := by dsimp [n]; omega
  have : C.IsLE (a - 1 + n) := C.isLE_of_le b _ hbn
  let e : Q.obj (C.truncLE (a - 1 + n)) ≅ K :=
    asIso (Q.map (C.ιTruncLE (a - 1 + n))) ≪≫ eK
  exact iso_witness e (tower n)

end DerivedCategory
