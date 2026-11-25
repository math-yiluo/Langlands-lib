/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.Subobject.Limits

/-! # Refining finite subobject filtrations

Source: Stacks Project, Tag 01YF, proof, induced filtrations in extensions.
(blueprint: lem-pc-s3-finite-filtration-refinement)
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory

private theorem quotient_iso_of_eq
    {C : Type u} [Category.{v} C] [Abelian C] {F : C}
    {a b a' b' : Subobject F} (hab : a ≤ b) (hab' : a' ≤ b')
    (ha : a = a') (hb : b = b') :
    Nonempty (cokernel (Subobject.ofLE a b hab) ≅
      cokernel (Subobject.ofLE a' b' hab')) := by
  subst a'
  subst b'
  exact ⟨Iso.refl _⟩

private theorem mapped_quotient_iso
    {C : Type u} [Category.{v} C] [Abelian C] {A B : C} (i : A ⟶ B) [Mono i]
    (a b : Subobject A) (hab : a ≤ b) :
    Nonempty (cokernel (Subobject.ofLE ((Subobject.map i).obj a)
      ((Subobject.map i).obj b) ((Subobject.map i).monotone hab)) ≅
      cokernel (Subobject.ofLE a b hab)) := by
  have ha : (Subobject.map i).obj a = Subobject.mk (a.arrow ≫ i) := by
    simpa only [Subobject.mk_arrow] using Subobject.map_mk a.arrow i
  have hb : (Subobject.map i).obj b = Subobject.mk (b.arrow ≫ i) := by
    simpa only [Subobject.mk_arrow] using Subobject.map_mk b.arrow i
  have hab' : Subobject.mk (a.arrow ≫ i) ≤ Subobject.mk (b.arrow ≫ i) :=
    Subobject.mk_le_mk_of_comm (Subobject.ofLE a b hab) (by simp)
  obtain ⟨e⟩ := quotient_iso_of_eq ((Subobject.map i).monotone hab) hab' ha hb
  refine ⟨e ≪≫ ?_⟩
  let e₁ := Subobject.underlyingIso (a.arrow ≫ i)
  let e₂ := Subobject.underlyingIso (b.arrow ≫ i)
  refine cokernel.mapIso _ (Subobject.ofLE a b hab) e₁ e₂ ?_
  apply (cancel_mono (b.arrow ≫ i)).mp
  simp only [e₁, e₂, Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk,
    Subobject.ofLE_arrow]
  rw [Subobject.ofLE_arrow_assoc, Subobject.underlyingIso_hom_comp_eq_mk]

private theorem subobject_filtration_of_closure
    {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] {F : C} (hF : P.filtrationClosure F) :
    ∃ (n : ℕ) (d : Fin (n + 1) → Subobject F) (hd : Monotone d),
      d 0 = ⊥ ∧ d (Fin.last n) = ⊤ ∧
      ∀ k : Fin n, P (cokernel (Subobject.ofLE (d k.castSucc) (d k.succ)
        (hd k.castSucc_le_succ))) := by
  classical
  induction hF with
  | of_isZero hF =>
    have := Subobject.subsingleton_of_isZero hF
    exact ⟨0, fun _ ↦ ⊥, monotone_const, rfl, Subsingleton.elim _ _, fun k ↦ k.elim0⟩
  | @of_mono A B i hi hA hPi ih =>
    obtain ⟨n, c, hc, hbot, htop, hquot⟩ := ih
    let d : Fin (n + 2) → Subobject B := fun j ↦
      if h : j.val < n + 1 then (Subobject.map i).obj (c ⟨j.val, h⟩) else ⊤
    have hdval (j : ℕ) (hj : j < n + 1) :
        d ⟨j, by omega⟩ = (Subobject.map i).obj (c ⟨j, hj⟩) := dite_eq_left hj
    have hdlast : d (Fin.last (n + 1)) = ⊤ := dite_eq_right (by simp)
    have hd : Monotone d := by
      intro a b hab
      dsimp only [d]
      split <;> split
      · exact (Subobject.map i).monotone (hc (by simpa using hab))
      · exact le_top
      · omega
      · exact le_rfl
    refine ⟨n + 1, d, hd, ?_, hdlast, ?_⟩
    · change d ⟨0, _⟩ = ⊥
      rw [hdval 0 (by omega)]
      rw [show (⟨0, by omega⟩ : Fin (n + 1)) = 0 from Fin.ext rfl, hbot]
      exact Subobject.map_bot i
    · intro j
      by_cases hj : j.val < n
      · have h₁ := hdval j.val (by omega)
        have h₂ := hdval (j.val + 1) (by omega)
        let k : Fin n := ⟨j.val, hj⟩
        obtain ⟨e⟩ := quotient_iso_of_eq (hd j.castSucc_le_succ)
          ((Subobject.map i).monotone (hc k.castSucc_le_succ)) h₁ h₂
        apply P.prop_of_iso e.symm
        exact P.prop_of_iso (mapped_quotient_iso i (c (⟨j.val, hj⟩ : Fin n).castSucc)
          (c (⟨j.val, hj⟩ : Fin n).succ) (hc (Fin.castSucc_le_succ _))).some.symm
          (hquot ⟨j.val, hj⟩)
      · have hjn : j.val = n := by omega
        have h₁ : d j.castSucc = Subobject.mk i := by
          change d ⟨j.val, _⟩ = Subobject.mk i
          rw [hdval j.val (by omega)]
          have he : (⟨j.val, by omega⟩ : Fin (n + 1)) = Fin.last n := by
            ext; simp [hjn]
          rw [he, htop, Subobject.map_top]
        have h₂ : d j.succ = ⊤ := by
          have he : j.succ = Fin.last (n + 1) := by ext; simp [hjn]
          rw [he, hdlast]
        obtain ⟨e⟩ := quotient_iso_of_eq (hd j.castSucc_le_succ) le_top h₁ h₂
        apply P.prop_of_iso e.symm
        apply P.prop_of_iso _ hPi
        exact (cokernel.mapIso _ i (Subobject.underlyingIso i)
          (Subobject.underlyingIso (𝟙 B)) (by
            rw [Subobject.underlyingIso_top_hom, Subobject.ofLE_arrow]
            exact (Subobject.underlyingIso_hom_comp_eq_mk i).symm)).symm

private theorem closure_of_subobject_filtration
    {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms]
    (F : C) (m : ℕ) (c : Fin (m + 1) → Subobject F) (hc : Monotone c)
    (hbot : c 0 = ⊥) (htop : c (Fin.last m) = ⊤)
    (hquot : ∀ j : Fin m,
      P.filtrationClosure (cokernel (Subobject.ofLE (c j.castSucc) (c j.succ)
        (hc j.castSucc_le_succ)))) : P.filtrationClosure F := by
  have hstep : ∀ (j : ℕ) (hj : j < m + 1), P.filtrationClosure (c ⟨j, hj⟩ : C) := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [show (⟨0, hj⟩ : Fin (m + 1)) = 0 from rfl, hbot]
      exact .of_isZero ((Limits.isZero_zero C).of_iso Subobject.botCoeIsoZero)
    | succ j ih =>
      intro hj
      let f := Subobject.ofLE (c (⟨j, by omega⟩ : Fin m).castSucc)
        (c (⟨j, by omega⟩ : Fin m).succ) (hc (Fin.castSucc_le_succ _))
      have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
        ⟨ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)⟩
      exact P.filtrationClosure.prop_X₂_of_shortExact hS (ih (by omega))
        (hquot ⟨j, by omega⟩)
  have ht := hstep m (by omega)
  rw [show (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m from rfl, htop] at ht
  exact P.filtrationClosure.prop_of_iso (Subobject.underlyingIso (𝟙 F)) ht

/-- A finite filtration can be refined by finite filtrations of its successive quotients.
A quotient already satisfying the isomorphism-invariant property needs no refinement.

Source: Stacks Project, Tag 01YF (`coherent.tex`, `lemma-coherent-filter`), proof,
induced filtrations in extensions and refinement of the J-adic filtration.
(blueprint: lem-pc-s3-finite-filtration-refinement)

Proof: Use the proved source-library property P.filtrationClosure, which contains P
and zero objects and is closed under isomorphisms and extensions. First convert any
subobject chain with quotients in P.filtrationClosure into membership in this closure:
induct on the chain index, starting at the zero bottom object, and apply extension
closure to each canonical short exact cokernel sequence. Transport the last top object
to the ambient object by the underlyingIso of its identity morphism. A quotient satisfying
P belongs to the closure; one with its own P-filtration belongs to the closure by the
same index induction. Thus every quotient of the outer chain belongs to the closure,
and hence so does F.
Finally convert closure membership into the required subobject chain, by induction on
the constructors of filtrationClosure. For a zero object, subobjects are subsingleton
and the constant bottom chain of length zero works. For a monomorphism A to B with
cokernel in P, map the existing chain of A along this monomorphism and append the top
subobject of B. Map preserves bottom and order. Its consecutive cokernels are isomorphic
to those of the original chain: use the underlyingIso of the composite inclusions and
cokernel.mapIso on their commuting square. The last quotient is isomorphic to the
cokernel of A to B, again by cokernel.mapIso with the top underlyingIso. The mapped
chain ends at the subobject represented by A to B, so it is monotone through the appended
top. Transport P through these isomorphisms. Repeated subobjects and zero-length inner
chains cause no exception; no assumption that P contains zero is needed. -/
theorem finite_filtration_refinement
    {C : Type u} [Category.{v} C] [Abelian C] (P : C → Prop)
    (hP : ∀ (A B : C), Nonempty (A ≅ B) → P A → P B)
    (F : C) (m : ℕ) (c : Fin (m + 1) → Subobject F) (hc : Monotone c)
    (hbot : c 0 = ⊥) (htop : c (Fin.last m) = ⊤)
    (hquot : ∀ j : Fin m,
      P (cokernel (Subobject.ofLE (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ))) ∨
      ∃ (n : ℕ)
        (d : Fin (n + 1) → Subobject
          (cokernel (Subobject.ofLE (c j.castSucc) (c j.succ)
            (hc j.castSucc_le_succ)))) (hd : Monotone d),
        d 0 = ⊥ ∧ d (Fin.last n) = ⊤ ∧
        ∀ k : Fin n, P (cokernel (Subobject.ofLE (d k.castSucc) (d k.succ)
          (hd k.castSucc_le_succ)))) :
    ∃ (n : ℕ) (d : Fin (n + 1) → Subobject F) (hd : Monotone d),
      d 0 = ⊥ ∧ d (Fin.last n) = ⊤ ∧
      ∀ k : Fin n, P (cokernel (Subobject.ofLE (d k.castSucc) (d k.succ)
        (hd k.castSucc_le_succ))) := by
  let P' : ObjectProperty C := P
  have : P'.IsClosedUnderIsomorphisms := ⟨fun e h ↦ hP _ _ ⟨e⟩ h⟩
  apply subobject_filtration_of_closure P'
  apply closure_of_subobject_filtration P' F m c hc hbot htop
  intro j
  rcases hquot j with hj | ⟨n, d, hd, hbot', htop', hquot'⟩
  · exact ObjectProperty.le_filtrationClosure (P := P') _ hj
  · apply closure_of_subobject_filtration P' _ n d hd hbot' htop'
    intro k
    exact ObjectProperty.le_filtrationClosure (P := P') _ (hquot' k)

end CategoryTheory
