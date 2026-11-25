/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.CategoryTheory.Filtered.Final

@[expose] public section

universe uI vI uJ vJ uC vC

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

/-! # Essential constancy under initial restriction

Source: Stacks Project, Categories, Lemma Tag 0A1T (lemma-initial-essentially-constant),
the pro form of Lemma Tag 0A1S (blueprint: lem-pur-essential-constant-cofinal-0a1s).
-/

private theorem restrict_witness
    {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsCofiltered I] [IsCofiltered J]
    (H : I ⥤ J) [H.Initial] (M : J ⥤ C) (X : C)
    (u : (Functor.const J).obj X ⟶ M)
    (hu : ∃ j₀ : J, ∃ r : M.obj j₀ ⟶ X, u.app j₀ ≫ r = 𝟙 X ∧
      ∀ j : J, ∃ k : J, ∃ a : k ⟶ j₀, ∃ b : k ⟶ j,
        M.map b = M.map a ≫ r ≫ u.app j) :
    ∃ i₀ : I, ∃ r : M.obj (H.obj i₀) ⟶ X, u.app (H.obj i₀) ≫ r = 𝟙 X ∧
      ∀ i : I, ∃ k : I, ∃ a : k ⟶ i₀, ∃ b : k ⟶ i,
        M.map (H.map b) = M.map (H.map a) ≫ r ≫ u.app (H.obj i) := by
  obtain ⟨j₀, r, hr, hstage⟩ := hu
  obtain ⟨i₀, ⟨p⟩⟩ := (H.initial_iff_of_isCofiltered.mp inferInstance).1 j₀
  refine ⟨i₀, M.map p ≫ r, ?_, ?_⟩
  · have hn := u.naturality p
    change 𝟙 X ≫ u.app j₀ = u.app (H.obj i₀) ≫ M.map p at hn
    rw [Category.id_comp] at hn
    rw [← Category.assoc, ← hn, hr]
  · intro i
    obtain ⟨j, a, b, hab⟩ := hstage (H.obj i)
    obtain ⟨l, ⟨q⟩⟩ := (H.initial_iff_of_isCofiltered.mp inferInstance).1 j
    obtain ⟨t, t₀, tl, _⟩ := IsCofilteredOrEmpty.cone_objs i₀ l
    obtain ⟨s, st, si, _⟩ := IsCofilteredOrEmpty.cone_objs t i
    obtain ⟨s₁, e₁, he₁⟩ := Functor.Initial.exists_eq H
      (H.map (st ≫ t₀) ≫ p) (H.map (st ≫ tl) ≫ q ≫ a)
    obtain ⟨s₂, e₂, he₂⟩ := Functor.Initial.exists_eq H
      (H.map (e₁ ≫ si)) (H.map (e₁ ≫ st ≫ tl) ≫ q ≫ b)
    refine ⟨s₂, e₂ ≫ e₁ ≫ st ≫ t₀, e₂ ≫ e₁ ≫ si, ?_⟩
    have ha : H.map (e₂ ≫ e₁ ≫ st ≫ t₀) ≫ p =
        H.map (e₂ ≫ e₁ ≫ st ≫ tl) ≫ q ≫ a := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun f => H.map e₂ ≫ f) he₁
    have hb : H.map (e₂ ≫ e₁ ≫ si) =
        H.map (e₂ ≫ e₁ ≫ st ≫ tl) ≫ q ≫ b := by
      simpa only [Functor.map_comp, Category.assoc] using he₂
    rw [hb, M.map_comp, M.map_comp, hab]
    simp only [Category.assoc]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun f => f ≫ r ≫ u.app (H.obj i)) (congrArg M.map ha).symm

private theorem extend_witness
    {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsCofiltered I] [IsCofiltered J]
    (H : I ⥤ J) [H.Initial] (M : J ⥤ C) (X : C)
    (v : (Functor.const I).obj X ⟶ H ⋙ M)
    (hv : ∃ i₀ : I, ∃ r : M.obj (H.obj i₀) ⟶ X, v.app i₀ ≫ r = 𝟙 X ∧
      ∀ i : I, ∃ k : I, ∃ a : k ⟶ i₀, ∃ b : k ⟶ i,
        M.map (H.map b) = M.map (H.map a) ≫ r ≫ v.app i) :
    ∃ u : (Functor.const J).obj X ⟶ M,
      (∃ j₀ : J, ∃ r : M.obj j₀ ⟶ X, u.app j₀ ≫ r = 𝟙 X ∧
        ∀ j : J, ∃ k : J, ∃ a : k ⟶ j₀, ∃ b : k ⟶ j,
          M.map b = M.map a ≫ r ≫ u.app j) ∧
      ∀ i : I, u.app (H.obj i) = v.app i := by
  let c : Cone (H ⋙ M) := ⟨X, v⟩
  let u := (Functor.Initial.extendCone (F := H) (G := M)).obj c
  have happ (i : I) : u.π.app (H.obj i) = v.app i := by
    have h := Functor.Initial.extendCone_obj_π_app' (F := H) (G := M)
      c (𝟙 (H.obj i))
    change u.π.app (H.obj i) = v.app i ≫ M.map (𝟙 (H.obj i)) at h
    rw [M.map_id] at h
    exact h.trans (Category.comp_id _)
  refine ⟨u.π, ?_, happ⟩
  obtain ⟨i₀, r, hr, hstage⟩ := hv
  refine ⟨H.obj i₀, r, ?_, ?_⟩
  · simpa only [happ] using hr
  · intro j
    obtain ⟨i, ⟨p⟩⟩ := (H.initial_iff_of_isCofiltered.mp inferInstance).1 j
    obtain ⟨k, a, b, hab⟩ := hstage i
    refine ⟨H.obj k, H.map a, H.map b ≫ p, ?_⟩
    rw [M.map_comp, hab, Category.assoc, Category.assoc]
    rw [← Functor.Initial.extendCone_obj_π_app' c p]

/-- Let `H : I ⥤ J` be an initial functor (Mathlib's `Functor.Initial`: every comma category
`CostructuredArrow H j` is nonempty and connected, Stacks' initial) between cofiltered
categories and `M : J ⥤ C`. Then `M` is essentially constant with value `X` as a pro-object
iff `H ⋙ M` is, with the same value. More precisely, if `u : X ⟶ M` is a cone exhibiting `M`
as essentially constant (an index `j₀`, a retraction `r` of `u.app j₀`, and the common-stage
clause of `IsEssentiallyConstantProDiagram`), then the restricted cone `H.whiskerLeft u`,
with components `u.app (H.obj i)`, exhibits `H ⋙ M` as essentially constant; and if `v`
exhibits `H ⋙ M` as essentially constant, there is a cone `u` exhibiting `M` as essentially
constant with `H.whiskerLeft u = v`, i.e. `u.app (H.obj i) = v.app i` for all `i`.

Proof (in words). We use Definition 05PU(2) directly, rather than Hom-colimits.
For restriction, choose `p : H.obj i₀ ⟶ j₀` by initiality and use `M.map p ≫ r`
as the retraction. Naturality of `u` proves the splitting identity. For an index `i`,
take a common stage `j` witnessing the original factorization to `H.obj i`, and choose
`q : H.obj l ⟶ j`. Cofilteredness gives a stage over `i₀`, `l`, and `i`. Initiality's
cofiltered equalization criterion refines this stage twice: first the two arrows to
`j₀` agree, then the two arrows to `H.obj i` agree. Applying `M` to these equalities
and to the original factorization gives the required restricted factorization.

Conversely, extend the cone `v` with Mathlib's `Functor.Initial.extendCone`, whose
component at any `j`, for any `p : H.obj i ⟶ j`, is `v.app i ≫ M.map p`.
At `H.obj i` use the identity arrow to recover exactly `v.app i`; in particular the
old retraction still splits. For an arbitrary `j`, choose `p : H.obj i ⟶ j` by
initiality and postcompose the common-stage factorization for `i` with `M.map p`.
The component formula gives the factorization for the extended cone. Finally these
two witness constructions prove the equivalence by unpacking the definition.
Source: Stacks Project, Categories, Lemma Tag 0A1T
(blueprint: lem-pur-essential-constant-cofinal-0a1s). -/
theorem initial_iff_essentiallyConstantProDiagram
    {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsCofiltered I] [IsCofiltered J]
    (H : I ⥤ J) [H.Initial] (M : J ⥤ C) (X : C) :
    (IsEssentiallyConstantProDiagram M X ↔
      IsEssentiallyConstantProDiagram (H ⋙ M) X) ∧
    (∀ u : (Functor.const J).obj X ⟶ M,
      (∃ j₀ : J, ∃ r : M.obj j₀ ⟶ X, u.app j₀ ≫ r = 𝟙 X ∧
        ∀ j : J, ∃ k : J, ∃ a : k ⟶ j₀, ∃ b : k ⟶ j,
          M.map b = M.map a ≫ r ≫ u.app j) →
      ∃ i₀ : I, ∃ r : M.obj (H.obj i₀) ⟶ X, u.app (H.obj i₀) ≫ r = 𝟙 X ∧
        ∀ i : I, ∃ k : I, ∃ a : k ⟶ i₀, ∃ b : k ⟶ i,
          M.map (H.map b) = M.map (H.map a) ≫ r ≫ u.app (H.obj i)) ∧
    (∀ v : (Functor.const I).obj X ⟶ H ⋙ M,
      (∃ i₀ : I, ∃ r : M.obj (H.obj i₀) ⟶ X, v.app i₀ ≫ r = 𝟙 X ∧
        ∀ i : I, ∃ k : I, ∃ a : k ⟶ i₀, ∃ b : k ⟶ i,
          M.map (H.map b) = M.map (H.map a) ≫ r ≫ v.app i) →
      ∃ u : (Functor.const J).obj X ⟶ M,
        (∃ j₀ : J, ∃ r : M.obj j₀ ⟶ X, u.app j₀ ≫ r = 𝟙 X ∧
          ∀ j : J, ∃ k : J, ∃ a : k ⟶ j₀, ∃ b : k ⟶ j,
            M.map b = M.map a ≫ r ≫ u.app j) ∧
        ∀ i : I, u.app (H.obj i) = v.app i) := by
  constructor
  · constructor
    · rintro ⟨_, u, hu⟩
      refine ⟨inferInstance, ?_⟩
      let v : (Functor.const I).obj X ⟶ H ⋙ M :=
        { app := fun i => u.app (H.obj i)
          naturality := fun i j f => by simpa using u.naturality (H.map f) }
      exact ⟨v, restrict_witness H M X u hu⟩
    · rintro ⟨_, v, hv⟩
      obtain ⟨u, hu, _⟩ := extend_witness H M X v hv
      exact ⟨inferInstance, u, hu⟩
  · exact ⟨restrict_witness H M X, extend_witness H M X⟩

end CategoryTheory
