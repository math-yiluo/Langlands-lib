/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Representable
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.Triangulated.ReductionTriangleMate
public import WeilConjectures.CategoryTheory.Triangulated.PreservesProducts

/-!
# Pro-constant towers of representing objects

Let `Φ : C ⥤ D` be a triangulated functor and `P` a shift-stable property of objects of `C`.
This file complements `CategoryTheory.Functor.RepresentsOn`:

* `CategoryTheory.Functor.RepresentsOn.shift`: shifts of representing maps represent;
* `CategoryTheory.Functor.RepresentsOn.of_distTriang₃`: the five lemma for representing maps,
  for the third component of a morphism of triangles;
* `CategoryTheory.Pretriangulated.IsHomotopyLimit.nonempty_iso_of_proConstant`: the homotopy
  limit of a tower which is pro-isomorphic to a constant tower `H` is isomorphic to `H`;
* `CategoryTheory.Pretriangulated.exists_proConstant_of_distTriang`: a tower `Nₙ` sitting in
  distinguished triangles `H --0--> H ⟶ Nₙ ⟶ H⟦1⟧`, compatibly with the transition maps, whose
  transition maps kill the connecting morphisms, is pro-isomorphic to the constant tower `H`;
* `CategoryTheory.Functor.RepresentsOn.nonempty_iso_of_isHomotopyLimit`: pro-isomorphisms with
  a constant tower transport along representing maps, so that the homotopy limit of a tower of
  objects representing a pro-constant tower is isomorphic to the representing object of the
  constant value.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Opposite Pretriangulated

namespace Pretriangulated

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The homotopy limit of a tower `F` which is pro-isomorphic to the constant tower `H` is
isomorphic to `H`: here `a : F ⟶ H` and `bₙ : H ⟶ Fₙ` satisfy `bₙ ≫ aₙ = 𝟙` and
`aₙ₊₁ ≫ bₙ = F.map (n + 1 ⟶ n)`. -/
theorem IsHomotopyLimit.nonempty_iso_of_proConstant {F : ℕᵒᵖ ⥤ C} {c : Cone F}
    (hc : IsHomotopyLimit c) {H : C} [HasProduct fun _ : ℕ ↦ H]
    (a : F ⟶ (Functor.const ℕᵒᵖ).obj H) (b : ∀ n : ℕ, H ⟶ F.obj (op n))
    (hb₁ : ∀ n, b n ≫ a.app (op n) = 𝟙 H)
    (hb₂ : ∀ n, a.app (op (n + 1)) ≫ b n = F.map (homOfLE n.le_succ).op) :
    Nonempty (c.pt ≅ H) := by
  obtain ⟨PF, hPF, δX, hX⟩ := hc
  have : HasProduct fun n : ℕ ↦ ((Functor.const ℕᵒᵖ).obj H).obj (op n) :=
    inferInstanceAs (HasProduct fun _ : ℕ ↦ H)
  let cH : Cone ((Functor.const ℕᵒᵖ).obj H) := { pt := H, π := 𝟙 _ }
  have : ∀ n, IsIso (cH.π.app n) := fun _ ↦ IsIso.id _
  obtain ⟨PG, hPG, δY, hY⟩ := IsHomotopyLimit.of_isIso_π cH
  obtain ⟨u, hu₁, hu₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hX hY
    (productTowerMap (PF := PF) hPG a) (productTowerMap (PF := PF) hPG a)
    (productTowerMap_comp_sub_towerShift hPF hPG a).symm
  exact ⟨@asIso _ _ _ _ u (isIso_of_proIso hPF hPG hX hY a b hb₁ hb₂ u hu₁ hu₃)⟩

/-- Let `Nₙ` be a tower with distinguished triangles `H --0--> H --bₙ--> Nₙ --dₙ--> H⟦1⟧`, such
that `bₙ₊₁ ≫ N.map (n + 1 ⟶ n) = bₙ` and `N.map (n + 1 ⟶ n) ≫ dₙ = 0`. Then `N` is
pro-isomorphic to the constant tower `H`: there is `a : N ⟶ H` with `bₙ ≫ aₙ = 𝟙` and
`aₙ₊₁ ≫ bₙ = N.map (n + 1 ⟶ n)`. -/
theorem exists_proConstant_of_distTriang {N : ℕᵒᵖ ⥤ C} {H : C} (b : ∀ n : ℕ, H ⟶ N.obj (op n))
    (d : ∀ n : ℕ, N.obj (op n) ⟶ H⟦(1 : ℤ)⟧)
    (hT : ∀ n, Triangle.mk (0 : H ⟶ H) (b n) (d n) ∈ distTriang C)
    (hb : ∀ n, b (n + 1) ≫ N.map (homOfLE n.le_succ).op = b n)
    (hd : ∀ n, N.map (homOfLE n.le_succ).op ≫ d n = 0) :
    ∃ a : N ⟶ (Functor.const ℕᵒᵖ).obj H, (∀ n, b n ≫ a.app (op n) = 𝟙 H) ∧
      ∀ n, a.app (op (n + 1)) ≫ b n = N.map (homOfLE n.le_succ).op := by
  have hmono (n : ℕ) : Mono (b n) := by
    obtain ⟨r, hr⟩ := Triangle.yoneda_exact₂ _ (hT n) (𝟙 H) (by simp)
    have hr' : b n ≫ r = 𝟙 H := hr.symm
    exact ⟨fun g h hgh ↦ by simpa [hr'] using hgh =≫ r⟩
  obtain ⟨r, hr⟩ : ∃ r : N.obj (op 0) ⟶ H, b 0 ≫ r = 𝟙 H := by
    obtain ⟨r, hr⟩ := Triangle.yoneda_exact₂ _ (hT 0) (𝟙 H) (by simp)
    exact ⟨r, hr.symm⟩
  obtain ⟨x, hx⟩ : ∃ x : ∀ n : ℕ, N.obj (op (n + 1)) ⟶ H,
      ∀ n, x n ≫ b n = N.map (homOfLE n.le_succ).op :=
    ⟨fun n ↦ (Triangle.coyoneda_exact₃ _ (hT n) _ (hd n)).choose,
      fun n ↦ (Triangle.coyoneda_exact₃ _ (hT n) _ (hd n)).choose_spec.symm⟩
  have hbx (n : ℕ) : b (n + 1) ≫ x n = 𝟙 H := by
    rw [← cancel_mono (b n), assoc, hx, hb, id_comp]
  let app : ∀ n : ℕ, N.obj (op n) ⟶ H := fun n ↦ Nat.casesOn n r fun n ↦ x n
  have happ (n : ℕ) : app (n + 1) = x n := rfl
  refine ⟨NatTrans.ofOpSequence app fun n ↦ ?_, fun n ↦ ?_, fun n ↦ ?_⟩
  · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    rw [happ]
    cases n with
    | zero =>
      rw [← hx, assoc]
      exact (congrArg (x 0 ≫ ·) hr).trans (Category.comp_id _)
    | succ n => rw [happ, ← hx, assoc, hbx, Category.comp_id]
  · cases n with
    | zero => exact hr
    | succ n => exact hbx n
  · exact hx n

end Pretriangulated

namespace Functor.RepresentsOn

variable {C D : Type*} [Category C] [Category D] {Φ : C ⥤ D} {P : ObjectProperty C}

section Triangulated

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [Φ.CommShift ℤ] [Φ.Additive]
  [P.IsStableUnderShift ℤ]

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [Φ.Additive] in
/-- Shifts of representing maps represent: if `ε : Φ.obj T ⟶ M` represents on a shift-stable
property `P`, so does `Φ(T⟦n⟧) ≅ (Φ T)⟦n⟧ ⟶ M⟦n⟧`. -/
lemma shift {T : C} {M : D} {ε : Φ.obj T ⟶ M} (hε : Φ.RepresentsOn P ε) (n : ℤ) :
    Φ.RepresentsOn P ((Φ.commShiftIso n).hom.app T ≫ ε⟦n⟧') := by
  intro A hA
  let e : A ≅ (A⟦-n⟧)⟦n⟧ := ((shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).app A).symm
  let e' : Φ.obj A ≅ (Φ.obj (A⟦-n⟧))⟦n⟧ := Φ.mapIso e ≪≫ (Φ.commShiftIso n).app (A⟦-n⟧)
  have h₁ : Function.Bijective fun g : A⟦-n⟧ ⟶ T ↦ e.hom ≫ g⟦n⟧' :=
    (Equiv.bijective ⟨fun f ↦ e.hom ≫ f, fun f ↦ e.inv ≫ f, fun f ↦ by simp,
      fun f ↦ by simp⟩).comp
      ((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C n)).map_bijective _ _)
  have h₂ : Function.Bijective fun h : Φ.obj (A⟦-n⟧) ⟶ M ↦ e'.hom ≫ h⟦n⟧' :=
    (Equiv.bijective ⟨fun f ↦ e'.hom ≫ f, fun f ↦ e'.inv ≫ f, fun f ↦ by simp,
      fun f ↦ by simp⟩).comp
      ((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor D n)).map_bijective _ _)
  rw [← Function.Bijective.of_comp_iff _ h₁]
  convert h₂.comp (hε _ (P.le_shift (-n) A hA)) using 1
  funext g
  simp only [e', Function.comp_apply, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Φ.map_comp,
    assoc, Functor.map_comp]
  rw [Φ.commShiftIso_hom_naturality_assoc]

/-- The five lemma for representing maps, third component: let `T₁` be a distinguished triangle
in `C`, `T₂` a distinguished triangle in `D`, and `(a, b, c)` a morphism from the image of `T₁`
under `Φ` to `T₂`. If `a` and `b` represent on a shift-stable property `P`, then so does `c`. -/
lemma of_distTriang₃ {T₁ : Triangle C} (hT₁ : T₁ ∈ distTriang C) {T₂ : Triangle D}
    (hT₂ : T₂ ∈ distTriang D) (a : Φ.obj T₁.obj₁ ⟶ T₂.obj₁) (b : Φ.obj T₁.obj₂ ⟶ T₂.obj₂)
    (c : Φ.obj T₁.obj₃ ⟶ T₂.obj₃) (comm₁ : Φ.map T₁.mor₁ ≫ b = a ≫ T₂.mor₁)
    (comm₂ : Φ.map T₁.mor₂ ≫ c = b ≫ T₂.mor₂)
    (comm₃ : Φ.map T₁.mor₃ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app T₁.obj₁ ≫ a⟦(1 : ℤ)⟧' =
      c ≫ T₂.mor₃)
    (ha : Φ.RepresentsOn P a) (hb : Φ.RepresentsOn P b) : Φ.RepresentsOn P c := by
  refine of_distTriang (rot_of_distTriang _ (rot_of_distTriang _ hT₁))
    (rot_of_distTriang _ (rot_of_distTriang _ hT₂)) c
    ((Φ.commShiftIso (1 : ℤ)).hom.app T₁.obj₁ ≫ a⟦(1 : ℤ)⟧')
    ((Φ.commShiftIso (1 : ℤ)).hom.app T₁.obj₂ ≫ b⟦(1 : ℤ)⟧') ?_ ?_ ?_ (ha.shift 1) (hb.shift 1)
  · exact comm₃
  · have h : Φ.map (-T₁.mor₁⟦(1 : ℤ)⟧') ≫ (Φ.commShiftIso (1 : ℤ)).hom.app T₁.obj₂ ≫ b⟦(1 : ℤ)⟧' =
        ((Φ.commShiftIso (1 : ℤ)).hom.app T₁.obj₁ ≫ a⟦(1 : ℤ)⟧') ≫ (-T₂.mor₁⟦(1 : ℤ)⟧') := by
      simp only [Φ.map_neg, Preadditive.neg_comp, Preadditive.comp_neg, assoc,
        Φ.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, comm₁]
    exact h
  · have h : Φ.map (-T₁.mor₂⟦(1 : ℤ)⟧') ≫ (Φ.commShiftIso (1 : ℤ)).hom.app T₁.obj₃ ≫ c⟦(1 : ℤ)⟧' =
        ((Φ.commShiftIso (1 : ℤ)).hom.app T₁.obj₂ ≫ b⟦(1 : ℤ)⟧') ≫ (-T₂.mor₂⟦(1 : ℤ)⟧') := by
      simp only [Φ.map_neg, Preadditive.neg_comp, Preadditive.comp_neg, assoc,
        Φ.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, comm₂]
    exact h

end Triangulated

/-- Pro-isomorphisms with a constant tower transport along representing maps: let
`γ : W ⋙ Φ ⟶ N` be a morphism of towers whose components represent on `P`, with all `Wₙ`
satisfying `P`, and `e : Φ R ⟶ H` represent on `P`, with `P R`. If `N` is pro-isomorphic to the
constant tower `H` (through `a : N ⟶ H` and `bₙ : H ⟶ Nₙ`), then `W` is pro-isomorphic to the
constant tower `R`. -/
lemma exists_proConstant {W : ℕᵒᵖ ⥤ C} {N : ℕᵒᵖ ⥤ D} (γ : W ⋙ Φ ⟶ N)
    (hγ : ∀ n : ℕ, Φ.RepresentsOn P (γ.app (op n))) (hW : ∀ n : ℕ, P (W.obj (op n))) {R : C}
    {H : D} {e : Φ.obj R ⟶ H} (he : Φ.RepresentsOn P e) (hR : P R)
    (a : N ⟶ (Functor.const ℕᵒᵖ).obj H) (b : ∀ n : ℕ, H ⟶ N.obj (op n))
    (hb₁ : ∀ n, b n ≫ a.app (op n) = 𝟙 H)
    (hb₂ : ∀ n, a.app (op (n + 1)) ≫ b n = N.map (homOfLE n.le_succ).op) :
    ∃ (a' : W ⟶ (Functor.const ℕᵒᵖ).obj R) (b' : ∀ n : ℕ, R ⟶ W.obj (op n)),
      (∀ n, b' n ≫ a'.app (op n) = 𝟙 R) ∧
        ∀ n, a'.app (op (n + 1)) ≫ b' n = W.map (homOfLE n.le_succ).op := by
  choose x hx using fun n : ℕ ↦ (he _ (hW n)).2 (γ.app (op n) ≫ a.app (op n))
  choose y hy using fun n : ℕ ↦ (hγ n _ hR).2 (e ≫ b n)
  have hx' (n : ℕ) : Φ.map (x n) ≫ e = γ.app (op n) ≫ a.app (op n) := hx n
  have hy' (n : ℕ) : Φ.map (y n) ≫ γ.app (op n) = e ≫ b n := hy n
  have hγn (n : ℕ) : Φ.map (W.map (homOfLE n.le_succ).op) ≫ γ.app (op n) =
      γ.app (op (n + 1)) ≫ N.map (homOfLE n.le_succ).op := γ.naturality _
  have han (n : ℕ) : N.map (homOfLE n.le_succ).op ≫ a.app (op n) = a.app (op (n + 1)) := by
    simp
  refine ⟨NatTrans.ofOpSequence x fun n ↦ ?_, y, fun n ↦ ?_, fun n ↦ ?_⟩
  · refine ((he _ (hW (n + 1))).1 ?_).trans (Category.comp_id _).symm
    simp only [Φ.map_comp, assoc, hx']
    rw [reassoc_of% hγn, han]
  · refine (he _ hR).1 ?_
    simp only [NatTrans.ofOpSequence_app, Φ.map_comp, assoc, hx', reassoc_of% hy', hb₁,
      Φ.map_id, id_comp, comp_id]
  · refine (hγ n _ (hW (n + 1))).1 ?_
    simp only [NatTrans.ofOpSequence_app, Φ.map_comp, assoc, hy', reassoc_of% hx', hb₂, hγn]

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The homotopy limit of a tower `W` of objects representing a tower `N` which is
pro-isomorphic to a constant tower `H` is isomorphic to the representing object `R` of `H`. -/
theorem nonempty_iso_of_isHomotopyLimit {W : ℕᵒᵖ ⥤ C} {N : ℕᵒᵖ ⥤ D} (γ : W ⋙ Φ ⟶ N)
    (hγ : ∀ n : ℕ, Φ.RepresentsOn P (γ.app (op n))) (hW : ∀ n : ℕ, P (W.obj (op n))) {R : C}
    [HasProduct fun _ : ℕ ↦ R] {H : D} {e : Φ.obj R ⟶ H} (he : Φ.RepresentsOn P e) (hR : P R)
    (a : N ⟶ (Functor.const ℕᵒᵖ).obj H) (b : ∀ n : ℕ, H ⟶ N.obj (op n))
    (hb₁ : ∀ n, b n ≫ a.app (op n) = 𝟙 H)
    (hb₂ : ∀ n, a.app (op (n + 1)) ≫ b n = N.map (homOfLE n.le_succ).op) {c : Cone W}
    (hc : IsHomotopyLimit c) : Nonempty (c.pt ≅ R) := by
  obtain ⟨a', b', hb₁', hb₂'⟩ := exists_proConstant γ hγ hW he hR a b hb₁ hb₂
  exact hc.nonempty_iso_of_proConstant a' b' hb₁' hb₂'

variable [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- **Reduction of the derived limit of partial right adjoints.** Let `Φ : C ⥤ D` be triangulated
and `Q_C`, `Q_D` natural cones of the multiplication by an integer `m'` on `C` and `D` (natural
distinguished triangles `K --m'--> K --η--> Q K --δ--> K⟦1⟧`), compatible with `Φ` through
`ρ : Φ ⋙ Q_D ⟶ Q_C ⋙ Φ`. Let `L ∈ D` and `M` a tower with distinguished triangles
`L --mⁿ⁺¹--> L --πₙ--> Mₙ --dₙ--> L⟦1⟧`, compatible with transition maps `(m, 𝟙, -)`, where `m`
kills the image of `Q_D`. Let `ε : T ⋙ Φ ⟶ M` be a morphism of towers whose components represent
on a triangulated property `P`, with all `Tₙ` in `P`, and let `e : Φ R ⟶ Q_D L` represent on `P`,
with `R` in `P`. Then `Q_C` of the homotopy limit of `T` satisfies `P` (it is isomorphic to `R`).

The tower `Q_D Mₙ` is pro-isomorphic to the constant tower `Q_D L`
(`CategoryTheory.Pretriangulated.exists_proConstant_of_distTriang`), and `Q_C Tₙ` represents
`Q_D Mₙ` by the five lemma; `Q_C` commutes with homotopy limits, preserving products. -/
theorem prop_obj_homotopyLimit_of_distTriang [HasLimitsOfShape (Discrete ℕ) C]
    [Φ.CommShift ℤ] [Φ.IsTriangulated] [Φ.Additive] [P.IsStableUnderShift ℤ]
    [P.IsTriangulatedClosed₃] [P.IsClosedUnderIsomorphisms]
    {QC : C ⥤ C} [QC.CommShift ℤ] [QC.IsTriangulated] (ηC : 𝟭 C ⟶ QC)
    (δC : QC ⟶ shiftFunctor C (1 : ℤ)) {QD : D ⥤ D} [QD.CommShift ℤ] [QD.IsTriangulated]
    (ηD : 𝟭 D ⟶ QD) (δD : QD ⟶ shiftFunctor D (1 : ℤ)) (m' : ℤ)
    (hC : ∀ K, Triangle.mk (m' • 𝟙 K) (ηC.app K) (δC.app K) ∈ distTriang C)
    (hD : ∀ K, Triangle.mk (m' • 𝟙 K) (ηD.app K) (δD.app K) ∈ distTriang D)
    (ρ : Φ ⋙ QD ⟶ QC ⋙ Φ) (hρη : ∀ K, ηD.app (Φ.obj K) ≫ ρ.app K = Φ.map (ηC.app K))
    (hρδ : ∀ K, ρ.app K ≫ Φ.map (δC.app K) ≫ (Φ.commShiftIso (1 : ℤ)).hom.app K =
      δD.app (Φ.obj K))
    (m : ℤ) (hm : ∀ X, m • 𝟙 (QD.obj X) = 0) {L : D} {M : ℕᵒᵖ ⥤ D}
    (π : ∀ n : ℕ, L ⟶ M.obj (op n)) (d : ∀ n : ℕ, M.obj (op n) ⟶ L⟦(1 : ℤ)⟧)
    (hL : ∀ n, Triangle.mk ((m ^ (n + 1)) • 𝟙 L) (π n) (d n) ∈ distTriang D)
    (hπ : ∀ n, π (n + 1) ≫ M.map (homOfLE n.le_succ).op = π n)
    (hd : ∀ n, M.map (homOfLE n.le_succ).op ≫ d n = d (n + 1) ≫ (m • 𝟙 L)⟦(1 : ℤ)⟧')
    {T : ℕᵒᵖ ⥤ C} (hT : ∀ n : ℕ, P (T.obj (op n))) (ε : T ⋙ Φ ⟶ M)
    (hε : ∀ n : ℕ, Φ.RepresentsOn P (ε.app (op n))) {R : C} (hR : P R)
    {e : Φ.obj R ⟶ QD.obj L} (he : Φ.RepresentsOn P e) {c : Cone T}
    (hc : IsHomotopyLimit c) : P (QC.obj c.pt) := by
  have : PreservesLimit (Discrete.functor fun n : ℕ ↦ T.obj (op n)) QC :=
    preservesLimit_discrete_of_distTriang QC m' ηC δC hC _
  have hc' := hc.map QC
  have hρ (K : C) : IsIso (ρ.app K) := by
    have hT : Triangle.mk (Φ.map (m' • 𝟙 K)) (Φ.map (ηC.app K))
        (Φ.map (δC.app K) ≫ (Φ.commShiftIso (1 : ℤ)).hom.app K) ∈ distTriang D :=
      Φ.map_distinguished _ (hC K)
    refine isIso₃_of_isIso₁₂ (Triangle.homMk
      (Triangle.mk (m' • 𝟙 (Φ.obj K)) (ηD.app (Φ.obj K)) (δD.app (Φ.obj K)))
      (Triangle.mk (Φ.map (m' • 𝟙 K)) (Φ.map (ηC.app K))
        (Φ.map (δC.app K) ≫ (Φ.commShiftIso (1 : ℤ)).hom.app K)) (𝟙 (Φ.obj K)) (𝟙 (Φ.obj K))
      (ρ.app K)
      ?_ ?_ ?_) (hD _) hT ?_ ?_
    · simp [Φ.map_zsmul]
    · exact (hρη K).trans (Category.id_comp _).symm
    · exact ((congrArg (fun g ↦ δD.app (Φ.obj K) ≫ g) ((shiftFunctor D (1 : ℤ)).map_id _)).trans
        (Category.comp_id _)).trans (hρδ K).symm
    · exact IsIso.id _
    · exact IsIso.id _
  have : IsIso ρ := NatIso.isIso_of_isIso_app ρ
  let γ₁ : T ⋙ QC ⋙ Φ ⟶ T ⋙ Φ ⋙ QD := Functor.whiskerLeft T (CategoryTheory.inv ρ)
  let γ : (T ⋙ QC) ⋙ Φ ⟶ M ⋙ QD := γ₁ ≫ Functor.whiskerRight ε QD
  have hγ (n : ℕ) : Φ.RepresentsOn P (γ.app (op n)) := by
    have hη := ηD.naturality (ε.app (op n))
    have hδ := δD.naturality (ε.app (op n))
    have h₁ := hρη (T.obj (op n))
    have h₂ := hρδ (T.obj (op n))
    dsimp at hη hδ
    have hγn : γ.app (op n) =
        CategoryTheory.inv (ρ.app (T.obj (op n))) ≫ QD.map (ε.app (op n)) := by
      simp [γ, γ₁, NatIso.isIso_inv_app]
    refine of_distTriang₃ (hC (T.obj (op n))) (hD (M.obj (op n))) (ε.app (op n)) (ε.app (op n))
      (γ.app (op n)) ?_ ?_ ?_ (hε n) (hε n)
    · have h : Φ.map (m' • 𝟙 (T.obj (op n))) ≫ ε.app (op n) =
          ε.app (op n) ≫ (m' • 𝟙 (M.obj (op n))) := by
        rw [Φ.map_zsmul, CategoryTheory.Functor.map_id, Preadditive.zsmul_comp,
          Preadditive.comp_zsmul, Category.id_comp, Category.comp_id]
      exact h
    · have h : Φ.map (ηC.app (T.obj (op n))) ≫ γ.app (op n) =
          ε.app (op n) ≫ ηD.app (M.obj (op n)) := by
        rw [hγn, ← h₁, Category.assoc, IsIso.hom_inv_id_assoc]
        exact hη.symm
      exact h
    · have h : Φ.map (δC.app (T.obj (op n))) ≫
          (Φ.commShiftIso (1 : ℤ)).hom.app (T.obj (op n)) ≫ (ε.app (op n))⟦(1 : ℤ)⟧' =
          γ.app (op n) ≫ δD.app (M.obj (op n)) := by
        rw [hγn, ← cancel_epi (ρ.app (T.obj (op n))), Category.assoc, IsIso.hom_inv_id_assoc,
          reassoc_of% h₂]
        exact hδ.symm
      exact h
  have hm' (k : ℕ) (X : D) : (m ^ (k + 1)) • 𝟙 (QD.obj X) = 0 := by
    rw [pow_succ, mul_smul, hm, smul_zero]
  obtain ⟨a, hb₁, hb₂⟩ := exists_proConstant_of_distTriang (N := M ⋙ QD)
    (fun n ↦ QD.map (π n)) (fun n ↦ QD.map (d n) ≫ (QD.commShiftIso (1 : ℤ)).hom.app L)
    (fun n ↦ by
      have h₀ : QD.map ((m ^ (n + 1)) • 𝟙 L) = 0 := by
        rw [QD.map_zsmul, CategoryTheory.Functor.map_id, hm']
      have hT' : Triangle.mk (QD.map ((m ^ (n + 1)) • 𝟙 L)) (QD.map (π n))
          (QD.map (d n) ≫ (QD.commShiftIso (1 : ℤ)).hom.app L) ∈ distTriang D :=
        QD.map_distinguished _ (hL n)
      rwa [h₀] at hT')
    (fun n ↦ by simp only [Functor.comp_map, ← QD.map_comp, hπ])
    (fun n ↦ by
      have h₀ : QD.map ((m • 𝟙 L)⟦(1 : ℤ)⟧') = 0 := by
        rw [Functor.map_zsmul, CategoryTheory.Functor.map_id, QD.map_zsmul,
          CategoryTheory.Functor.map_id, hm]
      simp only [Functor.comp_map, ← QD.map_comp_assoc, hd, QD.map_comp, h₀, zero_comp,
        comp_zero])
  obtain ⟨f⟩ := nonempty_iso_of_isHomotopyLimit γ hγ
    (fun n ↦ P.ext_of_isTriangulatedClosed₃ _ (hC _) (hT n) (hT n)) he hR a _ hb₁ hb₂ hc'
  exact P.prop_of_iso f.symm hR

end Functor.RepresentsOn

section ReductionTriangle

open Functor.RepresentsOn

variable {AY AZ NY NZ : Type*} [Category AY] [Category AZ] [Category NY] [Category NZ]
  [HasZeroObject AY] [HasShift AY ℤ] [Preadditive AY] [∀ n : ℤ, (shiftFunctor AY n).Additive]
  [Pretriangulated AY] [HasZeroObject AZ] [HasShift AZ ℤ] [Preadditive AZ]
  [∀ n : ℤ, (shiftFunctor AZ n).Additive] [Pretriangulated AZ]

/-- **Reduction of the derived limit of partial right adjoints**, for reductions given by
adjunctions `red ⊣ Res` with natural reduction triangles `M --k--> M --η--> Res (red M) --δ--> M⟦1⟧`
(the unit `η` of `red ⊣ Res`), and a right adjoint `F` commuting with the reductions through
the mate of a pullback comparison `β` (the setting of
`CategoryTheory.isIso_mateEquiv_of_reductionTriangle`). Let `L ∈ A_Y` and `M` a tower with
distinguished triangles `L --mⁿ⁺¹--> L --πₙ--> Mₙ --dₙ--> L⟦1⟧` compatible with transition maps
`(m, 𝟙, -)`, where `m` kills `Res_Y (red_Y -)`. If `ε : T ⋙ F ⟶ M` has components representing on
a triangulated property `P`, all `Tₙ` satisfy `P`, and `e : F R ⟶ Res_Y (red_Y L)` represents on
`P` with `P R`, then `Res_Z (red_Z G)` satisfies `P` for the homotopy limit `G` of `T`. -/
theorem prop_obj_homotopyLimit_of_reductionTriangle [HasLimitsOfShape (Discrete ℕ) AZ]
    {redY : AY ⥤ NY} {resY : NY ⥤ AY} (adjY : redY ⊣ resY)
    {redZ : AZ ⥤ NZ} {resZ : NZ ⥤ AZ} (adjZ : redZ ⊣ resZ)
    {G : AY ⥤ AZ} {F : AZ ⥤ AY} (adj : G ⊣ F)
    {G' : NY ⥤ NZ} {F' : NZ ⥤ NY} (adj' : G' ⊣ F')
    (β : G ⋙ redZ ≅ redY ⋙ G') (ι : resY ⋙ G ≅ G' ⋙ resZ)
    [G.CommShift ℤ] [F.CommShift ℤ] [adj.CommShift ℤ] [F.IsTriangulated] [F.Additive]
    [(redY ⋙ resY).CommShift ℤ] [(redY ⋙ resY).IsTriangulated]
    [(redZ ⋙ resZ).CommShift ℤ] [(redZ ⋙ resZ).IsTriangulated]
    (δY : redY ⋙ resY ⟶ shiftFunctor AY (1 : ℤ)) (δZ : redZ ⋙ resZ ⟶ shiftFunctor AZ (1 : ℤ))
    (k : ℤ) (hY : ∀ M, Triangle.mk (k • 𝟙 M) (adjY.unit.app M) (δY.app M) ∈ distTriang AY)
    (hZ : ∀ M, Triangle.mk (k • 𝟙 M) (adjZ.unit.app M) (δZ.app M) ∈ distTriang AZ)
    (hι : ∀ M, G.map (adjY.unit.app M) ≫ ι.hom.app (redY.obj M) =
      adjZ.unit.app (G.obj M) ≫ resZ.map (β.hom.app M))
    (hδ : ∀ M, G.map (δY.app M) ≫ (G.commShiftIso (1 : ℤ)).hom.app M =
      ι.hom.app (redY.obj M) ≫ resZ.map (β.inv.app M) ≫ δZ.app (G.obj M))
    {P : ObjectProperty AZ} [P.IsStableUnderShift ℤ] [P.IsTriangulatedClosed₃]
    [P.IsClosedUnderIsomorphisms]
    (m : ℤ) (hm : ∀ X, m • 𝟙 (resY.obj (redY.obj X)) = 0) {L : AY} {M : ℕᵒᵖ ⥤ AY}
    (π : ∀ n : ℕ, L ⟶ M.obj (op n)) (d : ∀ n : ℕ, M.obj (op n) ⟶ L⟦(1 : ℤ)⟧)
    (hL : ∀ n, Triangle.mk ((m ^ (n + 1)) • 𝟙 L) (π n) (d n) ∈ distTriang AY)
    (hπ : ∀ n, π (n + 1) ≫ M.map (homOfLE n.le_succ).op = π n)
    (hd : ∀ n, M.map (homOfLE n.le_succ).op ≫ d n = d (n + 1) ≫ (m • 𝟙 L)⟦(1 : ℤ)⟧')
    {T : ℕᵒᵖ ⥤ AZ} (hT : ∀ n : ℕ, P (T.obj (op n))) (ε : T ⋙ F ⟶ M)
    (hε : ∀ n : ℕ, F.RepresentsOn P (ε.app (op n))) {R : AZ} (hR : P R)
    {e : F.obj R ⟶ resY.obj (redY.obj L)} (he : F.RepresentsOn P e) {c : Cone T}
    (hc : IsHomotopyLimit c) : P (resZ.obj (redZ.obj c.pt)) := by
  have hι' := mateEquiv_eq_of_map_unit_comp_hom_app adjY adjZ β ι hι
  exact prop_obj_homotopyLimit_of_distTriang (QC := redZ ⋙ resZ) (QD := redY ⋙ resY)
    adjZ.unit δZ adjY.unit δY k hZ hY
    (Functor.whiskerRight (mateEquiv adj adj' β.inv) resY ≫
      Functor.whiskerLeft redZ (conjugateEquiv (adjY.comp adj') (adj.comp adjZ) β.hom))
    (unit_comp_map_reductionComparison adjY adjZ adj adj' β ι hι')
    (map_reductionComparison_comp_δ adjY adjZ adj adj' β ι δY δZ hι' hδ) m hm π d hL hπ hd hT ε
    hε hR he hc

end ReductionTriangle

end CategoryTheory
