/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfFiniteAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
public import WeilConjectures.CategoryTheory.Triangulated.CompactBoundedHom
public import WeilConjectures.CategoryTheory.Triangulated.CompactFamily
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.CoproductTriangle

/-!
# Compactness from a uniform Ext bound against a heart

Blueprints `theorem-compactness-rational-coefficients`, `lemma-reduction-finitely-many-degrees` and
`proposition-compactness-proper-direct-image--1`, in the abstract form used there. Let `C` be an
abelian category with exact coproducts and exact countable products, and `P` a class of objects of
`C` closed under coproducts (the ind-constructible sheaves). Let `s` be an object of `D(C)` which is
bounded above (a constructible sheaf in degree `0`) such that

* `Hom(s, B[-n]) = 0` for `B` in `P` and `n` large (the uniform bound `Ext^q(s, B) = 0` for
  `q > d`), and
* `Hom(s, -[-n])` commutes with direct sums of objects of `P`.

Then `Hom(s, -)` commutes with direct sums of objects of `D(C)` with cohomology in `P`
(`DerivedCategory.compactFor_of_homologyProperty`).

The proof follows the blueprint: by induction on the amplitude, `s` is compact for uniformly
bounded families (`DerivedCategory.compactFor_of_isGE_of_isLE`); maps from `s` to an object
with cohomology in `P` in sufficiently negative degrees vanish, by induction on the amplitude for
bounded objects and by left completeness of `D(C)` in general
(`DerivedCategory.eq_zero_of_isLE`); hence morphisms out of `s` only see a finite window of
degrees, on which the bounded case applies.
-/

@[expose] public section

universe w

open CategoryTheory Category Limits Pretriangulated Preadditive

namespace CategoryTheory

namespace CompactFor

section Preadditive

variable {C : Type*} [Category* C] [Preadditive C]

/-- In a finite coproduct, the identity is the sum of the composites of the projections (through
the biproduct) with the inclusions. -/
lemma _root_.CategoryTheory.Limits.sum_isoCoproduct_inv_π_ι {S : Type*} [Fintype S] (B : S → C)
    [HasBiproduct B] :
    ∑ x, (biproduct.isoCoproduct B).inv ≫ biproduct.π B x ≫ Sigma.ι B x = 𝟙 (∐ B) := by
  classical
  refine Sigma.hom_ext _ _ fun j ↦ ?_
  have hj (x : S) : Sigma.ι B j ≫ (biproduct.isoCoproduct B).inv ≫ biproduct.π B x ≫
      Sigma.ι B x = if x = j then Sigma.ι B j else 0 := by
    split_ifs with h
    · subst h
      simp
    · simp [biproduct.ι_π_ne_assoc _ (Ne.symm h)]
  rw [comp_sum, comp_id, Finset.sum_congr rfl fun x _ ↦ hj x]
  simp

/-- Compactness for a family is invariant under isomorphisms of the family. -/
lemma of_iso {s : C} {J : Type*} {A T : J → C} [HasCoproduct A] [HasCoproduct T]
    (e : ∀ j, A j ≅ T j) (hT : CompactFor s T) : CompactFor s A :=
  hT.of_bijective (fun j ↦ (e j).hom) (fun j f ↦ ⟨f ≫ (e j).inv, by simp⟩)
    (fun f g h ↦ by simpa [Sigma.map_comp_map] using h =≫ Limits.Sigma.map fun j ↦ (e j).inv)

end Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Compactness for families is stable under extensions: if `T j` is a family of distinguished
triangles and `s` is compact for the families of first and third terms, it is compact for the
family of middle terms. -/
lemma of_distTriang {s : C} {J : Type*} [HasColimitsOfShape (Discrete J) C]
    (T : J → Triangle C) (hT : ∀ j, T j ∈ distTriang C)
    (h₁ : CompactFor s fun j ↦ (T j).obj₁)
    (h₃ : CompactFor s fun j ↦ (T j).obj₃) : CompactFor s fun j ↦ (T j).obj₂ := by
  classical
  have hS := coproductTriangle_distinguished T hT
  intro f
  obtain ⟨S₃, g, hg⟩ := h₃ (f ≫ (coproductTriangle T).mor₂)
  have hc : IsColimit (Cofan.mk ((∐ fun j ↦ (T j).obj₁)⟦(1 : ℤ)⟧)
      fun j ↦ (Sigma.ι (fun j ↦ (T j).obj₁) j)⟦(1 : ℤ)⟧') :=
    isColimitCofanMkObjOfIsColimit (shiftFunctor C (1 : ℤ)) _ _ (coproductIsCoproduct _)
  -- the components `gⱼ` lift along `(T j).mor₂`
  have hb (j : J) (hj : j ∈ S₃) : ∃ b : s ⟶ (T j).obj₂, g j = b ≫ (T j).mor₂ := by
    refine Triangle.coyoneda_exact₃ _ (hT j) (g j) ?_
    refine BrownRepresentability.eq_zero_of_sum_comp_inj_eq_zero hc S₃
      (fun j ↦ g j ≫ (T j).mor₃) ?_ hj
    have h0 : (coproductTriangle T).mor₂ ≫ (coproductTriangle T).mor₃ = 0 :=
      comp_distTriang_mor_zero₂₃ _ hS
    calc _ = ∑ j ∈ S₃, g j ≫ Sigma.ι (fun j ↦ (T j).obj₃) j ≫
          (coproductTriangle T).mor₃ := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          have := (coproductTriangle.ι T j).comm₃
          simp only [coproductTriangle.ι_hom₃, coproductTriangle.ι_hom₁] at this
          simp [this]
      _ = (f ≫ (coproductTriangle T).mor₂) ≫ (coproductTriangle T).mor₃ := by
          rw [hg, sum_comp]
          simp only [assoc]
      _ = 0 := by rw [assoc, h0, comp_zero]
  choose b hb using hb
  let b' (j : J) : s ⟶ (T j).obj₂ := if hj : j ∈ S₃ then b j hj else 0
  obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ _ hS
      (f - ∑ j ∈ S₃, b' j ≫ Sigma.ι (fun j ↦ (T j).obj₂) j) (by
    rw [sub_comp, hg, sum_comp, sub_eq_zero]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    simp [b', dite_eq_left hj, hb j hj, coproductTriangle])
  obtain ⟨S₁, d, hd⟩ := h₁ a
  let d' (j : J) : s ⟶ (T j).obj₂ := if j ∈ S₁ then d j ≫ (T j).mor₁ else 0
  refine ⟨S₁ ∪ S₃, fun j ↦ b' j + d' j, ?_⟩
  have e₃ : ∑ j ∈ S₁ ∪ S₃, b' j ≫ Sigma.ι (fun j ↦ (T j).obj₂) j =
      ∑ j ∈ S₃, b' j ≫ Sigma.ι (fun j ↦ (T j).obj₂) j :=
    (Finset.sum_subset Finset.subset_union_right fun j _ hj ↦ by simp [b', hj]).symm
  have e₁ : ∑ j ∈ S₁ ∪ S₃, d' j ≫ Sigma.ι (fun j ↦ (T j).obj₂) j =
      a ≫ (coproductTriangle T).mor₁ := by
    rw [hd, sum_comp, ← Finset.sum_subset Finset.subset_union_left fun j _ hj ↦ by
      simp [d', hj]]
    exact Finset.sum_congr rfl fun j hj ↦ by simp [d', hj, coproductTriangle]
  rw [sub_eq_iff_eq_add.1 ha]
  simp only [add_comp, Finset.sum_add_distrib, e₁, e₃]
  abel

end CompactFor

end CategoryTheory

namespace DerivedCategory

open TStructure (t)

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] {J : Type*} [HasColimitsOfShape (Discrete J) C]
  [HasExactColimitsOfShape (Discrete J) C] {P : ObjectProperty C} [P.ContainsZero]
  [P.IsClosedUnderIsomorphisms]

omit [HasExactColimitsOfShape (Discrete J) C] [P.ContainsZero] in
/-- If `Hom(s, -)` commutes with direct sums of objects `B[-a]` with `B` in `P`, then it
commutes with direct sums of objects with cohomology in `P` concentrated in degree `a`. -/
lemma compactFor_of_isGE_of_isLE_self {s : DerivedCategory C}
    (hsum : ∀ (n : ℤ) (B : J → C), (∀ j, P (B j)) →
      CompactFor s fun j ↦ (singleFunctor C n).obj (B j))
    (a : ℤ) (K : J → DerivedCategory C) (hK : ∀ j, homologyProperty P (K j))
    [∀ j, (K j).IsGE a] [∀ j, (K j).IsLE a] : CompactFor s K := by
  choose M e using fun j ↦ (K j).exists_iso_singleFunctor_obj_of_isGE_of_isLE a
  refine CompactFor.of_iso (fun j ↦ (e j).some) (hsum a M fun j ↦ ?_)
  exact P.prop_of_iso ((homologyFunctor C a).mapIso (e j).some ≪≫
    (singleFunctorCompHomologyFunctorIso C a).app (M j)) (hK j a)

omit [HasExactColimitsOfShape (Discrete J) C] in
/-- Blueprint `theorem-compactness-rational-coefficients`: if `Hom(s, -)` commutes with direct sums
of shifted objects of `P`, it commutes with direct sums of families of objects with cohomology in
`P` concentrated in a common interval `[a, a + d]`, by induction on `d`, using the truncation
triangles and the five lemma (`CategoryTheory.CompactFor.of_distTriang`). -/
lemma compactFor_of_isGE_of_isLE {s : DerivedCategory C}
    (hsum : ∀ (n : ℤ) (B : J → C), (∀ j, P (B j)) →
      CompactFor s fun j ↦ (singleFunctor C n).obj (B j)) (d : ℕ) :
    ∀ (a : ℤ) (K : J → DerivedCategory C) (_ : ∀ j, homologyProperty P (K j))
      [∀ j, (K j).IsGE a] [∀ j, (K j).IsLE (a + d)], CompactFor s K := by
  induction d with
  | zero =>
    intro a K hK _ _
    have (j : J) : (K j).IsLE a := t.isLE_of_le (K j) (a + (0 : ℕ)) a (by simp)
    exact compactFor_of_isGE_of_isLE_self hsum a K hK
  | succ d ih =>
    intro a K hK _ _
    let b : ℤ := a + (d + 1 : ℕ)
    let T (j : J) := (t.triangleLTGE b).obj (K j)
    have h₁ : CompactFor s fun j ↦ (T j).obj₁ := by
      have (j : J) : (T j).obj₁.IsLE (b - 1) := inferInstanceAs (t.IsLE (T j).obj₁ (b - 1))
      have (j : J) : (T j).obj₁.IsLE (a + d) := t.isLE_of_le _ (b - 1) _ (by
        push_cast [b]
        lia)
      have (j : J) : (T j).obj₁.IsGE a :=
        inferInstanceAs (t.IsGE ((t.truncLT b).obj (K j)) a)
      exact ih a _ fun j ↦ (homologyProperty P).prop_of_iso
        ((t.truncLEIsoTruncLT (b - 1) b (by lia)).app (K j))
        (homologyProperty_truncLE (hK j) (b - 1))
    have h₃ : CompactFor s fun j ↦ (T j).obj₃ := by
      have (j : J) : (T j).obj₃.IsGE b := inferInstanceAs (t.IsGE (T j).obj₃ b)
      have (j : J) : t.IsLE (K j) b := ‹∀ j, (K j).IsLE (a + ((d + 1 : ℕ) : ℤ))› j
      have (j : J) : (T j).obj₃.IsLE b :=
        inferInstanceAs (t.IsLE ((t.truncGE b).obj (K j)) b)
      exact compactFor_of_isGE_of_isLE_self hsum b _ fun j ↦ homologyProperty_truncGE (hK j) b
    exact CompactFor.of_distTriang T (fun j ↦ t.triangleLTGE_distinguished b (K j)) h₁ h₃

omit [Abelian.HasKInjectiveResolutions C] [HasColimitsOfShape (Discrete J) C]
  [HasExactColimitsOfShape (Discrete J) C] [P.ContainsZero] in
/-- If `Hom(s, B[-n]) = 0` for `B` in `P` and `n ≤ N`, then `Hom(s, L) = 0` for every `L` with
cohomology in `P` concentrated in a degree `a ≤ N`. -/
lemma eq_zero_of_isGE_of_isLE_self {s : DerivedCategory C} (N : ℤ)
    (hvan : ∀ B, P B → ∀ n ≤ N, ∀ f : s ⟶ (singleFunctor C n).obj B, f = 0)
    (a : ℤ) (L : DerivedCategory C) (hL : homologyProperty P L) [L.IsGE a] [L.IsLE a]
    (haN : a ≤ N) (f : s ⟶ L) : f = 0 := by
  obtain ⟨M, ⟨e⟩⟩ := L.exists_iso_singleFunctor_obj_of_isGE_of_isLE a
  have hM : P M := P.prop_of_iso ((homologyFunctor C a).mapIso e ≪≫
    (singleFunctorCompHomologyFunctorIso C a).app M) (hL a)
  rw [← cancel_mono e.hom, zero_comp]
  exact hvan M hM a haN _

omit [Abelian.HasKInjectiveResolutions C] [HasColimitsOfShape (Discrete J) C]
  [HasExactColimitsOfShape (Discrete J) C] in
/-- Blueprint `lemma-reduction-finitely-many-degrees`: if `Hom(s, B[-n]) = 0` for `B` in `P` and
`n ≤ N`, then `Hom(s, L) = 0` for every bounded `L` with cohomology in `P` in degrees `≤ N`. -/
lemma eq_zero_of_isGE_of_isLE {s : DerivedCategory C} (N : ℤ)
    (hvan : ∀ B, P B → ∀ n ≤ N, ∀ f : s ⟶ (singleFunctor C n).obj B, f = 0) (d : ℕ) :
    ∀ (a : ℤ) (L : DerivedCategory C) (_ : homologyProperty P L) [L.IsGE a] [L.IsLE (a + d)],
      a + d ≤ N → ∀ f : s ⟶ L, f = 0 := by
  induction d with
  | zero =>
    intro a L hL _ _ haN f
    have : L.IsLE a := t.isLE_of_le L (a + (0 : ℕ)) a (by simp)
    exact eq_zero_of_isGE_of_isLE_self N hvan a L hL (by simpa using haN) f
  | succ d ih =>
    intro a L hL _ _ haN f
    let b : ℤ := a + (d + 1 : ℕ)
    let T := (t.triangleLTGE b).obj L
    have hT : T ∈ distTriang _ := t.triangleLTGE_distinguished b L
    have : T.obj₁.IsLE (b - 1) := inferInstanceAs (t.IsLE T.obj₁ (b - 1))
    have : T.obj₁.IsLE (a + d) := t.isLE_of_le _ (b - 1) _ (by
      push_cast [b]
      lia)
    have : T.obj₁.IsGE a := inferInstanceAs (t.IsGE ((t.truncLT b).obj L) a)
    have : T.obj₃.IsGE b := inferInstanceAs (t.IsGE T.obj₃ b)
    have : t.IsLE L b := ‹L.IsLE (a + ((d + 1 : ℕ) : ℤ))›
    have : T.obj₃.IsLE b := inferInstanceAs (t.IsLE ((t.truncGE b).obj L) b)
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ hT f
      (eq_zero_of_isGE_of_isLE_self N hvan b T.obj₃ (homologyProperty_truncGE hL b) haN _)
    rw [hg, ih a T.obj₁ ((homologyProperty P).prop_of_iso
      ((t.truncLEIsoTruncLT (b - 1) b (by lia)).app L) (homologyProperty_truncLE hL (b - 1)))
      (by push_cast at haN ⊢; lia) g, zero_comp]

section LeftComplete

variable [HasLimitsOfShape (Discrete ℕ) C] [HasExactLimitsOfShape (Discrete ℕ) C]

omit [HasColimitsOfShape (Discrete J) C] [HasExactColimitsOfShape (Discrete J) C] in
/-- Blueprint `lemma-reduction-finitely-many-degrees`: if `Hom(s, B[-n]) = 0` for `B` in `P` and
`n ≤ N`, then `Hom(s, L) = 0` for every `L` with cohomology in `P` in degrees `≤ N - 1`, with no
lower bound: `L` is the homotopy limit of its truncations `τ_{≥ -n} L` (left completeness), and the
maps from `s` and `s⟦1⟧` to these vanish by the bounded case. -/
lemma eq_zero_of_isLE {s : DerivedCategory C} (N : ℤ)
    (hvan : ∀ B, P B → ∀ n ≤ N, ∀ f : s ⟶ (singleFunctor C n).obj B, f = 0)
    (L : DerivedCategory C) (hL : homologyProperty P L) [L.IsLE (N - 1)] (f : s ⟶ L) :
    f = 0 := by
  have hb (n : ℕ) (W : DerivedCategory C) (hW : homologyProperty P W)
      [W.IsGE (-(n : ℤ) - 1)] [W.IsLE N] (g : s ⟶ W) : g = 0 := by
    have : W.IsGE (min (-(n : ℤ) - 1) N) := t.isGE_of_ge W _ (-(n : ℤ) - 1) (min_le_left _ _)
    have : W.IsLE (min (-(n : ℤ) - 1) N + ((N - min (-(n : ℤ) - 1) N).toNat : ℕ)) :=
      t.isLE_of_le W N _ (by lia)
    exact eq_zero_of_isGE_of_isLE N hvan (N - min (-(n : ℤ) - 1) N).toNat
      (min (-(n : ℤ) - 1) N) W hW (by lia) g
  refine (isHomotopyLimit_truncGECone L).hom_ext_zero (fun n g ↦ ?_) (fun n g ↦ ?_) f
  · have : ((t.truncGE (-(n : ℤ))).obj L).IsGE (-(n : ℤ) - 1) :=
      t.isGE_of_ge _ (-(n : ℤ) - 1) (-(n : ℤ)) (by lia)
    have : ((t.truncGE (-(n : ℤ))).obj L).IsLE N := t.isLE_of_le _ (N - 1) N (by lia)
    exact hb n _ (homologyProperty_truncGE hL _) g
  · let X := (t.truncGE (-(n : ℤ))).obj L
    have : X.IsGE (-(n : ℤ)) := inferInstanceAs (t.IsGE ((t.truncGE (-(n : ℤ))).obj L) _)
    have : X.IsLE (N - 1) := inferInstanceAs (t.IsLE ((t.truncGE (-(n : ℤ))).obj L) _)
    have : (X⟦(-1 : ℤ)⟧).IsGE (-(n : ℤ) + 1) := t.isGE_shift X (-(n : ℤ)) (-1) _ (by lia)
    have : (X⟦(-1 : ℤ)⟧).IsGE (-(n : ℤ) - 1) := t.isGE_of_ge _ _ (-(n : ℤ) + 1) (by lia)
    have : (X⟦(-1 : ℤ)⟧).IsLE N := t.isLE_shift X (N - 1) (-1) N (by lia)
    have h := hb n _ ((homologyProperty P).le_shift (-1) X (homologyProperty_truncGE hL _))
      ((shiftFunctorCompIsoId (DerivedCategory C) (1 : ℤ) (-1) (by lia)).inv.app s ≫
        g⟦(-1 : ℤ)⟧')
    rw [← cancel_epi
      ((shiftFunctorCompIsoId (DerivedCategory C) (1 : ℤ) (-1) (by lia)).hom.app s),
      Iso.hom_inv_id_app_assoc, comp_zero] at h
    exact (shiftFunctor (DerivedCategory C) (-1 : ℤ)).map_eq_zero_iff.mp h

/-- Blueprints `lemma-reduction-finitely-many-degrees` and
`theorem-compactness-rational-coefficients`, abstract form: let `s` be bounded above, such that
`Hom(s, B[-n]) = 0` for `B` in `P` and `n ≤ N`, and `Hom(s, -[-n])` commutes with direct sums of
objects of `P`. Then `Hom(s, -)` commutes with direct sums of objects with cohomology in `P`.
Morphisms out of `s` only see the truncations `τ_{≥ N - 1} τ_{≤ m}`, on which the bounded case
applies (`DerivedCategory.compactFor_of_isGE_of_isLE`). -/
theorem compactFor_of_homologyProperty [P.IsClosedUnderColimitsOfShape (Discrete J)]
    {s : DerivedCategory C} (b N : ℤ) [s.IsLE b]
    (hvan : ∀ B, P B → ∀ n ≤ N, ∀ f : s ⟶ (singleFunctor C n).obj B, f = 0)
    (hsum : ∀ (n : ℤ) (B : J → C), (∀ j, P (B j)) →
      CompactFor s fun j ↦ (singleFunctor C n).obj (B j))
    (Y : J → DerivedCategory C) (hY : ∀ j, homologyProperty P (Y j)) : CompactFor s Y := by
  let c := N - 1
  let m := max b c
  let A (j : J) := (t.truncLE m).obj (Y j)
  have hA (j : J) : homologyProperty P (A j) := homologyProperty_truncLE (hY j) m
  -- objects in degrees `< c` receive no morphisms from `s` or `s⟦-1⟧`
  have hN' (W : DerivedCategory C) (hW : homologyProperty P W) (hW' : W.IsLE (c - 1)) :
      (∀ f : s ⟶ W, f = 0) ∧ ∀ f : s ⟶ W⟦(1 : ℤ)⟧, f = 0 := by
    have : W.IsLE (N - 1) := t.isLE_of_le W (c - 1) (N - 1) (by lia)
    have : (W⟦(1 : ℤ)⟧).IsLE (N - 1) := by
      have := t.isLE_shift W (c - 1) 1 (c - 2) (by lia)
      exact t.isLE_of_le _ (c - 2) (N - 1) (by lia)
    exact ⟨eq_zero_of_isLE N hvan W hW,
      eq_zero_of_isLE N hvan _ ((homologyProperty P).le_shift 1 W hW)⟩
  have hLT (j : J) : homologyProperty P ((t.truncLT c).obj (A j)) :=
    (homologyProperty P).prop_of_iso ((t.truncLEIsoTruncLT (c - 1) c (by lia)).app _)
      (homologyProperty_truncLE (hA j) (c - 1))
  -- the bounded truncations
  have hT : CompactFor s fun j ↦ (t.truncGE c).obj (A j) := by
    have (j : J) : ((t.truncGE c).obj (A j)).IsLE (c + ((m - c).toNat : ℕ)) :=
      t.isLE_of_le _ m _ (by lia)
    exact compactFor_of_isGE_of_isLE hsum (m - c).toNat c _
      fun j ↦ homologyProperty_truncGE (hA j) c
  have hcA : CompactFor s A := by
    refine CompactFor.of_bijective (fun j ↦ (t.truncGEπ c).app (A j)) hT (fun j ↦ ?_) ?_
    · have h := hN' _ (hLT j) inferInstance
      exact (bijective_comp_mor₂ _ (t.triangleLTGE_distinguished c (A j)) s h.1 h.2).2
    · have h := hN' _ (homologyProperty_sigma P _ hLT)
        (isLE_sigma _ _ fun j ↦ inferInstance)
      exact (bijective_comp_mor₂ _ (coproductTriangle_distinguished _
        fun j ↦ t.triangleLTGE_distinguished c (A j)) s h.1 h.2).1
  refine CompactFor.of_surjective (fun j ↦ (t.truncLEι m).app (Y j)) hcA ?_
  have hGT : (∐ fun j ↦ (t.truncGT m).obj (Y j)).IsGE (m + 1) :=
    isGE_sigma _ _ fun j ↦ inferInstance
  have hGT' : ((∐ fun j ↦ (t.truncGT m).obj (Y j))⟦(-1 : ℤ)⟧).IsGE (m + 2) :=
    t.isGE_shift _ (m + 1) (-1) (m + 2) (by lia)
  have : s.IsLE m := t.isLE_of_le s b m (le_max_left _ _)
  exact (bijective_comp_mor₁ _ (coproductTriangle_distinguished _
    fun j ↦ t.triangleLEGT_distinguished m (Y j)) s
    (fun f ↦ t.zero_of_isLE_of_isGE f m (m + 1) (by lia) this hGT)
    (fun f ↦ t.zero_of_isLE_of_isGE f m (m + 2) (by lia) this hGT')).2

end LeftComplete

section Continuity

/-! ### Continuity of `Hom(s, -[n])` on objects of `C` -/

omit [HasColimitsOfShape (Discrete J) C] [HasExactColimitsOfShape (Discrete J) C] in
/-- The functor `C ⥤ D(C)` placing an object in degree `n` preserves coproducts. -/
instance preservesColimitsOfShape_singleFunctor (n : ℤ) (J : Type*)
    [HasColimitsOfShape (Discrete J) C] :
    PreservesColimitsOfShape (Discrete J) (singleFunctor C n) :=
  have : PreservesColimitsOfShape (Discrete J) (CochainComplex.singleFunctor C n) :=
    inferInstanceAs
      (PreservesColimitsOfShape (Discrete J) (HomologicalComplex.single C (ComplexShape.up ℤ) n))
  preservesColimitsOfShape_of_natIso (singleFunctorIsoCompQ C n).symm

/-- A morphism `s ⟶ B[n]` out of `s` *factors through filtered colimits* (blueprint
`lemma-continuity-ext-out-constructible-complex--1`, surjectivity part, for targets in degree `0`)
if for every filtered colimit `B = colim Bᵢ` of objects of `C` (indexed by a category in `Type w`),
every morphism `s ⟶ B[n]` factors through some `Bᵢ[n]`. -/
def HomFactorsThroughFilteredColimits (s : DerivedCategory C) : Prop :=
  ∀ (I : Type w) [SmallCategory I] [IsFiltered I] (F : I ⥤ C) (c : Cocone F)
    (_ : IsColimit c) (n : ℤ) (f : s ⟶ (singleFunctor C n).obj c.pt),
    ∃ (i : I) (g : s ⟶ (singleFunctor C n).obj (F.obj i)),
      f = g ≫ (singleFunctor C n).map (c.ι.app i)

variable (P) in
omit [Abelian.HasKInjectiveResolutions C] [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [HasColimitsOfShape (Discrete J) C] [HasExactColimitsOfShape (Discrete J) C] in
/-- Blueprint `corollary-ind-heart-b--1`: if morphisms out of `s` factor through filtered
colimits, and `Hom(s, B[n])` vanishes for `B` in `P` and `n ≤ N`, it vanishes for `B` a filtered
colimit of objects of `P` and `n ≤ N`. -/
lemma eq_zero_of_ind {s : DerivedCategory C} (hcont : HomFactorsThroughFilteredColimits.{w} s)
    (N : ℤ) (hvan : ∀ B, P B → ∀ n ≤ N, ∀ f : s ⟶ (singleFunctor C n).obj B, f = 0)
    (B : C) (hB : ObjectProperty.ind.{w} P B) (n : ℤ) (hn : n ≤ N)
    (f : s ⟶ (singleFunctor C n).obj B) : f = 0 := by
  obtain ⟨I, _, _, pres, hpres⟩ := hB
  obtain ⟨i, g, rfl⟩ := hcont I pres.diag (Cocone.mk B pres.ι) pres.isColimit n f
  rw [hvan _ (hpres i) n hn g, zero_comp]

attribute [local instance] Abelian.hasFiniteBiproducts in
omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [HasColimitsOfShape (Discrete J) C]
  [HasExactColimitsOfShape (Discrete J) C] in
/-- Blueprint `corollary-ind-heart-b--2`: if morphisms out of `s` factor through filtered colimits,
then `Hom(s, -[n])` commutes with direct sums of objects of `C`: a direct sum is the filtered
colimit of its finite subsums. -/
lemma compactFor_singleFunctor_of_homFactorsThroughFilteredColimits {s : DerivedCategory C}
    {J : Type w} [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Finset (Discrete J)) C]
    (hcont : HomFactorsThroughFilteredColimits.{w} s) (n : ℤ) (B : J → C) :
    CompactFor s fun j ↦ (singleFunctor C n).obj (B j) := by
  classical
  intro f
  let G := singleFunctor C n
  let φ := sigmaComparison G B
  obtain ⟨S, g, hg⟩ := hcont (Finset (Discrete J)) _ _
    (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone B) n (f ≫ φ)
  let B' (x : S) : C := B x.1.as
  let h (x : S) : s ⟶ G.obj (B x.1.as) := g ≫ G.map ((biproduct.isoCoproduct B').inv ≫
    biproduct.π B' x)
  have hψ : (CoproductsFromFiniteFiltered.finiteSubcoproductsCocone B).ι.app S =
      ∑ x, (biproduct.isoCoproduct B').inv ≫ biproduct.π B' x ≫ Sigma.ι B x.1.as := by
    refine (id_comp _).symm.trans
      ((congrArg (· ≫ _) (sum_isoCoproduct_inv_π_ι B').symm).trans ?_)
    rw [sum_comp]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp [B']
  have hf : f ≫ φ = ∑ x, h x ≫ G.map (Sigma.ι B x.1.as) := by
    rw [hg, hψ, G.map_sum, comp_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp [h]
  refine ⟨S.image Discrete.as,
    fun j ↦ if hj : (⟨j⟩ : Discrete J) ∈ S then h ⟨⟨j⟩, hj⟩ else 0, ?_⟩
  rw [← cancel_mono φ, hf, Finset.sum_image fun x _ y _ hxy ↦ Discrete.ext hxy, sum_comp,
    ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have hx : (⟨(x : Discrete J).as⟩ : Discrete J) ∈ S := x.2
  simp only [dite_eq_left hx, assoc, φ]
  exact congrArg (h x ≫ ·) (ι_comp_sigmaComparison G B _).symm

end Continuity

end DerivedCategory
