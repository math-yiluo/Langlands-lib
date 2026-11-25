/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.DirectSum.Basic

/-!
# Hom into a sequence-relative telescope

Source: Stacks Project, Derived Categories, Tags 0CRK, 094A and 093W; the
sequence-relative version of their exact-sequence argument
(blueprint: lem-weil-pbc-sequence-relative-hom-telescope).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite DirectSum

namespace CategoryTheory

private theorem sequential_difference_injective
    (A : ℕ → Type v) [∀ n, AddCommGroup (A n)]
    (t : ∀ n, A n →+ A (n + 1))
    (σ : (⨁ n, A n) →+ (⨁ n, A n))
    (hσ : ∀ n x, σ (DirectSum.of A n x) = DirectSum.of A (n + 1) (t n x)) :
    Function.Injective (AddMonoidHom.id (⨁ n, A n) - σ) := by
  have hzero (x : ⨁ n, A n) : σ x 0 = 0 := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n x => rw [hσ]; exact DirectSum.of_eq_of_ne _ _ _ (Nat.succ_ne_zero n).symm
    | add x y hx hy => simp [hx, hy]
  have hsucc (x : ⨁ n, A n) (n : ℕ) : σ x (n + 1) = t n (x n) := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of m x =>
      rw [hσ]
      by_cases h : m = n
      · subst m; simp
      · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm (Nat.succ_ne_succ_iff.mpr h)),
          DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), map_zero]
    | add x y hx hy => simp [hx, hy]
  apply (injective_iff_map_eq_zero _).2
  intro x hx
  have heq : x = σ x := sub_eq_zero.mp hx
  apply DirectSum.ext
  intro n
  change x n = 0
  induction n with
  | zero => rw [heq, hzero]
  | succ n ih => rw [congrArg (fun z : ⨁ n, A n ↦ z (n + 1)) heq, hsucc, ih, map_zero]

/-- Hom into a chosen telescope is the sequential colimit of the Hom groups if the
coproduct comparisons for this sequence and its shift by one are bijective.
Source: Stacks Project, Derived Categories, Tags 0CRK, 094A and 093W
(blueprint: lem-weil-pbc-sequence-relative-hom-telescope).

The colimit is in `AddCommGrpCat`; its transitions are postcomposition with the maps
of `X`. The equations on every stage uniquely specify the canonical group homomorphism.
Only the supplied coproduct and the two displayed comparisons are assumed.

Proof:
1. Put `A n = Hom(K, X n)` and `A' n = Hom(K, X n[1])`. The two assumed
   bijective additive comparison maps identify their direct sums with `Hom(K, B)`
   and `Hom(K, B[1])`. On each summand, postcomposition by `1 - s` corresponds
   to identity minus the forward transition shift. The same holds after shifting,
   since shift is additive (`def-weil-triangulated-category`). These identities
   extend to finite sums.
2. Identity minus forward shift on the shifted direct sum is injective: its
   zeroth coordinate gives `g 0 = 0`, and coordinate `n + 1` gives
   `g (n + 1) = u n[1] (g n)`. Induction makes every coordinate zero.
   Transport through the shifted comparison to obtain injectivity of `(1 - s)[1]_*`.
3. Apply `lem-weil-pbc-hom-into-triangle-exact` to the triangle and its rotations.
   Consecutive composites vanish, so injectivity in step 2 forces every map into
   `H` to have zero composite with `q`. Exactness of the once-rotated triangle
   makes postcomposition by `p` surjective. Exactness of the original triangle
   identifies its kernel with the image of postcomposition by `1 - s`.
   Thus the induced map from the unshifted direct sum is surjective with kernel
   the image of identity minus forward shift.
4. The quotient of that sum by this image is the sequential colimit of the
   groups `A n` (`def-weil-pbc-category-colimit`): its summand maps are compatible.
   Every compatible family of group homomorphisms extends to the sum, kills the
   image, and factors uniquely through the quotient. Successor compatibility
   extends to all transitions by induction.
5. Step 3 induces an injective and surjective homomorphism from this quotient to
   `Hom(K, H)`. Its value on a stage element is `f ≫ iota n ≫ p`.
   The colimit universal property identifies it with precisely the stated map.
   No coproduct comparison for any other family is used. -/
theorem sequence_relative_hom_telescope
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (K : C) (X : ℕ ⥤ C) (B : C) (iota : ∀ n : ℕ, X.obj n ⟶ B)
    (hB : IsColimit (Cofan.mk B iota))
    (s : B ⟶ B)
    (hs : ∀ n : ℕ, iota n ≫ s = X.map (homOfLE (Nat.le_succ n)) ≫ iota (n + 1))
    (H : C) (p : B ⟶ H) (q : H ⟶ B⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (𝟙 B - s) p q ∈ distTriang C)
    (hcomp : Function.Bijective
      (DirectSum.toAddMonoid (fun n : ℕ ↦ Preadditive.rightComp K (iota n)) :
        (⨁ n : ℕ, (K ⟶ X.obj n)) →+ (K ⟶ B)))
    (hcompShift : Function.Bijective
      (DirectSum.toAddMonoid (fun n : ℕ ↦
        Preadditive.rightComp K ((iota n)⟦(1 : ℤ)⟧')) :
        (⨁ n : ℕ, (K ⟶ (X.obj n)⟦(1 : ℤ)⟧)) →+ (K ⟶ B⟦(1 : ℤ)⟧))) :
    ∃ phi : colimit (X ⋙ preadditiveCoyoneda.obj (op K)) ⟶ AddCommGrpCat.of (K ⟶ H),
      (∀ (n : ℕ) (f : K ⟶ X.obj n),
        phi (colimit.ι (X ⋙ preadditiveCoyoneda.obj (op K)) n f) = f ≫ iota n ≫ p) ∧
      Function.Bijective phi := by
  classical
  have _ := hB
  let A : ℕ → Type v := fun n ↦ K ⟶ X.obj n
  let A' : ℕ → Type v := fun n ↦ K ⟶ (X.obj n)⟦(1 : ℤ)⟧
  let β : (⨁ n, A n) →+ (K ⟶ B) :=
    DirectSum.toAddMonoid (fun n ↦ Preadditive.rightComp K (iota n))
  let β' : (⨁ n, A' n) →+ (K ⟶ B⟦(1 : ℤ)⟧) :=
    DirectSum.toAddMonoid (fun n ↦ Preadditive.rightComp K ((iota n)⟦(1 : ℤ)⟧'))
  let t' : ∀ n, A' n →+ A' (n + 1) := fun n ↦
    Preadditive.rightComp K ((X.map (homOfLE (Nat.le_succ n)))⟦(1 : ℤ)⟧')
  let σ' : (⨁ n, A' n) →+ (⨁ n, A' n) :=
    DirectSum.toAddMonoid (fun n ↦ (DirectSum.of A' (n + 1)).comp (t' n))
  have hσ' (n : ℕ) (f : A' n) :
      σ' (DirectSum.of A' n f) = DirectSum.of A' (n + 1) (t' n f) := by
    simp [σ']
  have hcomm : (Preadditive.rightComp K ((𝟙 B - s)⟦(1 : ℤ)⟧')).comp β' =
      β'.comp (AddMonoidHom.id _ - σ') := by
    apply DirectSum.addHom_ext
    intro n f
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply,
      AddMonoidHom.id_apply, hσ', map_sub]
    simp only [β', DirectSum.toAddMonoid_of]
    change (f ≫ (iota n)⟦(1 : ℤ)⟧') ≫ (𝟙 B - s)⟦(1 : ℤ)⟧' =
      f ≫ (iota n)⟦(1 : ℤ)⟧' -
        (f ≫ (X.map (homOfLE (Nat.le_succ n)))⟦(1 : ℤ)⟧') ≫
          (iota (n + 1))⟦(1 : ℤ)⟧'
    simp only [Functor.map_sub, Functor.map_id, Preadditive.comp_sub, Category.comp_id]
    rw [Category.assoc, ← Functor.map_comp, hs, Functor.map_comp, Category.assoc]
  have hinj : Function.Injective (Preadditive.rightComp K ((𝟙 B - s)⟦(1 : ℤ)⟧')) := by
    intro f g hfg
    obtain ⟨x, rfl⟩ := hcompShift.2 f
    obtain ⟨y, rfl⟩ := hcompShift.2 g
    apply congrArg β'
    apply sequential_difference_injective A' t' σ' hσ'
    apply hcompShift.1
    exact (DFunLike.congr_fun hcomm x).symm.trans
      (hfg.trans (DFunLike.congr_fun hcomm y))
  have hp : Function.Surjective (Preadditive.rightComp K p) := by
    intro f
    have hf : f ≫ q = 0 := by
      apply hinj
      change (f ≫ q) ≫ (𝟙 B - s)⟦(1 : ℤ)⟧' = 0 ≫ _
      have hzero : q ≫ (𝟙 B - s)⟦(1 : ℤ)⟧' = 0 :=
        comp_distTriang_mor_zero₃₁ _ hT
      rw [Category.assoc, hzero, comp_zero, zero_comp]
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ _ hT f hf
    exact ⟨g, hg.symm⟩
  have hrel (n : ℕ) :
      X.map (homOfLE (Nat.le_succ n)) ≫ iota (n + 1) ≫ p = iota n ≫ p := by
    have hz := congrArg (fun a ↦ iota n ≫ a) (comp_distTriang_mor_zero₁₂ _ hT)
    change iota n ≫ ((𝟙 B - s) ≫ p) = iota n ≫ 0 at hz
    rw [← Category.assoc, Preadditive.comp_sub, Category.comp_id,
      Preadditive.sub_comp, comp_zero, hs] at hz
    simpa only [Category.assoc] using (sub_eq_zero.mp hz).symm
  let F := X ⋙ preadditiveCoyoneda.obj (op K)
  have hcompatible (n m : ℕ) (h : n ≤ m) :
      X.map (homOfLE h) ≫ iota m ≫ p = iota n ≫ p := by
    induction h using Nat.leRec with
    | refl => simp
    | @le_succ_of_le m h ih =>
      change X.map (homOfLE h ≫ homOfLE (Nat.le_succ m)) ≫ _ = _
      rw [X.map_comp, Category.assoc, hrel, ih]
  let c : Cocone F :=
    { pt := AddCommGrpCat.of (K ⟶ H)
      ι :=
        { app := fun n ↦ AddCommGrpCat.ofHom (Preadditive.rightComp K (iota n ≫ p))
          naturality := by
            intro n m a
            ext f
            change (f ≫ X.map a) ≫ (iota m ≫ p) = f ≫ (iota n ≫ p)
            rw [Category.assoc, ← homOfLE_leOfHom a, hcompatible] } }
  let phi := colimit.desc F c
  have hphi (n : ℕ) (f : A n) :
      phi (colimit.ι F n f) = f ≫ iota n ≫ p := by
    change (colimit.ι F n ≫ colimit.desc F c) f = _
    rw [colimit.ι_desc]
    rfl
  let e : (⨁ n, A n) ≃+ (K ⟶ B) := AddEquiv.ofBijective β hcomp
  let l : (⨁ n, A n) →+ ↥(colimit F) :=
    DirectSum.toAddMonoid (fun n ↦ (colimit.ι F n).hom)
  let g : (K ⟶ B) →+ ↥(colimit F) := l.comp e.symm.toAddMonoidHom
  have hgbeta (x : ⨁ n, A n) : g (β x) = l x := by
    change l (e.symm (e x)) = l x
    rw [e.symm_apply_apply]
  have hgon (n : ℕ) (f : A n) : g (f ≫ iota n) = colimit.ι F n f := by
    have hh := hgbeta (DirectSum.of A n f)
    simp only [β, l, DirectSum.toAddMonoid_of] at hh
    change g (f ≫ iota n) = colimit.ι F n f at hh
    exact hh
  have hz : (g.comp (Preadditive.rightComp K (𝟙 B - s))).comp β = 0 := by
    apply DirectSum.addHom_ext
    intro n f
    change g ((β (DirectSum.of A n f)) ≫ (𝟙 B - s)) = 0
    simp only [β, DirectSum.toAddMonoid_of]
    change g ((f ≫ iota n) ≫ (𝟙 B - s)) = 0
    rw [Preadditive.comp_sub, Category.comp_id, Category.assoc, hs,
      ← Category.assoc, map_sub, hgon, hgon]
    apply sub_eq_zero.mpr
    exact (ConcreteCategory.congr_hom (colimit.w F (homOfLE (Nat.le_succ n))) f).symm
  have hgker : (Preadditive.rightComp K p).ker ≤ g.ker := by
    intro b hb
    obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ _ hT b hb
    obtain ⟨x, hx⟩ := hcomp.2 a
    rw [AddMonoidHom.mem_ker, ha, ← hx]
    exact DFunLike.congr_fun hz x
  let psi : (K ⟶ H) →+ ↥(colimit F) :=
    (Preadditive.rightComp K p).liftOfSurjective hp ⟨g, hgker⟩
  have hpsi (b : K ⟶ B) : psi (b ≫ p) = g b := by
    exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ b
  have hleft : (phi ≫ AddCommGrpCat.ofHom psi) = 𝟙 (colimit F) := by
    apply colimit.hom_ext
    intro n
    ext f
    change psi (phi (colimit.ι F n f)) = colimit.ι F n f
    rw [hphi, ← Category.assoc, hpsi, hgon]
  have hright (b : K ⟶ B) : phi (g b) = b ≫ p := by
    obtain ⟨x, rfl⟩ := hcomp.2 b
    rw [hgbeta]
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n f =>
      change phi (l (DirectSum.of A n f)) = β (DirectSum.of A n f) ≫ p
      simp only [l, β, DirectSum.toAddMonoid_of]
      change phi (colimit.ι F n f) = (f ≫ iota n) ≫ p
      rw [Category.assoc]
      exact hphi n f
    | add x y hx hy => simp [map_add, Preadditive.add_comp, hx, hy]
  refine ⟨phi, hphi, ?_, ?_⟩
  · intro x y hxy
    have hx := ConcreteCategory.congr_hom hleft x
    have hy := ConcreteCategory.congr_hom hleft y
    change psi (phi x) = x at hx
    change psi (phi y) = y at hy
    rw [← hx, ← hy, hxy]
  · intro f
    obtain ⟨b, rfl⟩ := hp f
    exact ⟨g b, hright b⟩

end CategoryTheory
