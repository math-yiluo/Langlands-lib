/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Data.Finset.Sort
public import WeilConjectures.AlgebraicGeometry.ExtendedLocalizationCech

/-! # Extended localization Čech complexes on ringed sites

Source: Stacks Project, Tags 0913 and 099H
(blueprint: def-weil-pbc-extended-localization-cech).

The construction uses the explicit cochain Koszul colimit of Tag 0913. Its degree-q
summands are indexed by subsets of cardinality q, including the empty subset in degree
zero. The transition on the subset I multiplies by the product of the f_i in I.
Thus its termwise colimit is the sheafification of the localization at that product;
the differential is the alternating localization differential. Finite coproducts are
finite products. The empty-subset transition is the identity, identifying degree zero
canonically with the original ring sheaf. For an empty family only degree zero remains.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules
namespace LocalizationCech

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- Index set in degree q. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
def Indices (r : ℕ) (q : ℤ) := {s : Finset (Fin r) // (s.card : ℤ) = q}

/-- Insertion raises the degree by one. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech).
Proof: insertion of a new element raises the finite cardinality by one; cast to integers. -/
theorem insert_degree {r : ℕ} {q : ℤ} (s : Indices r q) (j : Fin r) (h : j ∉ s.val) :
    ((insert j s.val).card : ℤ) = q + 1 := by
  rw [Finset.card_insert_of_notMem h, Nat.cast_add, Nat.cast_one, s.property]

/-- Free term on the subsets of cardinality q. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def term (R : Sheaf J CommRingCat.{u}) (r : ℕ) (q : ℤ) :
    CategoryTheory.ringedSiteModules.{u} (rings R) :=
  ∐ fun _ : Indices r q ↦ unit (rings R)

private def value {R : Sheaf J CommRingCat.{u}}
    (f : (unit (rings R)).sections) (X : Cᵒᵖ) : R.obj.obj X := f.val X

private theorem scalar_apply (R : Sheaf J CommRingCat.{u})
    (f : (unit (rings R)).sections) (X : Cᵒᵖ) (a : R.obj.obj X) :
    (scalar R f).asHom.val.app X a = a * value f X := by
  rfl

private theorem scalar_pow_apply (R : Sheaf J CommRingCat.{u})
    (f : (unit (rings R)).sections) (k : ℕ) (X : Cᵒᵖ) (a : R.obj.obj X) :
    (scalar R f ^ k).asHom.val.app X a = a * value f X ^ k := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change (scalar R f).asHom.val.app X ((scalar R f ^ k).asHom.val.app X a) = _
    rw [scalar_apply, ih, pow_succ, mul_assoc]

/-- Cochain Koszul differential at the positive exponent n+1. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def differential (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) (q : ℤ) :
    term R r q ⟶ term R r (q + 1) := by
  classical
  exact Sigma.desc (fun s ↦ ∑ j : Fin r,
    if h : j ∉ s.val then
      (-1 : ℤ) ^ (s.val.filter (· < j)).card •
        (((scalar R (f j) ^ (n + 1)).asHom) ≫
          Sigma.ι (fun _ : Indices r (q + 1) ↦ unit (rings R))
            ⟨insert j s.val, insert_degree s j h⟩)
    else 0)

private theorem scalar_powers_comm (R : Sheaf J CommRingCat.{u})
    (f g : (unit (rings R)).sections) (k : ℕ) :
    ((scalar R f ^ k).asHom) ≫ ((scalar R g ^ k).asHom) =
      ((scalar R g ^ k).asHom) ≫ ((scalar R f ^ k).asHom) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (scalar R g ^ k).asHom.val.app X ((scalar R f ^ k).asHom.val.app X a) =
    (scalar R f ^ k).asHom.val.app X ((scalar R g ^ k).asHom.val.app X a)
  rw [scalar_pow_apply, scalar_pow_apply, scalar_pow_apply, scalar_pow_apply]
  ac_rfl

private theorem insertion_signs_cancel {r : ℕ} (s : Finset (Fin r))
    (j k : Fin r) (hj : j ∉ s) (hk : k ∉ s) (hjk : j ≠ k) :
    (-1 : ℤ) ^ (s.filter (· < j)).card *
        (-1 : ℤ) ^ ((insert j s).filter (· < k)).card +
      (-1 : ℤ) ^ (s.filter (· < k)).card *
        (-1 : ℤ) ^ ((insert k s).filter (· < j)).card = 0 := by
  classical
  rcases lt_or_gt_of_ne hjk with h | h
  · have hkj : ¬ k < j := not_lt_of_ge h.le
    have hm : j ∉ s.filter (· < k) := fun hm ↦ hj (Finset.mem_filter.mp hm).1
    simp only [Finset.filter_insert, h, hkj, ite_true, ite_false,
      Finset.card_insert_of_notMem hm, pow_succ]
    ring
  · have hkj : ¬ j < k := not_lt_of_ge h.le
    have hm : k ∉ s.filter (· < j) := fun hm ↦ hk (Finset.mem_filter.mp hm).1
    simp only [Finset.filter_insert, h, hkj, ite_true, ite_false,
      Finset.card_insert_of_notMem hm, pow_succ]
    ring

private def doubleIndex {r : ℕ} {q : ℤ} (s : Indices r q) (j k : Fin r)
    (hj : j ∉ s.val) (hk : k ∉ insert j s.val) : Indices r (q + 1 + 1) :=
  ⟨insert k (insert j s.val),
    insert_degree ⟨insert j s.val, insert_degree s j hj⟩ k hk⟩

private noncomputable def doubleTerm (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) (q : ℤ) (s : Indices r q)
    (j k : Fin r) : unit (rings R) ⟶ term R r (q + 1 + 1) := by
  classical
  exact if hj : j ∉ s.val then if hk : k ∉ insert j s.val then
    ((-1 : ℤ) ^ (s.val.filter (· < j)).card *
      (-1 : ℤ) ^ ((insert j s.val).filter (· < k)).card) •
      (((scalar R (f j) ^ (n + 1)).asHom) ≫ ((scalar R (f k) ^ (n + 1)).asHom) ≫
        Sigma.ι (fun _ : Indices r (q + 1 + 1) ↦ unit (rings R))
          (doubleIndex s j k hj hk))
    else 0 else 0

private theorem doubleTerm_cancel (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) (q : ℤ) (s : Indices r q)
    (j k : Fin r) : doubleTerm R r f n q s j k + doubleTerm R r f n q s k j = 0 := by
  classical
  by_cases hj : j ∈ s.val
  · simp [doubleTerm, hj]
  by_cases hk : k ∈ s.val
  · simp [doubleTerm, hk]
  by_cases he : j = k
  · subst k
    simp [doubleTerm]
  have hkj : k ∉ insert j s.val := by simp [Finset.mem_insert, Ne.symm he, hk]
  have hjk : j ∉ insert k s.val := by simp [Finset.mem_insert, he, hj]
  have hi : doubleIndex s j k hj hkj = doubleIndex s k j hk hjk := by
    apply Subtype.ext
    exact Finset.insert_comm k j s.val
  simp only [doubleTerm, dite_eq_left hj, dite_eq_left hk, dite_eq_left hkj, dite_eq_left hjk, hi]
  rw [← Category.assoc, scalar_powers_comm R (f j) (f k) (n + 1), Category.assoc,
    ← add_smul, insertion_signs_cancel s.val j k hj hk he, zero_smul]

/-- The Koszul differential squares to zero. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech).
Proof: on each free summand, pair the two orders of insertion of distinct indices.
The scalar endomorphisms commute because the coefficient ring is commutative, and
inserting the smaller index changes the sign of the other insertion. Repeated
indices contribute zero. Each pair therefore cancels. -/
theorem differential_sq (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) (q : ℤ) :
    differential R r f n q ≫ differential R r f n (q + 1) = 0 := by
  classical
  apply Sigma.hom_ext
  intro s
  have hsum : ∑ j, ∑ k, doubleTerm R r f n q s j k = 0 := by
    rw [← Fintype.sum_prod_type
      (fun p : Fin r × Fin r ↦ doubleTerm R r f n q s p.1 p.2)]
    apply Finset.sum_involution (fun p _ ↦ Prod.swap p)
    · intro p _
      exact doubleTerm_cancel R r f n q s p.1 p.2
    · intro p _ hp he
      have he' : p.1 = p.2 := congrArg Prod.snd he
      apply hp
      simp [he', doubleTerm]
    · intro p _
      exact Finset.mem_univ _
    · intro p _
      exact Prod.swap_swap p
  have hexpand : Sigma.ι (fun _ : Indices r q ↦ unit (rings R)) s ≫
      differential R r f n q ≫ differential R r f n (q + 1) =
        ∑ j, ∑ k, doubleTerm R r f n q s j k := by
    simp only [differential, Sigma.ι_comp_desc_assoc, Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · simp only [zero_comp]
      simp [doubleTerm, hj]
    · simp only [Preadditive.zsmul_comp, Category.assoc, Sigma.ι_comp_desc,
        Preadditive.comp_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs with hk
      · simp [doubleTerm, hj, hk]
      · simp only [Preadditive.comp_zsmul, smul_smul,
          doubleTerm, dite_eq_left hj, dite_eq_left hk]
        rfl
  rw [hexpand, hsum, comp_zero]

/-- The positive-power cochain Koszul complex. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def koszul (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) :
    CochainComplex (CategoryTheory.ringedSiteModules.{u} (rings R)) ℤ :=
  CochainComplex.of (term R r) (differential R r f n) (differential_sq R r f n)

/-- Multiplication by the subset product; ordering fixes an actual composite.
Source: Tag 0913 (blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def subsetScalar (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (s : Finset (Fin r)) :
    End (unit (rings R)) :=
  .of ((s.sort (· ≤ ·)).foldr (fun j a ↦ (scalar R (f j)).asHom ≫ a) (𝟙 _))

private theorem subsetScalar_apply (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (s : Finset (Fin r))
    (X : Cᵒᵖ) (a : R.obj.obj X) :
    (subsetScalar R r f s).asHom.val.app X a = a * ∏ j ∈ s, value (f j) X := by
  have hl : ∀ (l : List (Fin r)) (a : R.obj.obj X),
      (l.foldr (fun j b ↦ (scalar R (f j)).asHom ≫ b) (𝟙 _)).val.app X a =
        a * (l.map (fun j ↦ value (f j) X)).prod := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons j l ih =>
      intro a
      change (l.foldr (fun j b ↦ (scalar R (f j)).asHom ≫ b) (𝟙 _)).val.app X
        ((scalar R (f j)).asHom.val.app X a) = _
      rw [scalar_apply, ih]
      simp only [List.map_cons, List.prod_cons, mul_assoc]
  have hp : ((s.sort (· ≤ ·)).map (fun j ↦ value (f j) X)).prod =
      ∏ j ∈ s, value (f j) X := by
    change (Multiset.map (fun j ↦ value (f j) X) (s.sort (· ≤ ·))).prod = _
    rw [Finset.sort_eq]
    rfl
  exact (hl (s.sort (· ≤ ·)) a).trans (congrArg (a * ·) hp)

/-- Termwise transition from exponent n+1 to n+2. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def transitionTerm (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (q : ℤ) : term R r q ⟶ term R r q :=
  Sigma.desc (fun s ↦ (subsetScalar R r f s.val).asHom ≫
    Sigma.ι (fun _ : Indices r q ↦ unit (rings R)) s)

/-- The transitions commute with the differentials. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech).
Proof: on the summand I and the component I union {j}, both composites have
coefficient (-1)^a(j,I) times (product over I of f_i) times f_j^(n+2). -/
theorem transition_comm (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) (q : ℤ) :
    transitionTerm R r f q ≫ (koszul R r f (n + 1)).d q (q + 1) =
      (koszul R r f n).d q (q + 1) ≫ transitionTerm R r f (q + 1) := by
  classical
  have hc (s : Finset (Fin r)) (j : Fin r) (h : j ∉ s) :
      (subsetScalar R r f s).asHom ≫ ((scalar R (f j) ^ (n + 1 + 1)).asHom) =
        ((scalar R (f j) ^ (n + 1)).asHom) ≫ (subsetScalar R r f (insert j s)).asHom := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (scalar R (f j) ^ (n + 1 + 1)).asHom.val.app X
        ((subsetScalar R r f s).asHom.val.app X a) =
      (subsetScalar R r f (insert j s)).asHom.val.app X
        ((scalar R (f j) ^ (n + 1)).asHom.val.app X a)
    rw [scalar_pow_apply, subsetScalar_apply, subsetScalar_apply, scalar_pow_apply,
      Finset.prod_insert h, pow_succ]
    ac_rfl
  simp only [koszul, CochainComplex.of_d]
  change transitionTerm R r f q ≫ differential R r f (n + 1) q =
    differential R r f n q ≫ transitionTerm R r f (q + 1)
  apply Sigma.hom_ext
  intro s
  simp only [transitionTerm, differential, Category.assoc, Sigma.ι_comp_desc_assoc,
    Sigma.ι_comp_desc, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · simp only [comp_zero, zero_comp]
  · simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
      Category.assoc, Sigma.ι_comp_desc]
    rw [← Category.assoc, hc s.val j h, Category.assoc]

/-- Koszul transition as a chain map. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def transition (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) :
    koszul R r f n ⟶ koszul R r f (n + 1) :=
  CochainComplex.ofHom (transitionTerm R r f) (transition_comm R r f n)

/-- Sequential diagram of positive-power Koszul complexes. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def diagram (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) :
    ℕ ⥤ CochainComplex (CategoryTheory.ringedSiteModules.{u} (rings R)) ℤ :=
  Functor.ofSequence (transition R r f)

/-- The extended alternating localization Čech complex, constructed by the explicit
Koszul colimit. Source: Tag 0913 (blueprint: def-weil-pbc-extended-localization-cech).
On the subset I the cocone is a ↦ a/(product_I f_i)^(n+1). Every fraction occurs;
equality is eventual equality after multiplying by a power of that product.
The coefficient f_j^(n+1) becomes the localization map with sign (-1)^a(j,I).
Thus this is the extended alternating localization complex, including degree zero. -/
noncomputable def complex (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) :
    CochainComplex (CategoryTheory.ringedSiteModules.{u} (rings R)) ℤ :=
  colimit (diagram R r f)

/-- Coefficient maps carry global sections to global sections. Source: Tag 099H
(blueprint: def-weil-pbc-extended-localization-cech).
Proof: the naturality square of φ commutes with restriction; apply it to the section
and use the section's compatibility with restriction. -/
theorem mapSection_naturality {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (s : (unit (rings R)).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    (unit (rings B)).val.map a ((φ.hom.app X) (s.val X)) =
      (φ.hom.app Y) (s.val Y) := by
  have h := CategoryTheory.congr_fun (φ.hom.naturality a) (s.val X)
  change (φ.hom.app Y) ((R.obj.map a) (s.val X)) =
    (B.obj.map a) ((φ.hom.app X) (s.val X)) at h
  change (B.obj.map a) ((φ.hom.app X) (s.val X)) = _
  rw [← h]
  exact congrArg (φ.hom.app Y) (s.property a)

/-- Image of a global section under the coefficient map. Source: Tag 099H
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def mapSection {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (s : (unit (rings R)).sections) : (unit (rings B)).sections :=
  ⟨fun X ↦ (φ.hom.app X) (s.val X), mapSection_naturality φ s⟩

private theorem unitMap_apply {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (X : Cᵒᵖ) (a : R.obj.obj X) :
    (unitMap φ).val.app X a = (φ.hom.app X) a :=
  (unitMap_existsUnique φ).choose_spec.1 X a

private theorem scalar_unitMap {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (f : (unit (rings R)).sections) (k : ℕ) :
    ((scalar R f ^ k).asHom) ≫ unitMap φ =
      unitMap φ ≫ (restriction φ).map ((scalar B (mapSection φ f) ^ k).asHom) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (unitMap φ).val.app X ((scalar R f ^ k).asHom.val.app X a) =
    (scalar B (mapSection φ f) ^ k).asHom.val.app X ((unitMap φ).val.app X a)
  rw [unitMap_apply, scalar_pow_apply, scalar_pow_apply, unitMap_apply]
  let b : R.obj.obj X := a
  change (φ.hom.app X).hom (b * value f X ^ k) =
    (φ.hom.app X).hom b * ((φ.hom.app X).hom (value f X)) ^ k
  simp

private theorem subsetScalar_unitMap {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (f : Fin r → (unit (rings R)).sections) (s : Finset (Fin r)) :
    (subsetScalar R r f s).asHom ≫ unitMap φ =
      unitMap φ ≫ (restriction φ).map ((subsetScalar B r (mapSection φ ∘ f) s)).asHom := by
  have hl : ∀ l : List (Fin r),
      l.foldr (fun j b ↦ (scalar R (f j)).asHom ≫ b) (𝟙 _) ≫ unitMap φ =
        unitMap φ ≫ (restriction φ).map
          (l.foldr (fun j b ↦ (scalar B (mapSection φ (f j))).asHom ≫ b) (𝟙 _)) := by
    intro l
    induction l with
    | nil => simp
    | cons j l ih =>
      simp only [List.foldr_cons, Category.assoc, ih, Functor.map_comp]
      have hs := scalar_unitMap φ (f j) 1
      simp only [pow_one] at hs
      rw [← Category.assoc, hs, Category.assoc]
  exact hl (s.sort (· ≤ ·))

/-- Comparison of the free Koszul terms, with the same subset labels.
Source: Tag 099H (blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def comparisonTerm {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (q : ℤ) : term R r q ⟶ (restriction φ).obj (term B r q) :=
  Sigma.desc (fun s ↦ unitMap φ ≫
    (restriction φ).map (Sigma.ι (fun _ : Indices r q ↦ unit (rings B)) s))

private theorem transitionTerm_comparison {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (f : Fin r → (unit (rings R)).sections) (q : ℤ) :
    transitionTerm R r f q ≫ comparisonTerm φ r q =
      comparisonTerm φ r q ≫ (restriction φ).map
        (transitionTerm B r (mapSection φ ∘ f) q) := by
  apply Sigma.hom_ext
  intro s
  simp only [transitionTerm, comparisonTerm, Category.assoc, Sigma.ι_comp_desc_assoc,
    Sigma.ι_comp_desc]
  rw [← Category.assoc, subsetScalar_unitMap, Category.assoc]
  simp only [← Functor.map_comp, Sigma.ι_comp_desc]

/-- The coefficient comparison commutes with the Koszul differential. Source: Tag 099H
(blueprint: def-weil-pbc-extended-localization-cech).
Proof: on the summand I the j-th insertion has the same integer sign on both sides;
the equality φ(f_j^(n+1) a) = φ(f_j)^(n+1) φ(a) gives its scalar coefficient.
Coproduct extensionality then gives the equality. -/
theorem comparison_comm {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (f : Fin r → (unit (rings R)).sections) (n : ℕ) (q : ℤ) :
    comparisonTerm φ r q ≫
        (((restriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (koszul B r (mapSection φ ∘ f) n)).d q (q + 1) =
      (koszul R r f n).d q (q + 1) ≫ comparisonTerm φ r (q + 1) := by
  classical
  dsimp only [term, Indices] at *
  simp only [koszul, Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d]
  change comparisonTerm φ r q ≫
    (restriction φ).map (differential B r (mapSection φ ∘ f) n q) =
    differential R r f n q ≫ comparisonTerm φ r (q + 1)
  apply Sigma.hom_ext
  intro s
  simp only [comparisonTerm, differential, Category.assoc, Sigma.ι_comp_desc_assoc,
    ← Functor.map_comp, Sigma.ι_comp_desc, Functor.map_sum,
    Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · simp only [Functor.map_zero, comp_zero, zero_comp]
  · simp only [Functor.map_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
      Functor.map_comp, Category.assoc, Sigma.ι_comp_desc, Function.comp_apply]
    rw [← Category.assoc, ← scalar_unitMap, Category.assoc]

/-- The termwise coefficient map of Koszul complexes. Source: Tag 099H
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def comparisonStage {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (f : Fin r → (unit (rings R)).sections) (n : ℕ) :
    koszul R r f n ⟶
      ((restriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (koszul B r (mapSection φ ∘ f) n) :=
  CochainComplex.ofHom (comparisonTerm φ r) (comparison_comm φ r f n)

/-- Stage maps give a cocone into the restricted target Čech complex. Source: Tag 099H
(blueprint: def-weil-pbc-extended-localization-cech).
Proof: coefficient maps carry each product of the f_i to the corresponding product
of their images, hence commute with each transition. Induction gives the same
identity for every natural-number arrow. The target colimit cocone then gives
exactly this naturality equation. -/
theorem comparisonCocone_naturality {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (f : Fin r → (unit (rings R)).sections)
    {n m : ℕ} (a : n ⟶ m) :
    (diagram R r f).map a ≫
        (comparisonStage φ r f m ≫
          ((restriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (colimit.ι (diagram B r (mapSection φ ∘ f)) m)) =
      comparisonStage φ r f n ≫
        ((restriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (colimit.ι (diagram B r (mapSection φ ∘ f)) n) := by
  let T := (restriction φ).mapHomologicalComplex (ComplexShape.up ℤ)
  let t : diagram R r f ⟶ diagram B r (mapSection φ ∘ f) ⋙ T :=
    NatTrans.ofSequence (comparisonStage φ r f) (fun n ↦ by
      simp only [diagram, Functor.ofSequence_map_homOfLE_succ, Functor.comp_map]
      apply HomologicalComplex.hom_ext
      intro q
      exact transitionTerm_comparison φ r f q)
  change (diagram R r f).map a ≫ (t.app m ≫ T.map _) = t.app n ≫ T.map _
  rw [← Category.assoc, t.naturality, Functor.comp_map, Category.assoc, ← T.map_comp, colimit.w]

/-- Cocone of the explicit coefficient comparisons. Source: Tag 099H
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def comparisonCocone {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (f : Fin r → (unit (rings R)).sections) : Cocone (diagram R r f) where
  pt := ((restriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (complex B r (mapSection φ ∘ f))
  ι :=
    { app := fun n ↦ comparisonStage φ r f n ≫
        ((restriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (colimit.ι (diagram B r (mapSection φ ∘ f)) n)
      naturality := fun _ _ a ↦ comparisonCocone_naturality φ r f a }

/-- The canonical termwise localization comparison. On a fraction it sends
 a/(product_I f_i)^k to φ(a)/(product_I φ(f_i))^k.
Source: Tag 099H (blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def comparison {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (f : Fin r → (unit (rings R)).sections) :
    complex R r f ⟶
      ((restriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (complex B r (mapSection φ ∘ f)) :=
  colimit.desc (diagram R r f) (comparisonCocone φ r f)

/-- The coefficient map followed by the target quotient annihilates the source ideal.
Source: Tag 099H (blueprint: def-weil-pbc-extended-localization-cech).
Proof: on the j-th summand, φ(f_j a) = φ(f_j) φ(a); this belongs to the target ideal.
The cokernel projection kills every generator, so the composite is zero. -/
theorem idealRow_comparison_zero {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (f : Fin r → (unit (rings R)).sections) :
    idealRow R r f ≫
      (unitMap φ ≫ (restriction φ).map (cokernel.π (idealRow B r (mapSection φ ∘ f)))) =
        0 := by
  classical
  have hi : ∀ j, Sigma.ι (fun _ : Fin r ↦ unit (rings R)) j ≫ idealRow R r f =
      (scalar R (f j)).asHom := fun j ↦ Sigma.ι_comp_desc _ _
  have hb : ∀ j, Sigma.ι (fun _ : Fin r ↦ unit (rings B)) j ≫
      idealRow B r (mapSection φ ∘ f) = (scalar B (mapSection φ (f j))).asHom :=
    fun j ↦ Sigma.ι_comp_desc _ _
  apply Sigma.hom_ext
  intro j
  rw [← Category.assoc, hi]
  have hs := scalar_unitMap φ (f j) 1
  simp only [pow_one] at hs
  rw [← Category.assoc, hs, Category.assoc, ← Functor.map_comp, ← hb j,
    Category.assoc, cokernel.condition, comp_zero, Functor.map_zero, comp_zero, comp_zero]

/-- Underlying module morphism of the canonical quotient-ring-sheaf map.
The cokernel of the row is the sheafified quotient by the generated ideal; being
an isomorphism of this underlying module morphism is equivalent to the canonical
quotient-ring-sheaf map being an isomorphism.
Source: Tag 099H (blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def quotientComparison {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (r : ℕ) (f : Fin r → (unit (rings R)).sections) :
    cokernel (idealRow R r f) ⟶
      (restriction φ).obj (cokernel (idealRow B r (mapSection φ ∘ f))) :=
  cokernel.desc (idealRow R r f)
    (unitMap φ ≫ (restriction φ).map (cokernel.π (idealRow B r (mapSection φ ∘ f))))
    (idealRow_comparison_zero φ r f)

/-- Fold the unique empty-subset summand onto the coefficient sheaf.
Source: Tag 0913 (blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def degreeZeroFold (R : Sheaf J CommRingCat.{u}) (r : ℕ) :
    term R r 0 ⟶ unit (rings R) :=
  Sigma.desc (fun _ ↦ 𝟙 _)

/-- There is no incoming differential in degree zero. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech).
Proof: a subset cannot have negative cardinality, so degree minus one is an empty
coproduct, hence zero. Every morphism out of it is zero. -/
theorem augmentation_incoming (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) (i : ℤ)
    (h : (ComplexShape.up ℤ).Rel i 0) :
    (koszul R r f n).d i 0 ≫ degreeZeroFold R r = 0 := by
  have hi : i + 1 = 0 := h
  have hempty : IsEmpty (Indices r i) := ⟨fun s ↦ by
    have hn := Int.natCast_nonneg s.val.card
    rw [s.property] at hn
    omega⟩
  apply Sigma.hom_ext
  intro s
  exact (hempty.false s).elim

/-- Koszul augmentation to the coefficient sheaf in degree zero.
Source: Tag 0913 (blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def augmentationStage (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) :
    koszul R r f n ⟶
      (HomologicalComplex.single (CategoryTheory.ringedSiteModules.{u} (rings R))
        (ComplexShape.up ℤ) 0).obj (unit (rings R)) :=
  HomologicalComplex.mkHomToSingle (degreeZeroFold R r) (augmentation_incoming R r f n)

/-- The augmentations are compatible with the Koszul transitions. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech).
Proof: the empty-subset product is the identity. Thus every transition is the
identity in degree zero, where both augmentations are the fold. All other
augmentation components are zero. Iterate this equality along the given arrow. -/
theorem augmentation_naturality (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) {n m : ℕ} (a : n ⟶ m) :
    (diagram R r f).map a ≫ augmentationStage R r f m = augmentationStage R r f n := by
  let F := diagram R r f
  let A := (HomologicalComplex.single (CategoryTheory.ringedSiteModules.{u} (rings R))
    (ComplexShape.up ℤ) 0).obj (unit (rings R))
  let t : F ⟶ (Functor.const ℕ).obj A := NatTrans.ofSequence
    (augmentationStage R r f) (fun n ↦ by
      simp only [F, diagram, Functor.ofSequence_map_homOfLE_succ,
        Functor.const_obj_map]
      apply HomologicalComplex.to_single_hom_ext
      simp only [HomologicalComplex.comp_f, augmentationStage,
        HomologicalComplex.mkHomToSingle_f]
      change transitionTerm R r f 0 ≫ degreeZeroFold R r ≫ _ = degreeZeroFold R r ≫ _
      have hfold : transitionTerm R r f 0 ≫ degreeZeroFold R r = degreeZeroFold R r := by
        apply Sigma.hom_ext
        intro s
        have hs : s.val = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast s.property)
        simp [transitionTerm, degreeZeroFold, subsetScalar, hs]
      rw [← Category.assoc, hfold]
      rfl)
  exact (t.naturality a).trans (Category.comp_id _)

/-- The augmentation cocone. Source: Tag 0913
(blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def augmentationCocone (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) : Cocone (diagram R r f) where
  pt := (HomologicalComplex.single (CategoryTheory.ringedSiteModules.{u} (rings R))
    (ComplexShape.up ℤ) 0).obj (unit (rings R))
  ι :=
    { app := augmentationStage R r f
      naturality := fun _ _ a ↦ augmentation_naturality R r f a }

/-- Augmentation of the extended Čech complex: identity on the empty-subset
coefficient sheaf in degree zero, and zero in every other degree.
Source: Tag 0913 (blueprint: def-weil-pbc-extended-localization-cech). -/
noncomputable def augmentation (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) :
    complex R r f ⟶
      (HomologicalComplex.single (CategoryTheory.ringedSiteModules.{u} (rings R))
        (ComplexShape.up ℤ) 0).obj (unit (rings R)) :=
  colimit.desc (diagram R r f) (augmentationCocone R r f)

end LocalizationCech
end SheafOfModules
