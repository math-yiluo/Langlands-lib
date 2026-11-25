/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechHomologySurjective
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechHomologyInjective

/-! # Alternating total Čech complexes on finite principal covers

Source: Stacks Project, Cohomology, Sections 20.25 and 20.40, and Tag 08D2
(blueprint: def-sc-principal-open-alternating-total).
Nonempty subsets index the alternating rows; the empty cover gives the zero complex.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC wC vC

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

variable (A : Type uC) [CommRing A]

/-- Sections on an affine scheme, with the A-action supplied by Mathlib's
`modulesSpecToSheaf`. Source: Stacks, Tag 08D2
(blueprint: def-sc-principal-open-alternating-total). -/
def affineOpenSections (U : (Spec (.of A)).Opens) :
    SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace) ⥤ ModuleCat.{uC} A where
  obj F := (modulesSpecToSheaf.obj F).obj.obj (op U)
  map g := (modulesSpecToSheaf.map g).hom.app (op U)
  map_id F := congrArg (fun g ↦ g.hom.app (op U)) (modulesSpecToSheaf.map_id F)
  map_comp g h := congrArg (fun g ↦ g.hom.app (op U)) (modulesSpecToSheaf.map_comp g h)

/-- The additive instance for A-module sections.
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total). -/
instance affineOpenSections_additive (U : (Spec (.of A)).Opens) :
    (affineOpenSections A U).Additive := by
  constructor
  intro F G g h
  rfl

variable {A} (r : ℕ) (f : Fin r → A)

/-- The intersection belonging to a finite subset of cover indices.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechIntersection (J : Finset (Fin r)) : (Spec (.of A)).Opens :=
  PrimeSpectrum.basicOpen (∏ j ∈ J, f j)

/-- Erasing an index enlarges a principal intersection.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total).
Proof: the product for J is the erased product times f_j. Its basic open is their
intersection, hence contained in the erased basic open. -/
theorem principalCechIntersection_erase_le (J : Finset (Fin r)) (j : Fin r) :
    principalCechIntersection r f J ≤ principalCechIntersection r f (J.erase j) := by
  classical
  unfold principalCechIntersection
  by_cases hj : j ∈ J
  · rw [← Finset.mul_prod_erase J f hj]
    exact PrimeSpectrum.basicOpen_mul_le_right _ _
  · simp [Finset.erase_eq_of_notMem hj]

/-- Each singleton principal open is contained in the union of the principal opens.
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total).
Proof: a singleton product is f_j, and each D(f_j) is contained in their supremum. -/
theorem principalCechIntersection_singleton_le (j : Fin r) :
    principalCechIntersection r f {j} ≤ ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i) := by
  simpa [principalCechIntersection] using
    (le_iSup (fun i : Fin r ↦ PrimeSpectrum.basicOpen (f i)) j)

/-- Deleting an index gives the same vertical degree in the incoming horizontal row.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total).
Proof: card(J.erase j) = card(J)-1 when j belongs to J; subtract this identity in ℤ. -/
theorem principalCech_erase_degree (J : Finset (Fin r)) (j : Fin r) (hj : j ∈ J) (n : ℤ) :
    n + 1 - ((J.erase j).card : ℤ) = (n + 1) + 1 - (J.card : ℤ) := by
  have h := Finset.card_erase_add_one hj
  omega

variable (F : CochainComplex
  (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

/-- Total Čech cochains, with row p = card(J)-1 and vertical degree n-p.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechTerms (n : ℤ) : ModuleCat.{uC} A :=
  ModuleCat.of A (∀ J : {J : Finset (Fin r) // J.Nonempty},
    (affineOpenSections A (principalCechIntersection r f J.val)).obj
      (F.X (n + 1 - (J.val.card : ℤ))))

/-- The signed total differential: alternating horizontal restriction and
`(-1)^p d_F` in row p. Empty erased subsets contribute zero.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechDifferentialValue (n : ℤ) (s : principalCechTerms r f F n) :
    principalCechTerms r f F (n + 1) :=
  fun J ↦
    (-1 : A) ^ (J.val.card - 1) •
      (affineOpenSections A (principalCechIntersection r f J.val)).map
        (F.d (n + 1 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ))) (s J) +
    @id ((affineOpenSections A (principalCechIntersection r f J.val)).obj
      (F.X ((n + 1) + 1 - (J.val.card : ℤ)))) (∑ j : J.val, if h : (J.val.erase j.val).Nonempty then
      (-1 : A) ^ ((J.val.filter (fun i ↦ i < j.val)).card) •
        (modulesSpecToSheaf.obj (F.X ((n + 1) + 1 - (J.val.card : ℤ)))).obj.map
          (homOfLE (principalCechIntersection_erase_le r f J.val j.val)).op
          ((affineOpenSections A (principalCechIntersection r f (J.val.erase j.val))).map
            (eqToHom (congrArg F.X
              (principalCech_erase_degree r J.val j.val j.property n)))
            (s ⟨J.val.erase j.val, h⟩))
    else 0)

/-- Existence of the linear total differential, with exactly the displayed value.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total).
Proof: every restriction and coefficient differential is A-linear; multiplication by a
sign and finite sums preserve linearity. -/
theorem principalCechDifferential_exists (n : ℤ) :
    ∃ d : principalCechTerms r f F n ⟶ principalCechTerms r f F (n + 1),
      ∀ s, d s = principalCechDifferentialValue r f F n s := by
  classical
  refine ⟨ModuleCat.ofHom
    { toFun := principalCechDifferentialValue r f F n
      map_add' := ?_
      map_smul' := ?_ }, fun _ ↦ rfl⟩
  · intro s t
    funext J
    simp only [principalCechDifferentialValue, Pi.add_apply, id_eq]
    simp only [map_add, smul_add]
    rw [add_add_add_comm, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp only [add_zero]
  · intro a s
    funext J
    simp only [principalCechDifferentialValue, Pi.smul_apply, id_eq]
    simp only [map_smul, RingHom.id_apply, smul_add, Finset.smul_sum]
    congr 1
    · exact smul_comm _ _ _
    · apply Finset.sum_congr rfl
      intro j _
      split
      · rw [smul_comm]
      · exact (smul_zero a).symm

/-- The A-linear total differential, selected from its fully specified formula.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechDifferential (n : ℤ) :
    principalCechTerms r f F n ⟶ principalCechTerms r f F (n + 1) :=
  (principalCechDifferential_exists r f F n).choose

private def principalCechVerticalValue (n : ℤ) (s : principalCechTerms r f F n) :
    principalCechTerms r f F (n + 1) :=
  fun J ↦ (-1 : A) ^ (J.val.card - 1) •
    (affineOpenSections A (principalCechIntersection r f J.val)).map
      (F.d (n + 1 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ))) (s J)

private def principalCechHorizontalValue (n : ℤ) (s : principalCechTerms r f F n) :
    principalCechTerms r f F (n + 1) :=
  fun J ↦ ∑ j : J.val, if h : (J.val.erase j.val).Nonempty then
    (-1 : A) ^ ((J.val.filter (fun i ↦ i < j.val)).card) •
      (modulesSpecToSheaf.obj (F.X ((n + 1) + 1 - (J.val.card : ℤ)))).obj.map
        (homOfLE (principalCechIntersection_erase_le r f J.val j.val)).op
        ((affineOpenSections A (principalCechIntersection r f (J.val.erase j.val))).map
          (eqToHom (congrArg F.X
            (principalCech_erase_degree r J.val j.val j.property n)))
          (s ⟨J.val.erase j.val, h⟩))
    else 0

private theorem principalCechVertical_square (n : ℤ) (s : principalCechTerms r f F n) :
    principalCechVerticalValue r f F (n + 1) (principalCechVerticalValue r f F n s) = 0 := by
  funext J
  dsimp only [principalCechVerticalValue]
  rw [map_smul, smul_smul]
  change _ • (((affineOpenSections A (principalCechIntersection r f J.val)).map
    (F.d (n + 1 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ))) ≫
    (affineOpenSections A (principalCechIntersection r f J.val)).map
    (F.d ((n + 1) + 1 - (J.val.card : ℤ)) (((n + 1) + 1) + 1 -
      (J.val.card : ℤ)))) (s J)) = 0
  rw [← Functor.map_comp, F.d_comp_d]
  simp

private theorem deletion_sign {A : Type uC} [CommRing A] {r : ℕ} (S : Finset (Fin r))
    (a b : Fin r) (ha : a ∈ S) (hab : a < b) :
    (-1 : A) ^ (S.filter (fun k ↦ k < a)).card *
        (-1 : A) ^ ((S.erase a).filter (fun k ↦ k < b)).card =
      -((-1 : A) ^ (S.filter (fun k ↦ k < b)).card *
        (-1 : A) ^ ((S.erase b).filter (fun k ↦ k < a)).card) := by
  have h₁ : ((S.erase b).filter (fun k ↦ k < a)) = S.filter (fun k ↦ k < a) := by
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
    simp only [Finset.mem_filter, not_and]
    exact fun _ ↦ not_lt_of_ge (le_of_lt hab)
  have h₂ : ((S.erase a).filter (fun k ↦ k < b)).card + 1 =
      (S.filter (fun k ↦ k < b)).card := by
    rw [Finset.filter_erase]
    exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨ha, hab⟩)
  rw [h₁, ← h₂, pow_succ]
  ring

private theorem alternating_erase_sum {A : Type uC} [CommRing A]
    {r : ℕ} {M : Type*} [AddCommGroup M] [Module A M]
    (S : Finset (Fin r)) (t : Fin r → Fin r → M)
    (ht : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → t a b = t b a) :
    (∑ a ∈ S, ∑ b ∈ S.erase a,
      ((-1 : A) ^ (S.filter (fun k ↦ k < a)).card *
        (-1 : A) ^ ((S.erase a).filter (fun k ↦ k < b)).card) • t a b) = 0 := by
  classical
  let w (ab : Fin r × Fin r) : M :=
    ((-1 : A) ^ (S.filter (fun k ↦ k < ab.1)).card *
      (-1 : A) ^ ((S.erase ab.1).filter (fun k ↦ k < ab.2)).card) • t ab.1 ab.2
  have hw : ∑ ab ∈ S.offDiag, w ab = 0 := by
    have hm (ab : Fin r × Fin r) (hab : ab ∈ S.offDiag) : ab.swap ∈ S.offDiag := by
      exact Finset.mem_offDiag.mpr
        ⟨(Finset.mem_offDiag.mp hab).2.1, (Finset.mem_offDiag.mp hab).1,
          (Finset.mem_offDiag.mp hab).2.2.symm⟩
    refine Finset.sum_involution (fun ab _ ↦ ab.swap) ?_ ?_ hm ?_
    · intro ab hab
      obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
      have he : t ab.1 ab.2 = t ab.2 ab.1 := ht _ ha _ hb hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · dsimp [w]
        rw [deletion_sign S _ _ ha hlt, he, neg_smul]
        exact neg_add_cancel _
      · dsimp [w]
        rw [deletion_sign S _ _ hb hlt, ← he, neg_smul]
        exact add_neg_cancel _
    · intro ab hab _ heq
      exact (Finset.mem_offDiag.mp hab).2.2 (congrArg Prod.fst heq).symm
    · intro ab _
      exact Prod.swap_swap ab
  rw [Finset.sum_finset_product S.offDiag S (fun a ↦ S.erase a)
    (fun ab ↦ by simp only [Finset.mem_offDiag, Finset.mem_erase]; tauto)] at hw
  exact hw

private theorem transport_two_restrictions {A : Type uC} [CommRing A]
    (F : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (U V W : (Spec (.of A)).Opens) (hVU : V ≤ U) (hWV : W ≤ V)
    (a b c : ℤ) (e : a = b) (e' : b = c) :
    (affineOpenSections A U).map (eqToHom (congrArg F.X e)) ≫
        (modulesSpecToSheaf.obj (F.X b)).obj.map (homOfLE hVU).op ≫
        (affineOpenSections A V).map (eqToHom (congrArg F.X e')) ≫
        (modulesSpecToSheaf.obj (F.X c)).obj.map (homOfLE hWV).op =
      (affineOpenSections A U).map (eqToHom (congrArg F.X (e.trans e'))) ≫
        (modulesSpecToSheaf.obj (F.X c)).obj.map (homOfLE (hWV.trans hVU)).op := by
  subst b c
  change (𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _) = (𝟙 _ ≫ _)
  simp only [Category.id_comp]
  exact ((modulesSpecToSheaf.obj (F.X a)).obj.map_comp
    (homOfLE hVU).op (homOfLE hWV).op).symm

private noncomputable def doubleTerm {A : Type uC} [CommRing A]
    (r : ℕ) (f : Fin r → A)
    (F : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (n : ℤ) (s : principalCechTerms r f F n) (T S : Finset (Fin r)) :
    (affineOpenSections A (principalCechIntersection r f T)).obj
      (F.X (((n + 1) + 1) + 1 - (T.card : ℤ))) := by
  classical
  exact if hc : n + 1 - (S.card : ℤ) = ((n + 1) + 1) + 1 - (T.card : ℤ) then
    if hl : principalCechIntersection r f T ≤ principalCechIntersection r f S then
      if hn : S.Nonempty then
        (modulesSpecToSheaf.obj (F.X (((n + 1) + 1) + 1 - (T.card : ℤ)))).obj.map
          (homOfLE hl).op
          ((affineOpenSections A (principalCechIntersection r f S)).map
            (eqToHom (congrArg F.X hc)) (s ⟨S, hn⟩))
      else 0
    else 0
  else 0

/-- Horizontal square-zero, the two-deletion part of the total calculation.
Source: Stacks Project, Cohomology, Tag 08D1.
(blueprint: def-sc-principal-open-alternating-total).

Proof: Expand the two finite signed sums. Terms with an empty twice-erased subset
vanish. Pair the surviving deletion orders (a,b) and (b,a). Their restrictions
and degree transports agree by presheaf functoriality and equality induction.
When a < b, erasing a lowers the position of b by one, while erasing b does not
change the position of a. The paired signs are negatives. Sum the cancelling
pairs using the swap involution on the off-diagonal of the subset. Singletons,
pairs, and the empty cover have no surviving twice-deletion terms. -/
private theorem principalCechHorizontalValue_square {A : Type uC} [CommRing A]
    (r : ℕ) (f : Fin r → A)
    (F : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (n : ℤ) (s : principalCechTerms r f F n) :
    principalCechHorizontalValue r f F (n + 1)
      (principalCechHorizontalValue r f F n s) = 0 := by
  classical
  change (fun T ↦ _) = (fun T ↦ 0)
  funext T
  let t (a b : Fin r) := doubleTerm r f F n s T.val ((T.val.erase a).erase b)
  have ht (a b : Fin r) : t a b = t b a := by
    dsimp only [t]
    rw [Finset.erase_right_comm]
  have hh : (∑ a ∈ T.val, ∑ b ∈ T.val.erase a,
      ((-1 : A) ^ (T.val.filter (fun k ↦ k < a)).card *
        (-1 : A) ^ ((T.val.erase a).filter (fun k ↦ k < b)).card) • t a b) = 0 :=
    alternating_erase_sum T.val t (fun a _ b _ _ ↦ ht a b)
  change (∑ a : T.val, _) = 0
  trans (∑ a ∈ T.val, ∑ b ∈ T.val.erase a,
    ((-1 : A) ^ (T.val.filter (fun k ↦ k < a)).card *
      (-1 : A) ^ ((T.val.erase a).filter (fun k ↦ k < b)).card) • t a b)
  swap
  · exact hh
  rw [← Finset.sum_coe_sort T.val]
  apply Finset.sum_congr rfl
  intro a _
  split
  next hn =>
    simp only [principalCechHorizontalValue, map_sum, Finset.smul_sum]
    rw [← Finset.sum_coe_sort (T.val.erase a.val)]
    apply Finset.sum_congr rfl
    intro b _
    have hc : n + 1 - (((T.val.erase a.val).erase b.val).card : ℤ) =
        ((n + 1) + 1) + 1 - (T.val.card : ℤ) := by
      have := Finset.card_erase_add_one a.property
      have := Finset.card_erase_add_one b.property
      omega
    have hl := (principalCechIntersection_erase_le r f T.val a.val).trans
      (principalCechIntersection_erase_le r f (T.val.erase a.val) b.val)
    dsimp only [t, doubleTerm]
    rw [dite_eq_left hc, dite_eq_left hl]
    split
    next hn₂ =>
      rw [map_smul, map_smul, smul_smul]
      apply congrArg (fun z ↦ ((-1 : A) ^ (T.val.filter (fun k ↦ k < a.val)).card *
        (-1 : A) ^ ((T.val.erase a.val).filter (fun k ↦ k < b.val)).card) • z)
      exact ConcreteCategory.congr_hom
        (transport_two_restrictions F
          (principalCechIntersection r f ((T.val.erase a.val).erase b.val))
          (principalCechIntersection r f (T.val.erase a.val))
          (principalCechIntersection r f T.val)
          (principalCechIntersection_erase_le r f (T.val.erase a.val) b.val)
          (principalCechIntersection_erase_le r f T.val a.val)
          (n + 1 - (((T.val.erase a.val).erase b.val).card : ℤ))
          ((n + 1) + 1 - ((T.val.erase a.val).card : ℤ))
          (((n + 1) + 1) + 1 - (T.val.card : ℤ))
          (principalCech_erase_degree r (T.val.erase a.val) b.val b.property n)
          (principalCech_erase_degree r T.val a.val a.property (n + 1)))
          (s ⟨(T.val.erase a.val).erase b.val, hn₂⟩)
    next hn₂ => simp
  next hn =>
    have he : T.val.erase a.val = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he]

private theorem transport_restriction_d {A : Type uC} [CommRing A]
    (F : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (U V : (Spec (.of A)).Opens) (hle : V ≤ U)
    (a b c d : ℤ) (e : a = c) (e' : b = d) :
    (affineOpenSections A U).map (eqToHom (congrArg F.X e)) ≫
        (modulesSpecToSheaf.obj (F.X c)).obj.map (homOfLE hle).op ≫
        (affineOpenSections A V).map (F.d c d) =
      (affineOpenSections A U).map (F.d a b) ≫
        (affineOpenSections A U).map (eqToHom (congrArg F.X e')) ≫
        (modulesSpecToSheaf.obj (F.X d)).obj.map (homOfLE hle).op := by
  subst c d
  change (𝟙 _ ≫ _) = (_ ≫ 𝟙 _ ≫ _)
  simp only [Category.id_comp]
  exact (modulesSpecToSheaf.map (F.d a b)).hom.naturality (homOfLE hle).op

/-- The mixed horizontal and vertical terms cancel.
Source: Stacks Project, Cohomology, Tag 08D1.
(blueprint: def-sc-principal-open-alternating-total).

Proof: Distribute the vertical map across the finite horizontal sum, using its
linearity. For each deletion of j, restriction commutes with the coefficient
differential by naturality of modulesSpecToSheaf.map. Equality induction on the
degree transports identifies both coefficient maps. If the erased subset is
nonempty, its cardinality is one less, so the vertical signs of the two rows
are negatives. Thus each pair of mixed summands cancels. Empty erased subsets
contribute zero to both sums. Sum these identities; the empty cover is vacuous. -/
private theorem principalCechValue_mixed_cancel {A : Type uC} [CommRing A] (r : ℕ) (f : Fin r → A)
    (F : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (n : ℤ) (s : principalCechTerms r f F n) :
    principalCechVerticalValue r f F (n + 1)
        (principalCechHorizontalValue r f F n s) +
      principalCechHorizontalValue r f F (n + 1)
        (principalCechVerticalValue r f F n s) = 0 := by
  classical
  change (fun T ↦ _) + (fun T ↦ _) = (fun T ↦ 0)
  funext T
  simp only [Pi.add_apply, principalCechVerticalValue, principalCechHorizontalValue]
  rw [map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  split
  next h =>
    rw [map_smul, smul_smul]
    rw [map_smul, map_smul, smul_smul]
    have he := ConcreteCategory.congr_hom
      (transport_restriction_d F
        (principalCechIntersection r f (T.val.erase j.val))
        (principalCechIntersection r f T.val)
        (principalCechIntersection_erase_le r f T.val j.val)
        (n + 1 - ((T.val.erase j.val).card : ℤ))
        ((n + 1) + 1 - ((T.val.erase j.val).card : ℤ))
        ((n + 1) + 1 - (T.val.card : ℤ))
        (((n + 1) + 1) + 1 - (T.val.card : ℤ))
        (principalCech_erase_degree r T.val j.val j.property n)
        (principalCech_erase_degree r T.val j.val j.property (n + 1)))
        (s ⟨T.val.erase j.val, h⟩)
    simp only [ModuleCat.comp_apply] at he
    have hc : T.val.card - 1 = (T.val.erase j.val).card - 1 + 1 := by
      have := Finset.card_erase_add_one j.property
      have := h.card_pos
      omega
    have hsign : (-1 : A) ^ (T.val.card - 1) *
        (-1 : A) ^ (T.val.filter (fun i ↦ i < j.val)).card =
      -((-1 : A) ^ (T.val.filter (fun i ↦ i < j.val)).card *
        (-1 : A) ^ ((T.val.erase j.val).card - 1)) := by
      rw [hc, pow_succ]
      ring
    let x := (modulesSpecToSheaf.obj
      (F.X (((n + 1) + 1) + 1 - (T.val.card : ℤ)))).obj.map
        (homOfLE (principalCechIntersection_erase_le r f T.val j.val)).op
        ((affineOpenSections A (principalCechIntersection r f (T.val.erase j.val))).map
          (eqToHom (congrArg F.X
            (principalCech_erase_degree r T.val j.val j.property (n + 1))))
          ((affineOpenSections A (principalCechIntersection r f (T.val.erase j.val))).map
            (F.d (n + 1 - ((T.val.erase j.val).card : ℤ))
              ((n + 1) + 1 - ((T.val.erase j.val).card : ℤ)))
            (s ⟨T.val.erase j.val, h⟩)))
    trans ((-1 : A) ^ (T.val.card - 1) *
        (-1 : A) ^ (T.val.filter (fun i ↦ i < j.val)).card) • x +
      ((-1 : A) ^ (T.val.filter (fun i ↦ i < j.val)).card *
        (-1 : A) ^ ((T.val.erase j.val).card - 1)) • x
    · exact congrArg₂ (· + ·) (congrArg (fun z ↦
        ((-1 : A) ^ (T.val.card - 1) *
          (-1 : A) ^ (T.val.filter (fun i ↦ i < j.val)).card) • z) he) rfl
    · rw [hsign, neg_smul]
      exact neg_add_cancel _
  next => simp
/-- Consecutive total Čech differentials compose to zero.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total).
Proof: two horizontal deletions cancel with opposite signs; vertical squares are zero;
the mixed terms cancel because the vertical sign changes between adjacent rows.
Restrictions commute with the coefficient differential. -/
theorem principalCechDifferential_square (n : ℤ) :
    principalCechDifferential r f F n ≫ principalCechDifferential r f F (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change (principalCechDifferential_exists r f F (n + 1)).choose
    ((principalCechDifferential_exists r f F n).choose s) = 0
  rw [(principalCechDifferential_exists r f F n).choose_spec,
    (principalCechDifferential_exists r f F (n + 1)).choose_spec]
  have hsplit (m : ℤ) (t : principalCechTerms r f F m) :
      principalCechDifferentialValue r f F m t =
        principalCechVerticalValue r f F m t + principalCechHorizontalValue r f F m t := rfl
  have hadd (m : ℤ) (t u : principalCechTerms r f F m) :
      principalCechDifferentialValue r f F m (t + u) =
        principalCechDifferentialValue r f F m t + principalCechDifferentialValue r f F m u := by
    rw [← (principalCechDifferential_exists r f F m).choose_spec,
      ← (principalCechDifferential_exists r f F m).choose_spec,
      ← (principalCechDifferential_exists r f F m).choose_spec]
    exact map_add _ _ _
  rw [hsplit n s, hadd, hsplit, hsplit, principalCechVertical_square,
    principalCechHorizontalValue_square, zero_add, add_zero]
  exact (add_comm _ _).trans (principalCechValue_mixed_cancel r f F n s)

/-- The alternating Čech total complex, including unbounded coefficient complexes.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechTotal : CochainComplex (ModuleCat.{uC} A) ℤ :=
  CochainComplex.of (principalCechTerms r f F) (principalCechDifferential r f F)
    (principalCechDifferential_square r f F)

private theorem principalCech_transport_naturality
    {G : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ}
    (g : F ⟶ G) (m k : ℤ) (e : m = k) (U : (Spec (.of A)).Opens) :
    (affineOpenSections A U).map (g.f m) ≫
        (affineOpenSections A U).map (eqToHom (congrArg G.X e)) =
      (affineOpenSections A U).map (eqToHom (congrArg F.X e)) ≫
        (affineOpenSections A U).map (g.f k) := by
  subst k
  simp

set_option linter.unusedVariables false in
/-- The Čech totalization extends to an additive functor, with componentwise maps.
Its augmentation restricts sections of the union to the singleton rows and is zero
on all larger subsets. Source: Stacks, Tag 08D2
(blueprint: def-sc-principal-open-alternating-total).
Proof: apply a coefficient chain map to each subset's sections; naturality commutes with
restrictions and the vertical differential. Identities and composition are componentwise.
The alternating differential of restrictions is zero; restrictions commute with d_F. -/
theorem principalCechFunctor_exists :
    ∃ (C : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ ⥤
        CochainComplex (ModuleCat.{uC} A) ℤ) (hC : C.Additive),
      (∀ F, C.obj F = principalCechTotal r f F) ∧
      (∀ (F G : CochainComplex
        (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (g : F ⟶ G)
        (n : ℤ) (s : principalCechTerms r f F n) (J : {J : Finset (Fin r) // J.Nonempty})
        (hF : C.obj F = principalCechTotal r f F)
        (hG : C.obj G = principalCechTotal r f G),
        ((eqToHom hF.symm ≫ C.map g ≫ eqToHom hG).f n) s J =
          (affineOpenSections A (principalCechIntersection r f J.val)).map
            (g.f (n + 1 - (J.val.card : ℤ)))
            (s J)) := by
  classical
  let φ (F G : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
      (g : F ⟶ G) (n : ℤ) :
      principalCechTerms r f F n ⟶ principalCechTerms r f G n :=
    ModuleCat.ofHom
      { toFun := fun s J ↦
          (affineOpenSections A (principalCechIntersection r f J.val)).map
            (g.f (n + 1 - (J.val.card : ℤ))) (s J)
        map_add' := fun s t ↦ by
          funext J
          exact map_add _ _ _
        map_smul' := fun a s ↦ by
          funext J
          exact ((affineOpenSections A (principalCechIntersection r f J.val)).map
            (g.f (n + 1 - (J.val.card : ℤ)))).hom.map_smul a (s J) }
  have hcomm (F G : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
      (g : F ⟶ G) (n : ℤ) :
      φ F G g n ≫ (principalCechTotal r f G).d n (n + 1) =
        (principalCechTotal r f F).d n (n + 1) ≫ φ F G g (n + 1) := by
    ext s
    simp only [principalCechTotal, CochainComplex.of_d, ModuleCat.comp_apply]
    change (principalCechDifferential_exists r f G n).choose (φ F G g n s) =
      φ F G g (n + 1) ((principalCechDifferential_exists r f F n).choose s)
    rw [(principalCechDifferential_exists r f G n).choose_spec,
      (principalCechDifferential_exists r f F n).choose_spec]
    dsimp only [φ]
    funext J
    let τ := (affineOpenSections A (principalCechIntersection r f J.val)).map
      (g.f ((n + 1) + 1 - (J.val.card : ℤ)))
    change _ = τ _
    simp only [principalCechDifferentialValue, id_eq]
    rw [τ.hom.map_add, τ.hom.map_smul, map_sum τ.hom]
    apply congrArg₂ (· + ·)
    · apply congrArg (_ • ·)
      change ((affineOpenSections A (principalCechIntersection r f J.val)).map
        (g.f (n + 1 - (J.val.card : ℤ))) ≫
        (affineOpenSections A (principalCechIntersection r f J.val)).map
        (G.d (n + 1 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ)))) (s J) =
        ((affineOpenSections A (principalCechIntersection r f J.val)).map
        (F.d (n + 1 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ))) ≫
        τ) (s J)
      dsimp only [τ]
      rw [← Functor.map_comp, ← Functor.map_comp, g.comm]
    · apply Finset.sum_congr rfl
      intro j _
      split
      next h =>
        rw [τ.hom.map_smul]
        apply congrArg (_ • ·)
        have hres := (modulesSpecToSheaf.map (g.f
          ((n + 1) + 1 - (J.val.card : ℤ)))).hom.naturality
            (homOfLE (principalCechIntersection_erase_le r f J.val j.val)).op
        have hcast := principalCech_transport_naturality F g
          (n + 1 - ((J.val.erase j.val).card : ℤ))
          ((n + 1) + 1 - (J.val.card : ℤ))
          (principalCech_erase_degree r J.val j.val j.property n)
          (principalCechIntersection r f (J.val.erase j.val))
        have hcast' := ConcreteCategory.congr_hom hcast (s ⟨J.val.erase j.val, h⟩)
        have hres' := ConcreteCategory.congr_hom hres
          ((affineOpenSections A (principalCechIntersection r f (J.val.erase j.val))).map
            (eqToHom (congrArg F.X
              (principalCech_erase_degree r J.val j.val j.property n)))
            (s ⟨J.val.erase j.val, h⟩))
        simp only [ModuleCat.comp_apply] at hcast' hres'
        exact (congrArg
          ((modulesSpecToSheaf.obj (G.X ((n + 1) + 1 - (J.val.card : ℤ)))).obj.map
            (homOfLE (principalCechIntersection_erase_le r f J.val j.val)).op)
          hcast').trans hres'.symm
      next h => exact τ.hom.map_zero.symm
  let C : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ ⥤
      CochainComplex (ModuleCat.{uC} A) ℤ :=
    { obj := principalCechTotal r f
      map := fun g ↦ CochainComplex.ofHom (φ _ _ g) (hcomm _ _ g)
      map_id := fun F ↦ by
        ext n s
        dsimp only [φ]
        funext J
        simp
        rfl
      map_comp := fun g h ↦ by
        ext n s
        dsimp only [φ]
        funext J
        simp
        rfl }
  refine ⟨C, ?_, (fun _ ↦ rfl), ?_⟩
  · constructor
    intro F G g h
    ext n s
    dsimp only [C, φ]
    funext J
    simp
    rfl
  · intro F G g n s J hF hG
    have hF' : hF = (rfl : C.obj F = principalCechTotal r f F) := Subsingleton.elim _ _
    have hG' : hG = (rfl : C.obj G = principalCechTotal r f G) := Subsingleton.elim _ _
    subst hF'
    subst hG'
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl


/-- The alternating total Čech functor with its componentwise action.
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechFunctor := (principalCechFunctor_exists r f).choose

/-- Its chosen objects are the explicitly constructed total complexes.
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechObjIso : (principalCechFunctor r f).obj F ≅ principalCechTotal r f F :=
  eqToIso ((principalCechFunctor_exists r f).choose_spec.choose_spec.1 F)

/-- A singleton Čech row has vertical degree n.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total).
Proof: a singleton has cardinality one, so n + 1 - 1 = n. -/
theorem principalCech_singleton_degree (j : Fin r) (n : ℤ) :
    n = n + 1 - (({j} : Finset (Fin r)).card : ℤ) := by
  simp

private def principalCechAugmentationComponent (n : ℤ) :
    (affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).obj (F.X n) ⟶
      principalCechTerms r f F n := by
  classical
  exact ModuleCat.ofHom (R := A)
    (X := (affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).obj (F.X n))
    (Y := principalCechTerms r f F n)
    (LinearMap.pi fun J ↦ if h : J.val.card = 1 then
      ((modulesSpecToSheaf.obj (F.X (n + 1 - (J.val.card : ℤ)))).obj.map
        (homOfLE (show principalCechIntersection r f J.val ≤
            ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i) by
          obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
          rw [hj]
          exact principalCechIntersection_singleton_le r f j)).op).hom.comp
        ((affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).map
          (eqToHom (congrArg F.X (show n = n + 1 - (J.val.card : ℤ) by omega)))).hom
      else 0)

private theorem principalCechAugmentationComponent_one (n : ℤ)
    (s : (affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).obj (F.X n))
    (J : {J : Finset (Fin r) // J.Nonempty}) (h : J.val.card = 1)
    (hle : principalCechIntersection r f J.val ≤
      ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))
    (he : n = n + 1 - (J.val.card : ℤ)) :
    principalCechAugmentationComponent r f F n s J =
      (modulesSpecToSheaf.obj (F.X (n + 1 - (J.val.card : ℤ)))).obj.map
        (homOfLE hle).op
        ((affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).map
          (eqToHom (congrArg F.X he)) s) := by
  classical
  change (if h : J.val.card = 1 then _ else (0 : _ →ₗ[A] _)) s = _
  rw [dite_eq_left h]
  rfl

private theorem principalCechAugmentationComponent_large (n : ℤ)
    (s : (affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).obj (F.X n))
    (J : {J : Finset (Fin r) // J.Nonempty}) (h : 1 < J.val.card) :
    principalCechAugmentationComponent r f F n s J = 0 := by
  classical
  change (if h : J.val.card = 1 then _ else (0 : _ →ₗ[A] _)) s = 0
  rw [dite_eq_right (ne_of_gt h)]
  rfl

private theorem principalCech_transport_restriction_d
    (U V : (Spec (.of A)).Opens) (hle : V ≤ U)
    (a b c d : ℤ) (e : a = c) (e' : b = d) :
    (affineOpenSections A U).map (eqToHom (congrArg F.X e)) ≫
        (modulesSpecToSheaf.obj (F.X c)).obj.map (homOfLE hle).op ≫
        (affineOpenSections A V).map (F.d c d) =
      (affineOpenSections A U).map (F.d a b) ≫
        (affineOpenSections A U).map (eqToHom (congrArg F.X e')) ≫
        (modulesSpecToSheaf.obj (F.X d)).obj.map (homOfLE hle).op := by
  subst c d
  change (𝟙 _ ≫ _) = (_ ≫ 𝟙 _ ≫ _)
  simp only [Category.id_comp]
  exact (modulesSpecToSheaf.map (F.d a b)).hom.naturality (homOfLE hle).op

private theorem principalCech_transport_two_restrictions
    (U V W : (Spec (.of A)).Opens) (hVU : V ≤ U) (hWV : W ≤ V)
    (a b c : ℤ) (e : a = b) (e' : b = c) :
    (affineOpenSections A U).map (eqToHom (congrArg F.X e)) ≫
        (modulesSpecToSheaf.obj (F.X b)).obj.map (homOfLE hVU).op ≫
        (affineOpenSections A V).map (eqToHom (congrArg F.X e')) ≫
        (modulesSpecToSheaf.obj (F.X c)).obj.map (homOfLE hWV).op =
      (affineOpenSections A U).map (eqToHom (congrArg F.X (e.trans e'))) ≫
        (modulesSpecToSheaf.obj (F.X c)).obj.map (homOfLE (hWV.trans hVU)).op := by
  subst b c
  change (𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _) = (𝟙 _ ≫ _)
  simp only [Category.id_comp]
  exact ((modulesSpecToSheaf.obj (F.X a)).obj.map_comp
    (homOfLE hVU).op (homOfLE hWV).op).symm

-- The pair calculation contains several dependent transports of section modules.
private theorem principalCechAugmentationComponent_comm (n : ℤ) :
    principalCechAugmentationComponent r f F n ≫
        (principalCechTotal r f F).d n (n + 1) =
      (affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).map
        (F.d n (n + 1)) ≫
          principalCechAugmentationComponent r f F (n + 1) := by
  classical
  ext s
  simp only [principalCechTotal, CochainComplex.of_d, ModuleCat.comp_apply]
  change (principalCechDifferential_exists r f F n).choose
      (principalCechAugmentationComponent r f F n s) = _
  rw [(principalCechDifferential_exists r f F n).choose_spec]
  funext J
  by_cases h1 : J.val.card = 1
  · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h1
    rcases J with ⟨J, hJ⟩
    dsimp at hj
    subst J
    simp only [principalCechDifferentialValue, id_eq]
    let v := (-1 : A) ^ (({j} : Finset (Fin r)).card - 1) •
      (affineOpenSections A (principalCechIntersection r f {j})).map
        (F.d (n + 1 - (({j} : Finset (Fin r)).card : ℤ))
          ((n + 1) + 1 - (({j} : Finset (Fin r)).card : ℤ)))
        (principalCechAugmentationComponent r f F n s ⟨{j}, hJ⟩)
    trans v + 0
    · apply congrArg (fun x ↦ v + x)
      apply Finset.sum_eq_zero
      intro k _
      split
      next h =>
        exfalso
        have hk : k.val = j := Finset.mem_singleton.mp k.property
        have he : ({j} : Finset (Fin r)).erase k.val = ∅ := by simp [hk]
        exact h.ne_empty he
      next => rfl
    · dsimp only [v]
      rw [add_zero]
      rw [principalCechAugmentationComponent_one r f F n s _ h1
        (principalCechIntersection_singleton_le r f j) (principalCech_singleton_degree r j n)]
      rw [principalCechAugmentationComponent_one r f F (n + 1)
        ((affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).map
          (F.d n (n + 1)) s) _ h1
        (principalCechIntersection_singleton_le r f j)
        (principalCech_singleton_degree r j (n + 1))]
      have hp : ({j} : Finset (Fin r)).card - 1 = 0 := by simp
      rw [hp, pow_zero, one_smul]
      exact ConcreteCategory.congr_hom
        (principalCech_transport_restriction_d F _ _
          (principalCechIntersection_singleton_le r f j) n (n + 1) _ _
          (principalCech_singleton_degree r j n)
          (principalCech_singleton_degree r j (n + 1))) s
  · have hlarge : 1 < J.val.card := by
      have := J.property.card_pos
      omega
    by_cases h2 : J.val.card = 2
    · obtain ⟨a, b, hab, hJ⟩ := Finset.card_eq_two.mp h2
      have hs : ∃ a b : Fin r, a < b ∧ J.val = {a, b} := by
        rcases lt_or_gt_of_ne hab with hlt | hgt
        · exact ⟨a, b, hlt, hJ⟩
        · exact ⟨b, a, hgt, hJ.trans (Finset.pair_comm a b)⟩
      obtain ⟨a, b, hab, hJ⟩ := hs
      rcases J with ⟨J, hne⟩
      dsimp at hJ
      subst J
      let a' : ({a, b} : Finset (Fin r)) := ⟨a, by simp⟩
      let b' : ({a, b} : Finset (Fin r)) := ⟨b, by simp⟩
      have hu : (Finset.univ : Finset ({a, b} : Finset (Fin r))) = {a', b'} := by
        ext x
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        rcases Finset.mem_insert.mp x.property with hx | hx
        · exact Or.inl (Subtype.ext hx)
        · exact Or.inr (Subtype.ext (Finset.mem_singleton.mp hx))
      simp only [principalCechDifferentialValue, id_eq]
      rw [principalCechAugmentationComponent_large r f F n s _ hlarge,
        principalCechAugmentationComponent_large r f F (n + 1) _ _ hlarge]
      simp only [map_zero, smul_zero, zero_add]
      rw [hu, Finset.sum_pair (show a' ≠ b' from fun h ↦ hab.ne (congrArg Subtype.val h))]
      dsimp only [a', b']
      have hea : ({a, b} : Finset (Fin r)).erase a = {b} := by simp [hab.ne]
      have heb : ({a, b} : Finset (Fin r)).erase b = {a} := by
        rw [Finset.pair_comm]
        simp [hab.ne']
      have hna : (({a, b} : Finset (Fin r)).erase a).Nonempty := by simp [hea]
      have hnb : (({a, b} : Finset (Fin r)).erase b).Nonempty := by simp [heb]
      rw [dite_eq_left hna, dite_eq_left hnb]
      have hca : (({a, b} : Finset (Fin r)).erase a).card = 1 := by simp [hea]
      have hcb : (({a, b} : Finset (Fin r)).erase b).card = 1 := by simp [heb]
      have hlea : principalCechIntersection r f (({a, b} : Finset (Fin r)).erase a) ≤
          ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i) := by
        rw [hea]
        exact principalCechIntersection_singleton_le r f b
      have hleb : principalCechIntersection r f (({a, b} : Finset (Fin r)).erase b) ≤
          ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i) := by
        rw [heb]
        exact principalCechIntersection_singleton_le r f a
      have hda : n = n + 1 - ((({a, b} : Finset (Fin r)).erase a).card : ℤ) := by
        rw [hca]
        omega
      have hdb : n = n + 1 - ((({a, b} : Finset (Fin r)).erase b).card : ℤ) := by
        rw [hcb]
        omega
      rw [principalCechAugmentationComponent_one r f F n s
        ⟨({a, b} : Finset (Fin r)).erase a, hna⟩ hca hlea hda]
      rw [principalCechAugmentationComponent_one r f F n s
        ⟨({a, b} : Finset (Fin r)).erase b, hnb⟩ hcb hleb hdb]
      have ha := ConcreteCategory.congr_hom
        (principalCech_transport_two_restrictions F _ _ _ hlea
          (principalCechIntersection_erase_le r f {a, b} a) n _ _ hda
          (principalCech_erase_degree r {a, b} a (by simp) n)) s
      have hb := ConcreteCategory.congr_hom
        (principalCech_transport_two_restrictions F _ _ _ hleb
          (principalCechIntersection_erase_le r f {a, b} b) n _ _ hdb
          (principalCech_erase_degree r {a, b} b (by simp) n)) s
      simp only [ModuleCat.comp_apply] at ha hb
      have ht : n = n + 1 + 1 - (({a, b} : Finset (Fin r)).card : ℤ) := by
        rw [show ({a, b} : Finset (Fin r)).card = 2 from h2]
        omega
      let t := (modulesSpecToSheaf.obj
          (F.X (n + 1 + 1 - (({a, b} : Finset (Fin r)).card : ℤ)))).obj.map
        (homOfLE ((principalCechIntersection_erase_le r f {a, b} a).trans hlea)).op
        ((affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).map
          (eqToHom (congrArg F.X ht)) s)
      trans (-1 : A) ^ (({a, b} : Finset (Fin r)).filter (fun x ↦ x < a)).card • t +
        (-1 : A) ^ (({a, b} : Finset (Fin r)).filter (fun x ↦ x < b)).card • t
      · exact congrArg₂ (· + ·)
          (congrArg (fun x ↦ (-1 : A) ^
            (({a, b} : Finset (Fin r)).filter (fun x ↦ x < a)).card • x) ha)
          (congrArg (fun x ↦ (-1 : A) ^
            (({a, b} : Finset (Fin r)).filter (fun x ↦ x < b)).card • x) hb)
      have hpa : (({a, b} : Finset (Fin r)).filter (fun x ↦ x < a)).card = 0 := by
        simp [Finset.filter_insert, Finset.filter_singleton, hab.not_gt]
      have hpb : (({a, b} : Finset (Fin r)).filter (fun x ↦ x < b)).card = 1 := by
        simp [Finset.filter_insert, Finset.filter_singleton, hab]
      rw [hpa, hpb, pow_zero, one_smul, pow_one, neg_one_smul]
      exact add_neg_cancel _
    · simp only [principalCechDifferentialValue, id_eq]
      rw [principalCechAugmentationComponent_large r f F n s _ hlarge,
        principalCechAugmentationComponent_large r f F (n + 1) _ _ hlarge]
      simp only [map_zero, smul_zero, zero_add]
      apply Finset.sum_eq_zero
      intro j _
      split
      next h =>
        have hj : 1 < (J.val.erase j.val).card := by
          have := Finset.card_erase_add_one j.property
          omega
        rw [principalCechAugmentationComponent_large r f F n s _ hj]
        simp only [map_zero, smul_zero]
      next => rfl

private theorem principalCech_transport_restriction_map
    {G : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ}
    (g : F ⟶ G) (U V : (Spec (.of A)).Opens) (hle : V ≤ U)
    (a b : ℤ) (e : a = b) :
    (affineOpenSections A U).map (g.f a) ≫
        (affineOpenSections A U).map (eqToHom (congrArg G.X e)) ≫
        (modulesSpecToSheaf.obj (G.X b)).obj.map (homOfLE hle).op =
      (affineOpenSections A U).map (eqToHom (congrArg F.X e)) ≫
        (modulesSpecToSheaf.obj (F.X b)).obj.map (homOfLE hle).op ≫
        (affineOpenSections A V).map (g.f b) := by
  subst b
  change (_ ≫ 𝟙 _ ≫ _) = (𝟙 _ ≫ _)
  simp only [Category.id_comp]
  exact ((modulesSpecToSheaf.map (g.f a)).hom.naturality (homOfLE hle).op).symm

/-- The augmentation from sections of U to alternating Čech cochains.
It is restriction on singleton rows and zero on larger subsets.
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total).
Proof: the restrictions agree on pairwise intersections, so their alternating
horizontal differential vanishes; restrictions also commute with d_F.
This gives a chain map, natural in the coefficient complex. -/
theorem principalCechAugmentation_exists :
    ∃ α : (affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶ principalCechFunctor r f,
      (∀ (F : CochainComplex
        (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (n : ℤ)
        (s : (affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).obj (F.X n))
        (j : Fin r),
        ((α.app F ≫ (principalCechObjIso r f F).hom).f n) s ⟨{j}, by simp⟩ =
          (modulesSpecToSheaf.obj
            (F.X (n + 1 - (({j} : Finset (Fin r)).card : ℤ)))).obj.map
              (homOfLE (principalCechIntersection_singleton_le r f j)).op
              ((affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).map
                (eqToHom (congrArg F.X (principalCech_singleton_degree r j n))) s)) ∧
      (∀ (F : CochainComplex
        (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (n : ℤ)
        (s : (affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).obj (F.X n))
        (J : {J : Finset (Fin r) // J.Nonempty}), 1 < J.val.card →
          ((α.app F ≫ (principalCechObjIso r f F).hom).f n) s J = 0) := by
  classical
  let a (F : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
      ((affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj F ⟶ principalCechTotal r f F :=
    CochainComplex.ofHom (principalCechAugmentationComponent r f F)
      (principalCechAugmentationComponent_comm r f F)
  let α : (affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).mapHomologicalComplex
      (ComplexShape.up ℤ) ⟶ principalCechFunctor r f :=
    { app F := a F ≫ (principalCechObjIso r f F).inv
      naturality := by
        intro F G g
        apply (cancel_mono (principalCechObjIso r f G).hom).mp
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        ext n s
        funext J
        change principalCechAugmentationComponent r f G n
            ((affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).map
              (g.f n) s) J =
          (((principalCechObjIso r f F).inv ≫ (principalCechFunctor r f).map g ≫
            (principalCechObjIso r f G).hom).f n)
              (principalCechAugmentationComponent r f F n s) J
        trans (affineOpenSections A (principalCechIntersection r f J.val)).map
          (g.f (n + 1 - (J.val.card : ℤ)))
            (principalCechAugmentationComponent r f F n s J)
        swap
        · exact ((principalCechFunctor_exists r f).choose_spec.choose_spec.2 F G g n
            (principalCechAugmentationComponent r f F n s) J
            ((principalCechFunctor_exists r f).choose_spec.choose_spec.1 F)
            ((principalCechFunctor_exists r f).choose_spec.choose_spec.1 G)).symm
        by_cases h : J.val.card = 1
        · have hle : principalCechIntersection r f J.val ≤
              ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i) := by
            obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
            rw [hj]
            exact principalCechIntersection_singleton_le r f j
          have he : n = n + 1 - (J.val.card : ℤ) := by rw [h]; omega
          rw [principalCechAugmentationComponent_one r f G n _ J h hle he,
            principalCechAugmentationComponent_one r f F n s J h hle he]
          exact ConcreteCategory.congr_hom
            (principalCech_transport_restriction_map F g _ _ hle n _ he) s
        · have hlarge : 1 < J.val.card := by
            have := J.property.card_pos
            omega
          rw [principalCechAugmentationComponent_large r f G n _ J hlarge,
            principalCechAugmentationComponent_large r f F n s J hlarge]
          exact (map_zero _).symm }
  refine ⟨α, ?_, ?_⟩
  · intro F n s j
    change (((a F ≫ (principalCechObjIso r f F).inv) ≫
      (principalCechObjIso r f F).hom).f n) s ⟨{j}, by simp⟩ = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact principalCechAugmentationComponent_one r f F n s _ (Finset.card_singleton j)
      (principalCechIntersection_singleton_le r f j) (principalCech_singleton_degree r j n)
  · intro F n s J h
    change (((a F ≫ (principalCechObjIso r f F).inv) ≫
      (principalCechObjIso r f F).hom).f n) s J = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact principalCechAugmentationComponent_large r f F n s J h

/-- The canonical restriction augmentation.
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechAugmentation := (principalCechAugmentation_exists r f).choose

/-- On a K-injective complex, the Čech augmentation is a quasi-isomorphism.
Source: Stacks, Cohomology, Tag 08C2 (blueprint: def-sc-principal-open-alternating-total).
Proof: resolve by injectives and use the augmented Čech contraction locally on a cover
member. Sections of injective module sheaves are Čech-acyclic. A finite cover gives a
bounded horizontal direction; totalization therefore preserves the columnwise comparison,
including unbounded vertical complexes. K-injective replacement identifies the result
with derived sections, and the section-to-Čech augmentation is the displayed comparison. -/
theorem principalCechAugmentation_quasiIso
    (J : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) [J.IsKInjective] :
    QuasiIso ((principalCechAugmentation r f).app J) := by
  classical
  let V : (Spec (.of A)).Opens := ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)
  let K := ((affineOpenSections A V).mapHomologicalComplex (ComplexShape.up ℤ)).obj J
  let T := (principalCechFunctor r f).obj J
  let σ (n : ℤ) : K.X n ≅ (modulesSpecToSheaf.obj (J.X n)).obj.obj (op V) :=
    Iso.refl _
  let τ (n : ℤ) : T.X n ≅ principalCechTerms r f J n :=
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) n).mapIso
    (principalCechObjIso r f J)
  let α : K ⟶ T := (principalCechAugmentation r f).app J
  have hls (S : {S : Finset (Fin r) // S.Nonempty}) (h : S.val.card = 1) :
      principalCechIntersection r f S.val ≤ V := by
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
    rw [hj]
    exact principalCechIntersection_singleton_le r f j
  have hes (S : {S : Finset (Fin r) // S.Nonempty}) (h : S.val.card = 1) (n : ℤ) :
      n = n + 1 - (S.val.card : ℤ) := by rw [h]; omega
  have hd (n : ℤ) (s : T.X n) (S : {S : Finset (Fin r) // S.Nonempty}) :
      (τ (n + 1)).hom (T.d n (n + 1) s) S =
        principalCechDifferentialValue r f J n ((τ n).hom s) S := by
    have h := ConcreteCategory.congr_hom ((principalCechObjIso r f J).hom.comm n (n + 1)) s
    simp only [ModuleCat.comp_apply, principalCechTotal, CochainComplex.of_d] at h
    change principalCechDifferential r f J n ((τ n).hom s) =
      (τ (n + 1)).hom (T.d n (n + 1) s) at h
    rw [← h]
    exact congrFun ((principalCechDifferential_exists r f J n).choose_spec ((τ n).hom s)) S
  have ha (n : ℤ) (s : K.X n) (S : {S : Finset (Fin r) // S.Nonempty}) :
      (τ n).hom (α.f n s) S = if h : S.val.card = 1 then
        (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
          (homOfLE (hls S h)).op
          ((affineOpenSections A V).map (eqToHom (congrArg J.X (hes S h n))) s)
        else 0 := by
    change ((α ≫ (principalCechObjIso r f J).hom).f n) s S = _
    by_cases h : S.val.card = 1
    · rw [dite_eq_left h]
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
      rcases S with ⟨S, hS⟩
      dsimp only at hj
      subst S
      exact (principalCechAugmentation_exists r f).choose_spec.1 J n s j
    · rw [dite_eq_right h]
      have hlarge : 1 < S.val.card := by
        have := S.property.card_pos
        omega
      exact (principalCechAugmentation_exists r f).choose_spec.2 J n s S hlarge
  apply (quasiIso_iff _).2
  intro n
  apply (quasiIsoAt_iff_isIso_homologyMap _ n).2
  have hmono : Mono (HomologicalComplex.homologyMap α n) :=
    principalOpenCech_homology_injective A r f J K T σ τ α
      (principalCechIntersection_erase_le r f) hls (principalCech_erase_degree r) hes
      (fun _ _ ↦ rfl) hd ha n
  have hepi : Epi (HomologicalComplex.homologyMap α n) :=
    principalOpenCech_homology_surjective A r f J K T σ τ α
      (principalCechIntersection_erase_le r f) hls (principalCech_erase_degree r) hes
      (fun _ _ ↦ rfl) hd ha n
  exact isIso_of_mono_of_epi _

variable [HasDerivedCategory.{wC}
  (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace))]
  [HasDerivedCategory.{vC} (ModuleCat.{uC} A)]

private def principalCechSectionsDerivedUnit
    (U : (Spec (.of A)).Opens) :
    (affineOpenSections A U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ (affineOpenSections A U).rightDerivedFunctor :=
  let C := SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)
  let S := affineOpenSections A U
  (Functor.isoWhiskerLeft (S.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (ModuleCat.{uC} A))).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ))
      S.rightDerivedFunctorUnit ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C)
      S.rightDerivedFunctor).hom

private theorem principalCechSectionsDerivedUnit_iso
    (U : (Spec (.of A)).Opens)
    (J : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    [J.IsKInjective] :
    (principalCechSectionsDerivedUnit U).app J =
      ((affineOpenSections A U).rightDerivedFunctorObjQIso J).inv := by
  simp [principalCechSectionsDerivedUnit, Functor.rightDerivedFunctorObjQIso]

/-- The canonical derived Čech comparison, characterized by every K-injective resolution.
Source: Stacks, Tag 08C2 (blueprint: def-sc-principal-open-alternating-total).
Proof: choose F → J a K-injective resolution. Invert the Čech augmentation on J,
which is a quasi-isomorphism by principalCechAugmentation_quasiIso, and identify the
sections of J with the right derived functor using rightDerivedFunctorObjQIso.
The resulting roof is independent of the resolution: maps between K-injective
resolutions and naturality of the augmentation give the displayed commuting square.
Its uniqueness follows since both the resolution and the augmentation become invertible. -/
theorem principalCechDerivedComparison_exists :
    ∃ β : DerivedCategory.Q.obj ((principalCechFunctor r f).obj F) ⟶
      (affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj F),
      ∀ (J : CochainComplex
        (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
        [J.IsKInjective] (i : F ⟶ J) [QuasiIso i],
        β ≫
          (affineOpenSections A (⨆ i, PrimeSpectrum.basicOpen (f i))).rightDerivedFunctor.map
            (DerivedCategory.Q.map i) ≫
          ((affineOpenSections A (⨆ i, PrimeSpectrum.basicOpen (f i))).rightDerivedFunctorObjQIso
            J).hom ≫ DerivedCategory.Q.map ((principalCechAugmentation r f).app J) =
          DerivedCategory.Q.map ((principalCechFunctor r f).map i) := by
  let C := SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)
  let S := affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))
  let I := CochainComplex.kInjectiveResolutionFunctor.{uC} C
  let η := CochainComplex.toKInjectiveResolution.{uC} C
  let T := S.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  let B := principalCechFunctor r f ⋙ DerivedCategory.Q
  let D := DerivedCategory.Q ⋙ S.rightDerivedFunctor
  let a : T ⟶ B := Functor.whiskerRight (principalCechAugmentation r f) DerivedCategory.Q
  let b : T ⟶ D := principalCechSectionsDerivedUnit _
  let ai := Functor.whiskerLeft I a
  let d := Functor.whiskerRight η D
  have hη (K : CochainComplex C ℤ) : QuasiIso (η.app K) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{uC} C K).2
  have hai : IsIso ai := by
    have (K : CochainComplex C ℤ) : IsIso (ai.app K) := by
      change IsIso (DerivedCategory.Q.map ((principalCechAugmentation r f).app (I.obj K)))
      have := principalCechAugmentation_quasiIso r f (I.obj K)
      infer_instance
    exact NatIso.isIso_of_isIso_app ai
  have haI (K : CochainComplex C ℤ) : IsIso (a.app (I.obj K)) := by
    change IsIso (ai.app K)
    infer_instance
  have hd : IsIso d := by
    have (K : CochainComplex C ℤ) : IsIso (d.app K) := by
      have := hη K
      change IsIso (S.rightDerivedFunctor.map (DerivedCategory.Q.map (η.app K)))
      infer_instance
    exact NatIso.isIso_of_isIso_app d
  let β : B ⟶ D := Functor.whiskerRight η B ≫ inv ai ≫
    Functor.whiskerLeft I b ≫ inv d
  have hab (K : CochainComplex C ℤ) : a.app K ≫ β.app K = b.app K := by
    have := haI K
    apply (cancel_mono (d.app K)).mp
    simp only [β, NatTrans.comp_app, NatIso.isIso_inv_app]
    change (a.app K ≫
        (B.map (η.app K) ≫ inv (a.app (I.obj K)) ≫ b.app (I.obj K) ≫ inv (d.app K))) ≫
          d.app K = b.app K ≫ d.app K
    calc
      _ = (a.app K ≫ B.map (η.app K)) ≫ inv (a.app (I.obj K)) ≫
          b.app (I.obj K) := by simp [Category.assoc]
      _ = (T.map (η.app K) ≫ a.app (I.obj K)) ≫ inv (a.app (I.obj K)) ≫
          b.app (I.obj K) := by rw [a.naturality]; rfl
      _ = T.map (η.app K) ≫ b.app (I.obj K) := by simp [Category.assoc]
      _ = b.app K ≫ d.app K := b.naturality (η.app K)
  refine ⟨β.app F, ?_⟩
  intro J _ i _
  have haJ : IsIso (a.app J) := by
    have := principalCechAugmentation_quasiIso r f J
    change IsIso (DerivedCategory.Q.map ((principalCechAugmentation r f).app J))
    infer_instance
  have hbJ : b.app J = (S.rightDerivedFunctorObjQIso J).inv :=
    principalCechSectionsDerivedUnit_iso _ J
  have he : β.app J ≫ (S.rightDerivedFunctorObjQIso J).hom ≫ a.app J = 𝟙 _ := by
    apply (cancel_epi (a.app J)).mp
    simp only [← Category.assoc, hab J, hbJ, Iso.inv_hom_id,
      Category.id_comp, Category.comp_id]
  change β.app F ≫ D.map i ≫ (S.rightDerivedFunctorObjQIso J).hom ≫ a.app J = B.map i
  rw [← Category.assoc, ← Category.assoc, ← β.naturality i]
  simp only [Category.assoc, he, Category.comp_id]

/-- The canonical map Tot(Č_alt(U,F)) → RΓ(U,F), as a roof through a K-injective resolution.
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechDerivedComparison :
    DerivedCategory.Q.obj ((principalCechFunctor r f).obj F) ⟶
      (affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj F) :=
  (principalCechDerivedComparison_exists r f F).choose

end
end AlgebraicGeometry
