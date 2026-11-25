/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # PrincipalOpenCechSignedComplex

Source: Stacks Project, Cohomology, Tag 08C1.
(blueprint: lem-sc-principal-open-cech-signed-complex).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

namespace CoordinateConstruction
noncomputable section

variable (A : Type u) [CommRing A]

/-- Sections on an affine scheme, with the A-action supplied by Mathlib's
`modulesSpecToSheaf`. Source: Stacks, Tag 08D2
(blueprint: def-sc-principal-open-alternating-total). -/
private def affineOpenSections (U : (Spec (.of A)).Opens) :
    SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤ ModuleCat.{u} A where
  obj F := (modulesSpecToSheaf.obj F).obj.obj (op U)
  map g := (modulesSpecToSheaf.map g).hom.app (op U)
  map_id F := congrArg (fun g ↦ g.hom.app (op U)) (modulesSpecToSheaf.map_id F)
  map_comp g h := congrArg (fun g ↦ g.hom.app (op U)) (modulesSpecToSheaf.map_comp g h)

/-- Sections are additive, including after restriction of scalars from Γ(U,O).
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total).
Proof: sheaf-module morphisms add sectionwise, and evaluation and restriction of scalars
preserve their addition. -/
private theorem affineOpenSections_additive_proof (U : (Spec (.of A)).Opens) :
    (affineOpenSections A U).Additive := by
  constructor
  intro F G g h
  rfl

/-- The additive instance for A-module sections.
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total). -/
private instance affineOpenSections_additive (U : (Spec (.of A)).Opens) :
    (affineOpenSections A U).Additive := affineOpenSections_additive_proof A U

variable {A} (r : ℕ) (f : Fin r → A)

/-- The intersection belonging to a finite subset of cover indices.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total). -/
private def principalCechIntersection (J : Finset (Fin r)) : (Spec (.of A)).Opens :=
  PrimeSpectrum.basicOpen (∏ j ∈ J, f j)

/-- Erasing an index enlarges a principal intersection.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total).
Proof: the product for J is the erased product times f_j. Its basic open is their
intersection, hence contained in the erased basic open. -/
private theorem principalCechIntersection_erase_le (J : Finset (Fin r)) (j : Fin r) :
    principalCechIntersection r f J ≤ principalCechIntersection r f (J.erase j) := by
  classical
  unfold principalCechIntersection
  by_cases hj : j ∈ J
  · rw [← Finset.mul_prod_erase J f hj]
    exact PrimeSpectrum.basicOpen_mul_le_right _ _
  · simp [Finset.erase_eq_of_notMem hj]

/-- Deleting an index gives the same vertical degree in the incoming horizontal row.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total).
Proof: card(J.erase j) = card(J)-1 when j belongs to J; subtract this identity in ℤ. -/
private theorem principalCech_erase_degree (J : Finset (Fin r)) (j : Fin r) (hj : j ∈ J) (n : ℤ) :
    n + 1 - ((J.erase j).card : ℤ) = (n + 1) + 1 - (J.card : ℤ) := by
  have h := Finset.card_erase_add_one hj
  omega

variable (F : CochainComplex
  (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

/-- Total Čech cochains, with row p = card(J)-1 and vertical degree n-p.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total). -/
private def principalCechTerms (n : ℤ) : ModuleCat.{u} A :=
  ModuleCat.of A (∀ J : {J : Finset (Fin r) // J.Nonempty},
    (affineOpenSections A (principalCechIntersection r f J.val)).obj
      (F.X (n + 1 - (J.val.card : ℤ))))

/-- The signed total differential: alternating horizontal restriction and
`(-1)^p d_F` in row p. Empty erased subsets contribute zero.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total). -/
private def principalCechDifferentialValue (n : ℤ) (s : principalCechTerms r f F n) :
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
private theorem principalCechDifferential_exists (n : ℤ) :
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
private def principalCechDifferential (n : ℤ) :
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

private theorem deletion_sign {A : Type u} [CommRing A] {r : ℕ} (S : Finset (Fin r))
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

private theorem alternating_erase_sum {A : Type u} [CommRing A]
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

private theorem transport_two_restrictions {A : Type u} [CommRing A]
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
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

private noncomputable def doubleTerm {A : Type u} [CommRing A]
    (r : ℕ) (f : Fin r → A)
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
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
private theorem principalCechHorizontalValue_square {A : Type u} [CommRing A]
    (r : ℕ) (f : Fin r → A)
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
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

private theorem transport_restriction_d {A : Type u} [CommRing A]
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
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
private theorem principalCechValue_mixed_cancel {A : Type u} [CommRing A] (r : ℕ) (f : Fin r → A)
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
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
private theorem principalCechDifferential_square (n : ℤ) :
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
private def principalCechTotal : CochainComplex (ModuleCat.{u} A) ℤ :=
  CochainComplex.of (principalCechTerms r f F) (principalCechDifferential r f F)
    (principalCechDifferential_square r f F)

end
end CoordinateConstruction

/-- A separate construction step for the finite subset Čech argument.
Source: Stacks Project, Cohomology, Tag 08C1, equation (20.40.0.1).
(blueprint: lem-sc-principal-open-cech-signed-complex).

Proof: Construct degree n as the product of sections in degree n+1-card(S). Each vertical
and restriction summand is A-linear, so the displayed formula defines a linear map.
The vertical square is zero by the coefficient complex equation. In the horizontal
square, pair deletion of distinct indices in the two orders: the restrictions and
degree transports agree, while their signs are opposite. Empty deletions vanish.
The mixed terms cancel by naturality of the coefficient differential under
restriction and the change of the vertical sign when one index is deleted.
Apply CochainComplex.of to these consecutive linear maps; take τ₁ to be identity.
For r=0 the product is empty and each equation is vacuous. -/
theorem principalOpenCech_signed_complex_exists
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀
      (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ)),
      ∃ (T₁ : CochainComplex (ModuleCat.{u} A) ℤ)
      (τ₁ : ∀ n : ℤ, T₁.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (I.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val)))),
      (∀ (n : ℤ) (s : T₁.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ₁ (n + 1)).hom (T₁.d n (n + 1) s) S =
          (-1 : A) ^ (S.val.card - 1) •
            (modulesSpecToSheaf.map
              (I.d (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
                (op (D S.val)) ((τ₁ n).hom s S) +
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (I.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg I.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val))) ((τ₁ n).hom s ⟨S.val.erase j.val, h⟩))
          else 0) := by
  intro D hle he
  refine ⟨CoordinateConstruction.principalCechTotal r f I, fun _ ↦ Iso.refl _, ?_⟩
  intro n s S
  simp only [CoordinateConstruction.principalCechTotal, CochainComplex.of_d]
  change (CoordinateConstruction.principalCechDifferential_exists r f I n).choose s S = _
  rw [(CoordinateConstruction.principalCechDifferential_exists r f I n).choose_spec]
  rfl

end AlgebraicGeometry
