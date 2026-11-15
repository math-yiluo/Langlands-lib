import Langlands.GroupScheme.Rational.PartnerOrbitRootProducts
import Langlands.GroupScheme.Rational.SimpleRootFiberPartners
import Langlands.GroupScheme.Rational.SimpleRootFiberCoordinates
import Langlands.GroupScheme.Rational.SimpleRootFiberCoroot
import Langlands.GroupScheme.Rational.SimpleRootFiberProducts

/-! # Unitary coordinates on the simple-root fiber of a multipliable relative root -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme.AffineCharacterTowerDescent

namespace Langlands.GroupScheme

namespace SplitPinning.PartnerData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G} {O : Set p.base.support} (D : PartnerData O)
  {n : ℕ} (e : D.orientation ≃ Fin n)

/-- Reversal of the positions inside each piece. -/
def pieceRev (k' : Fin (n * 3)) : Fin (n * 3) :=
  finProdFinEquiv ((finProdFinEquiv.symm k').1, Fin.rev (finProdFinEquiv.symm k').2)

theorem pieceRev_pieceRev (k' : Fin (n * 3)) : pieceRev (pieceRev k') = k' := by
  simp only [pieceRev, Equiv.symm_apply_apply, Fin.rev_rev, Prod.mk.eta, Equiv.apply_symm_apply]

/-- The lower pieces are the negatives of the reversed upper pieces. -/
theorem lowerPieceEnum_eq_neg (k' : Fin (n * 3)) :
    D.lowerPieceEnum e k' = -D.upperPieceEnum e (pieceRev k') := by
  simp only [lowerPieceEnum, upperPieceEnum, pieceRev, Equiv.symm_apply_apply]
  generalize finProdFinEquiv.symm k' = q
  obtain ⟨l, c⟩ := q
  fin_cases c <;> rfl

theorem mem_range_lowerPieceEnum_iff (χ : characterLattice p.torus) :
    χ ∈ Set.range (D.lowerPieceEnum e) ↔ -χ ∈ Set.range (D.upperPieceEnum e) := by
  constructor
  · rintro ⟨k', rfl⟩
    exact ⟨pieceRev k', by rw [lowerPieceEnum_eq_neg, neg_neg]⟩
  · rintro ⟨k', hk'⟩
    refine ⟨pieceRev k', ?_⟩
    rw [lowerPieceEnum_eq_neg, pieceRev_pieceRev, hk', neg_neg]

theorem lowerPieceEnum_injective (h : Function.Injective (D.upperPieceEnum e)) :
    Function.Injective (D.lowerPieceEnum e) := by
  intro k₁ k₂ h₁₂
  rw [lowerPieceEnum_eq_neg, lowerPieceEnum_eq_neg, neg_inj] at h₁₂
  rw [← pieceRev_pieceRev k₁, ← pieceRev_pieceRev k₂, h h₁₂]

/-- The sums of the pieces are pairwise distinct: pairing with the coroot of `r` gives `1` on
the piece of `r` and `0` on the others. -/
theorem doubleRoot_injective : Function.Injective (D.doubleRoot e) := by
  intro l₁ l₂ h
  by_contra hne
  set r₁ : p.base.support := (e.symm l₁).1 with hr₁
  set r₂ : p.base.support := (e.symm l₂).1 with hr₂
  have h1O : r₁ ∈ O := D.mem_of_mem_orientation (e.symm l₁).2
  have h2O : r₂ ∈ O := D.mem_of_mem_orientation (e.symm l₂).2
  have hne' : r₂ ≠ r₁ := by
    intro h'
    apply hne
    rw [← e.apply_symm_apply l₁, ← e.apply_symm_apply l₂]
    exact congrArg e (Subtype.ext h'.symm)
  have hp1 : D.partner r₁ ∉ D.orientation := (D.mem_orientation_iff h1O).mp (e.symm l₁).2
  have hp2 : D.partner r₂ ∉ D.orientation := (D.mem_orientation_iff h2O).mp (e.symm l₂).2
  have o1 : p.rootDatum.IsOrthogonal r₁ r₂ :=
    D.orthogonal r₁ h1O r₂ h2O hne' (fun h' => hp1 (h' ▸ (e.symm l₂).2))
  have o2 : p.rootDatum.IsOrthogonal r₁ (D.partner r₂) := by
    refine D.orthogonal r₁ h1O _ (D.mem r₂ h2O) (fun h' => hp2 (h' ▸ (e.symm l₁).2)) ?_
    intro h'
    apply hne'
    rw [← D.partner_partner r₂ h2O, h', D.partner_partner r₁ h1O]
  have hc := congrArg (fun χ => p.rootDatum.toLinearMap χ (p.rootDatum.coroot r₁)) h
  simp only [doubleRoot, map_add, LinearMap.add_apply, RootPairing.root_coroot_eq_pairing] at hc
  rw [← hr₁, ← hr₂, RootPairing.pairing_same, (D.pairing r₁ h1O).2, o1.2, o2.2] at hc
  norm_num at hc

end SplitPinning.PartnerData

namespace SimpleRootFiber

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
  (f : S ⟶ T) (j : T.toGrp ⟶ G)

local notation "bK" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange bK) T
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange bK) S
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange bK) G
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange bK) j
local notation "f_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange bK) f

local instance simpleRootFiberUnitaryIsAffineHom : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom bK)
  infer_instance

local instance simpleRootFiberUnitaryFiniteType : LocallyOfFiniteType (G_K).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom bK)
  infer_instance

variable {J : Type u} [Finite J]
  {P : RootDatum J
    (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))}
  (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map j) P)
  (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j))
  (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
  (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
  [P.IsReduced]
  (ν : cocharacterLattice S)
  (hν : IsGenericCocharacter (CommGroupScheme.groupHom f ≫ j) ν)
  [FiniteDimensional k K]
  (hGK : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
  (hi : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map j))
  [IsGalois k K] (hjc : IsClosedSubgroup j)
  {a : characterLattice S} (ha : a ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν)
  (h2a : 2 • a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))

local notation "Dₚ" => fiberPinning k K f j hP hf hcent hT ν hν hGK hi
local notation "Oₐ" => fiberSet k K f j hP hf hcent hT ν hν hGK hi a
local notation "π" => partner k K f j hP hf hcent hT ν hν hGK hi

section Partners

/-- The partner structure on the fiber of a multipliable simple relative root. -/
def fiberPartnerData : SplitPinning.PartnerData (p := (Dₚ).pinning) Oₐ where
  partner := π
  mem _ ht := partner_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht
  partner_partner _ ht := partner_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht
  ne _ ht := partner_ne k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht
  pairing _ ht := pairing_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht
  orthogonal _ ht _ ht' hne hne' :=
    isOrthogonal_of_ne_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht ht' hne hne'

local notation "Dπ" => fiberPartnerData k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a

theorem fiberPartnerData_partner : (Dπ).partner = π := rfl

end Partners

section Enumerations

local notation "Dπ" => fiberPartnerData k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a

include hP hjc ha h2a in
/-- The sum of the roots of a member of the fiber and its partner restricts to `2 • a`, and
is a root. -/
theorem add_partner_mem {t : (Dₚ).pinning.base.support} (ht : t ∈ Oₐ) :
    P.root t.1 + P.root (π t).1 ∈ roots (T := T_K) (G := G_K) j_K ∧
      f_K ≫ (P.root t.1 + P.root (π t).1) = characterLattice.baseChange bK S (2 • a) := by
  obtain ⟨m, hm⟩ := exists_root_eq_add_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht
  have h1 := (mem_fiberSet_iff k K f j hP hf hcent hT ν hν hGK hi a t).mp ht
  have h2 := (mem_fiberSet_iff k K f j hP hf hcent hT ν hν hGK hi a _).mp
    (partner_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht)
  refine ⟨hm ▸ root_mem_roots k K j hP m, ?_⟩
  rw [Preadditive.comp_add]
  change f_K ≫ (Dₚ).pinning.rootDatum.root t + f_K ≫ (Dₚ).pinning.rootDatum.root (π t) = _
  rw [h1, h2, map_nsmul, two_nsmul]


/-- An enumeration of the orientation of the fiber pairs. -/
def fiberOrientationEquiv :
    (Dπ).orientation ≃ Fin (Fintype.card (Dπ).orientation) :=
  Fintype.equivFin _

local notation "eπ" => fiberOrientationEquiv k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a

variable [Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left]
  (hR : HasRelativeRootSystem (CommGroupScheme.groupHom f ≫ j))

omit [Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left] in
include hP hjc ha h2a in
theorem orientation_mem {r : (Dπ).orientation} : (r : (Dₚ).pinning.base.support) ∈ Oₐ :=
  (Dπ).mem_of_mem_orientation r.2

omit [Finite J] [P.IsReduced] [FiniteDimensional k K] [IsGalois k K] in
include hP hf hcent hT ha hR in
/-- A root restricting to a positive multiple of `a` restricts to `a` or `2 • a`. -/
theorem eq_one_or_two_of_restrict (idx : J) {m : ℕ}
    (h : f_K ≫ P.root idx = m • characterLattice.baseChange bK S a) : m = 1 ∨ m = 2 := by
  have hres : restrictCharacter k K f hf.1.1 (P.root idx) = m • a := by
    rw [restrictCharacter_eq_iff, map_nsmul]
    exact h
  have hmem : m • a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) :=
    hres ▸ restrictCharacter_root_mem k K f j hP hf hcent hT idx
  exact hR.eq_one_or_two_of_nsmul_mem ha.1.1 hmem

include hR in
/-- Every root restricting to `a` is the root of a member of the orientation or of its
partner; every root restricting to `2 • a` is the sum for a member of the orientation. -/
theorem mem_range_upperPieceEnum_iff (χ : characterLattice T_K) :
    χ ∈ Set.range ((Dπ).upperPieceEnum eπ) ↔
      (χ ∈ roots j_K ∧ ∃ m : ℕ, 0 < m ∧ f_K ≫ χ = m • characterLattice.baseChange bK S a) := by
  constructor
  · rintro ⟨k', rfl⟩
    obtain ⟨⟨l, c⟩, rfl⟩ := finProdFinEquiv.surjective k'
    rw [SplitPinning.PartnerData.upperPieceEnum_finProd]
    have hr := orientation_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a (r := (eπ).symm l)
    have hpr := partner_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hr
    fin_cases c
    · refine ⟨root_mem_roots k K j hP _, 1, one_pos, ?_⟩
      rw [one_nsmul]
      exact (mem_fiberSet_iff k K f j hP hf hcent hT ν hν hGK hi a _).mp hpr
    · obtain ⟨h1, h2⟩ := add_partner_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hr
      refine ⟨h1, 2, two_pos, ?_⟩
      rw [← map_nsmul]
      exact h2
    · refine ⟨root_mem_roots k K j hP _, 1, one_pos, ?_⟩
      rw [one_nsmul]
      exact (mem_fiberSet_iff k K f j hP hf hcent hT ν hν hGK hi a _).mp hr
  · rintro ⟨hχ, m, hm, hfχ⟩
    obtain ⟨idx, rfl⟩ : χ ∈ Set.range P.root := by
      rw [hP.2.1]
      exact hχ
    rcases eq_one_or_two_of_restrict k K f j hP hf hcent hT ν ha hR idx hfχ with h1 | h2
    · subst h1
      have hres : restrictCharacter k K f hf.1.1 (P.root idx) = a := by
        rw [restrictCharacter_eq_iff, ← one_nsmul (characterLattice.baseChange bK S a)]
        exact hfχ
      obtain ⟨t, ht, hti⟩ := exists_mem_fiberSet k K f j hP hf hcent hT ν hν hGK hi ha idx hres
      by_cases hto : t ∈ (Dπ).orientation
      · refine ⟨finProdFinEquiv (eπ ⟨t, hto⟩, 2), ?_⟩
        rw [SplitPinning.PartnerData.upperPieceEnum_finProd]
        simp [SplitPinning.PartnerData.upperPieceRoot, ← hti]
        rfl
      · have hpo := (Dπ).partner_mem_orientation ht hto
        refine ⟨finProdFinEquiv (eπ ⟨π t, hpo⟩, 0), ?_⟩
        rw [SplitPinning.PartnerData.upperPieceEnum_finProd]
        simp [SplitPinning.PartnerData.upperPieceRoot, fiberPartnerData_partner,
          partner_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht, ← hti]
        rfl
    · subst h2
      have hm2 : f_K ≫ P.root idx = characterLattice.baseChange bK S (2 • a) := by
        rw [map_nsmul]
        exact hfχ
      obtain ⟨t, ht, hsum⟩ := exists_mem_root_eq_add_partner k K f j hP hf hcent hT ν hν hGK hi
        hjc ha h2a idx hm2
      by_cases hto : t ∈ (Dπ).orientation
      · refine ⟨finProdFinEquiv (eπ ⟨t, hto⟩, 1), ?_⟩
        rw [SplitPinning.PartnerData.upperPieceEnum_finProd, hsum]
        simp [SplitPinning.PartnerData.upperPieceRoot, fiberPartnerData_partner]
        rfl
      · have hpo := (Dπ).partner_mem_orientation ht hto
        refine ⟨finProdFinEquiv (eπ ⟨π t, hpo⟩, 1), ?_⟩
        rw [SplitPinning.PartnerData.upperPieceEnum_finProd, hsum, add_comm]
        simp [SplitPinning.PartnerData.upperPieceRoot, fiberPartnerData_partner,
          partner_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht]
        rfl

omit [Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left] in
include hP hjc ha h2a in
/-- The upper piece enumeration is injective. -/
theorem upperPieceEnum_injective : Function.Injective ((Dπ).upperPieceEnum eπ) := by
  have hS : IsSplitTorus S.toGrp := hf.1.1
  have hsep : ∀ x y : (Dₚ).pinning.base.support, x ∈ Oₐ → y ∈ Oₐ →
      P.root x.1 ≠ P.root y.1 + P.root (π y).1 := by
    intro x y hx hy h
    have h1 := (mem_fiberSet_iff k K f j hP hf hcent hT ν hν hGK hi a x).mp hx
    have h2 := (add_partner_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hy).2
    have h3 : characterLattice.baseChange bK S a = characterLattice.baseChange bK S (2 • a) := by
      rw [← h2, ← h]
      exact h1.symm
    have h4 : a = 2 • a := (characterLattice.baseChangeEquiv bK S hS).injective h3
    apply ha.1.1.1
    rw [two_nsmul] at h4
    have h5 : a + a = a + 0 := by rw [add_zero]; exact h4.symm
    exact add_left_cancel h5
  intro k₁ k₂ h
  obtain ⟨⟨l₁, c₁⟩, rfl⟩ := finProdFinEquiv.surjective k₁
  obtain ⟨⟨l₂, c₂⟩, rfl⟩ := finProdFinEquiv.surjective k₂
  rw [SplitPinning.PartnerData.upperPieceEnum_finProd,
    SplitPinning.PartnerData.upperPieceEnum_finProd] at h
  have hr₁ := orientation_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a (r := (eπ).symm l₁)
  have hr₂ := orientation_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a (r := (eπ).symm l₂)
  have hp₁ := partner_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hr₁
  have hp₂ := partner_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hr₂
  have hn₁ : π ((eπ).symm l₁).1 ∉ (Dπ).orientation :=
    ((Dπ).mem_orientation_iff hr₁).mp ((eπ).symm l₁).2
  have hn₂ : π ((eπ).symm l₂).1 ∉ (Dπ).orientation :=
    ((Dπ).mem_orientation_iff hr₂).mp ((eπ).symm l₂).2
  have hl : ((eπ).symm l₁ : (Dₚ).pinning.base.support) = (eπ).symm l₂ → l₁ = l₂ :=
    fun h' => (eπ).symm.injective (Subtype.ext h')
  have hpp₁ := partner_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hr₁
  have hpp₂ := partner_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hr₂
  fin_cases c₁ <;> fin_cases c₂ <;>
    simp only [SplitPinning.PartnerData.upperPieceRoot, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h
  · have e1 : π ((eπ).symm l₁).1 = π ((eπ).symm l₂).1 :=
      Subtype.ext ((Dₚ).pinning.rootDatum.root.injective h)
    have e2 : ((eπ).symm l₁ : (Dₚ).pinning.base.support) = (eπ).symm l₂ := by
      rw [← hpp₁, e1, hpp₂]
    rw [hl e2]
  · exact absurd h (hsep _ _ hp₁ hr₂)
  · have e1 : π ((eπ).symm l₁).1 = ((eπ).symm l₂).1 :=
      Subtype.ext ((Dₚ).pinning.rootDatum.root.injective h)
    exact absurd (e1 ▸ ((eπ).symm l₂).2) hn₁
  · exact absurd h.symm (hsep _ _ hp₂ hr₁)
  · rw [(Dπ).doubleRoot_injective eπ h]
  · exact absurd h.symm (hsep _ _ hr₂ hr₁)
  · have e1 : ((eπ).symm l₁).1 = π ((eπ).symm l₂).1 :=
      Subtype.ext ((Dₚ).pinning.rootDatum.root.injective h)
    exact absurd (e1 ▸ ((eπ).symm l₁).2) hn₂
  · exact absurd h (hsep _ _ hr₁ hr₂)
  · rw [hl (Subtype.ext ((Dₚ).pinning.rootDatum.root.injective h))]

include hR in
/-- The lower piece enumeration lists the roots restricting to positive multiples of `-a`. -/
theorem mem_range_lowerPieceEnum_iff (χ : characterLattice T_K) :
    χ ∈ Set.range ((Dπ).lowerPieceEnum eπ) ↔
      (χ ∈ roots j_K ∧
        ∃ m : ℕ, 0 < m ∧ f_K ≫ χ = m • characterLattice.baseChange bK S (-a)) := by
  rw [SplitPinning.PartnerData.mem_range_lowerPieceEnum_iff,
    mem_range_upperPieceEnum_iff k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR]
  constructor
  · rintro ⟨hχ, m, hm, hfχ⟩
    refine ⟨by simpa using hP.neg_mem_roots hχ, m, hm, ?_⟩
    rw [map_neg, smul_neg, ← hfχ, Preadditive.comp_neg, neg_neg]
  · rintro ⟨hχ, m, hm, hfχ⟩
    refine ⟨hP.neg_mem_roots hχ, m, hm, ?_⟩
    rw [Preadditive.comp_neg, hfχ, map_neg, smul_neg, neg_neg]

include hR in
/-- The sums of the pieces are exactly the roots restricting to positive multiples of
`2 • a`. -/
theorem mem_range_doubleRoot_iff (χ : characterLattice T_K) :
    χ ∈ Set.range ((Dπ).doubleRoot eπ) ↔
      (χ ∈ roots j_K ∧
        ∃ m : ℕ, 0 < m ∧ f_K ≫ χ = m • characterLattice.baseChange bK S (2 • a)) := by
  constructor
  · rintro ⟨l, rfl⟩
    obtain ⟨h1, h2⟩ := add_partner_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a
      (orientation_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a (r := (eπ).symm l))
    exact ⟨h1, 1, one_pos, by rw [one_nsmul]; exact h2⟩
  · rintro ⟨hχ, m, hm, hfχ⟩
    obtain ⟨idx, rfl⟩ : χ ∈ Set.range P.root := by
      rw [hP.2.1]
      exact hχ
    have h2m : f_K ≫ P.root idx = (m * 2) • characterLattice.baseChange bK S a := by
      rw [hfχ, map_nsmul, smul_smul]
    have hm1 : m = 1 := by
      rcases eq_one_or_two_of_restrict k K f j hP hf hcent hT ν ha hR idx h2m with h | h <;>
        omega
    subst hm1
    have hm2 : f_K ≫ P.root idx = characterLattice.baseChange bK S (2 • a) := by
      rw [hfχ, one_nsmul]
    obtain ⟨t, ht, hsum⟩ := exists_mem_root_eq_add_partner k K f j hP hf hcent hT ν hν hGK hi
      hjc ha h2a idx hm2
    by_cases hto : t ∈ (Dπ).orientation
    · refine ⟨eπ ⟨t, hto⟩, ?_⟩
      rw [hsum]
      simp [SplitPinning.PartnerData.doubleRoot, fiberPartnerData_partner]
      rfl
    · have hpo := (Dπ).partner_mem_orientation ht hto
      refine ⟨eπ ⟨π t, hpo⟩, ?_⟩
      rw [hsum, add_comm]
      simp [SplitPinning.PartnerData.doubleRoot, fiberPartnerData_partner,
        partner_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht]
      rfl

include hR in
/-- The negated sums of the pieces are exactly the roots restricting to positive multiples of
`2 • -a`. -/
theorem mem_range_neg_doubleRoot_iff (χ : characterLattice T_K) :
    χ ∈ Set.range (fun l => -(Dπ).doubleRoot eπ l) ↔
      (χ ∈ roots j_K ∧
        ∃ m : ℕ, 0 < m ∧ f_K ≫ χ = m • characterLattice.baseChange bK S (2 • -a)) := by
  have key : χ ∈ Set.range (fun l => -(Dπ).doubleRoot eπ l) ↔
      -χ ∈ Set.range ((Dπ).doubleRoot eπ) := by
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨l, (neg_neg _).symm⟩
    · rintro ⟨l, hl⟩
      exact ⟨l, by simp [hl]⟩
  rw [key, mem_range_doubleRoot_iff k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR]
  constructor
  · rintro ⟨hχ, m, hm, hfχ⟩
    refine ⟨by simpa using hP.neg_mem_roots hχ, m, hm, ?_⟩
    rw [smul_neg, map_neg, smul_neg, ← hfχ, Preadditive.comp_neg, neg_neg]
  · rintro ⟨hχ, m, hm, hfχ⟩
    refine ⟨hP.neg_mem_roots hχ, m, hm, ?_⟩
    rw [Preadditive.comp_neg, hfχ, smul_neg, map_neg, smul_neg, neg_neg]

section Products

variable (hProd : Langlands.Geometry.Building.SplitRelativeRootGroupProductStatement.{u})

local notation "nπ" => Fintype.card
  (SplitPinning.PartnerData.orientation
    (fiberPartnerData k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a))

set_option hygiene false in
local notation "UK[" b "]" => Langlands.Geometry.Building.rootGroupPoints
  (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
  ((GroupScheme.baseChange (algebraBaseMap k K)).map (CommGroupScheme.groupHom f ≫ j))
  (characterLattice.baseChange (algebraBaseMap k K) S b)

include hR hProd in
/-- The split product statement for the upper pieces of the fiber of `a`. -/
theorem fiberUpperProduct :
    (∀ g : rationalPoints (G_K), g ∈ UK[a] ↔
      ∃ y : (k' : Fin (nπ * 3)) → Langlands.Geometry.Building.rootGroupPoints (S := T_K) j_K
          ((Dπ).upperPieceEnum eπ k'),
        g = (List.ofFn fun k' => (y k' : rationalPoints (G_K))).prod) ∧
    ∀ y y' : (k' : Fin (nπ * 3)) → Langlands.Geometry.Building.rootGroupPoints (S := T_K) j_K
        ((Dπ).upperPieceEnum eπ k'),
      (List.ofFn fun k' => (y k' : rationalPoints (G_K))).prod =
          (List.ofFn fun k' => (y' k' : rationalPoints (G_K))).prod → y = y' := by
  have hSK : IsSplitTorus ((CommGroupScheme.baseChange bK).obj S).toGrp :=
    hf.1.1.baseChange bK
  have h := hProd K (G_K) hGK (S_K) (T_K) j_K f_K hT hi hSK
    (characterLattice.baseChange bK S a) (baseChange_ne_zero_of_simple k K f j hf ν ha) _
    ((Dπ).upperPieceEnum eπ)
    (upperPieceEnum_injective k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a)
    (mem_range_upperPieceEnum_iff k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR)
  rw [Functor.map_comp]
  exact h

include hR hProd in
/-- The split product statement for the lower pieces of the fiber of `a`. -/
theorem fiberLowerProduct :
    (∀ g : rationalPoints (G_K), g ∈ UK[-a] ↔
      ∃ y : (k' : Fin (nπ * 3)) → Langlands.Geometry.Building.rootGroupPoints (S := T_K) j_K
          ((Dπ).lowerPieceEnum eπ k'),
        g = (List.ofFn fun k' => (y k' : rationalPoints (G_K))).prod) ∧
    ∀ y y' : (k' : Fin (nπ * 3)) → Langlands.Geometry.Building.rootGroupPoints (S := T_K) j_K
        ((Dπ).lowerPieceEnum eπ k'),
      (List.ofFn fun k' => (y k' : rationalPoints (G_K))).prod =
          (List.ofFn fun k' => (y' k' : rationalPoints (G_K))).prod → y = y' := by
  have hSK : IsSplitTorus ((CommGroupScheme.baseChange bK).obj S).toGrp :=
    hf.1.1.baseChange bK
  have hne : characterLattice.baseChange bK S (-a) ≠ 0 := by
    rw [map_neg, neg_ne_zero]
    exact baseChange_ne_zero_of_simple k K f j hf ν ha
  have h := hProd K (G_K) hGK (S_K) (T_K) j_K f_K hT hi hSK
    (characterLattice.baseChange bK S (-a)) hne _ ((Dπ).lowerPieceEnum eπ)
    ((Dπ).lowerPieceEnum_injective eπ
      (upperPieceEnum_injective k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a))
    (mem_range_lowerPieceEnum_iff k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR)
  rw [Functor.map_comp]
  exact h

include hR hProd in
/-- The split product statement for the sums of the pieces, at `2 • a`. -/
theorem fiberDoubleProduct :
    ∀ g : rationalPoints (G_K), g ∈ UK[2 • a] ↔
      ∃ y : (l : Fin nπ) → Langlands.Geometry.Building.rootGroupPoints (S := T_K) j_K
          ((Dπ).doubleRoot eπ l),
        g = (List.ofFn fun l => (y l : rationalPoints (G_K))).prod := by
  have hSK : IsSplitTorus ((CommGroupScheme.baseChange bK).obj S).toGrp :=
    hf.1.1.baseChange bK
  have hne : characterLattice.baseChange bK S (2 • a) ≠ 0 := by
    intro h
    apply h2a.1
    apply (characterLattice.baseChangeEquiv bK S hf.1.1).injective
    rw [map_zero]
    exact h
  have h := hProd K (G_K) hGK (S_K) (T_K) j_K f_K hT hi hSK
    (characterLattice.baseChange bK S (2 • a)) hne _ ((Dπ).doubleRoot eπ)
    ((Dπ).doubleRoot_injective eπ)
    (mem_range_doubleRoot_iff k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR)
  rw [Functor.map_comp]
  exact h.1

include hR hProd in
/-- The split product statement for the negated sums of the pieces, at `2 • -a`. -/
theorem fiberNegDoubleProduct :
    ∀ g : rationalPoints (G_K), g ∈ UK[2 • -a] ↔
      ∃ y : (l : Fin nπ) → Langlands.Geometry.Building.rootGroupPoints (S := T_K) j_K
          (-(Dπ).doubleRoot eπ l),
        g = (List.ofFn fun l => (y l : rationalPoints (G_K))).prod := by
  have hSK : IsSplitTorus ((CommGroupScheme.baseChange bK).obj S).toGrp :=
    hf.1.1.baseChange bK
  have hne : characterLattice.baseChange bK S (2 • -a) ≠ 0 := by
    intro h
    apply h2a.1
    apply (characterLattice.baseChangeEquiv bK S hf.1.1).injective
    rw [map_zero, ← neg_eq_zero, ← map_neg, ← smul_neg]
    exact h
  have h := hProd K (G_K) hGK (S_K) (T_K) j_K f_K hT hi hSK
    (characterLattice.baseChange bK S (2 • -a)) hne _ (fun l => -(Dπ).doubleRoot eπ l)
    (neg_injective.comp ((Dπ).doubleRoot_injective eπ))
    (mem_range_neg_doubleRoot_iff k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR)
  rw [Functor.map_comp]
  exact h.1

variable (hAdj : AdjacentSimpleRootSpecialLinearStatement.{u})

local notation "SL3K" => Matrix.SpecialLinearGroup (Fin 3) K

include hR hProd in
theorem fiber_hmem_upper : ∀ h : (Dₚ).pinning.base.support → SL3K,
    (∀ b ∈ Oₐ, SplitPinning.IsUpperSL3 (h b)) →
      (Dπ).pairOrbitSL3 hAdj (Dₚ).rootMaps h ∈ UK[a] := fun h hh =>
  (Dπ).pairOrbitSL3_mem_of_isUpper hAdj (Dₚ).rootMaps eπ _
    (fiberUpperProduct k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd).1 h hh

include hR hProd in
theorem fiber_hprod_upper : ∀ g ∈ UK[a], ∃ h : (Dₚ).pinning.base.support → SL3K,
    (∀ b ∈ Oₐ, SplitPinning.IsUpperSL3 (h b)) ∧ (Dπ).IsPairFamily h ∧
      (Dπ).pairOrbitSL3 hAdj (Dₚ).rootMaps h = g := fun _ hg =>
  (Dπ).exists_isUpper_pairOrbitSL3_eq hAdj (Dₚ).rootMaps eπ _
    (fiberUpperProduct k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd).1 hg

include hR hProd in
theorem fiber_huniq_upper : ∀ h h' : (Dₚ).pinning.base.support → SL3K,
    (∀ b ∈ Oₐ, SplitPinning.IsUpperSL3 (h b)) → (∀ b ∈ Oₐ, SplitPinning.IsUpperSL3 (h' b)) →
      (Dπ).IsPairFamily h → (Dπ).IsPairFamily h' →
        (Dπ).pairOrbitSL3 hAdj (Dₚ).rootMaps h = (Dπ).pairOrbitSL3 hAdj (Dₚ).rootMaps h' →
          ∀ b ∈ Oₐ, h b = h' b := fun h h' hh hh' hp hp' heq =>
  (Dπ).eq_of_isUpper_pairOrbitSL3_eq hAdj (Dₚ).rootMaps eπ
    (fiberUpperProduct k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd).2
    h h' hh hh' hp hp' heq

include hR hProd in
theorem fiber_hmem_lower : ∀ h : (Dₚ).pinning.base.support → SL3K,
    (∀ b ∈ Oₐ, SplitPinning.IsLowerSL3 (h b)) →
      (Dπ).pairOrbitSL3 hAdj (Dₚ).rootMaps h ∈ UK[-a] := fun h hh =>
  (Dπ).pairOrbitSL3_mem_of_isLower hAdj (Dₚ).rootMaps eπ _
    (fiberLowerProduct k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd).1 h hh

include hR hProd in
theorem fiber_hprod_lower : ∀ g ∈ UK[-a], ∃ h : (Dₚ).pinning.base.support → SL3K,
    (∀ b ∈ Oₐ, SplitPinning.IsLowerSL3 (h b)) ∧ (Dπ).IsPairFamily h ∧
      (Dπ).pairOrbitSL3 hAdj (Dₚ).rootMaps h = g := fun _ hg =>
  (Dπ).exists_isLower_pairOrbitSL3_eq hAdj (Dₚ).rootMaps eπ _
    (fiberLowerProduct k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd).1 hg

include hR hProd in
theorem fiber_huniq_lower : ∀ h h' : (Dₚ).pinning.base.support → SL3K,
    (∀ b ∈ Oₐ, SplitPinning.IsLowerSL3 (h b)) → (∀ b ∈ Oₐ, SplitPinning.IsLowerSL3 (h' b)) →
      (Dπ).IsPairFamily h → (Dπ).IsPairFamily h' →
        (Dπ).pairOrbitSL3 hAdj (Dₚ).rootMaps h = (Dπ).pairOrbitSL3 hAdj (Dₚ).rootMaps h' →
          ∀ b ∈ Oₐ, h b = h' b := fun h h' hh hh' hp hp' heq =>
  (Dπ).eq_of_isLower_pairOrbitSL3_eq hAdj (Dₚ).rootMaps eπ
    (fiberLowerProduct k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd).2
    h h' hh hh' hp hp' heq

include hR hProd in
theorem fiber_hmem2_upper : ∀ h : (Dₚ).pinning.base.support → SL3K,
    (∀ b ∈ Oₐ, SplitPinning.IsCentralUpperSL3 (h b)) →
      (Dπ).pairOrbitSL3 hAdj (Dₚ).rootMaps h ∈ UK[2 • a] := fun h hh =>
  (Dπ).pairOrbitSL3_mem_of_isCentralUpper hAdj (Dₚ).rootMaps eπ _
    (fiberDoubleProduct k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd) h hh

include hR hProd in
theorem fiber_hprod2_upper : ∀ g ∈ UK[2 • a], ∃ h : (Dₚ).pinning.base.support → SL3K,
    (∀ b ∈ Oₐ, SplitPinning.IsCentralUpperSL3 (h b)) ∧ (Dπ).IsPairFamily h ∧
      (Dπ).pairOrbitSL3 hAdj (Dₚ).rootMaps h = g := fun _ hg =>
  (Dπ).exists_isCentralUpper_pairOrbitSL3_eq hAdj (Dₚ).rootMaps eπ _
    (fiberDoubleProduct k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd) hg

include hR hProd in
theorem fiber_hmem2_lower : ∀ h : (Dₚ).pinning.base.support → SL3K,
    (∀ b ∈ Oₐ, SplitPinning.IsCentralLowerSL3 (h b)) →
      (Dπ).pairOrbitSL3 hAdj (Dₚ).rootMaps h ∈ UK[2 • -a] := fun h hh =>
  (Dπ).pairOrbitSL3_mem_of_isCentralLower hAdj (Dₚ).rootMaps eπ _
    (fiberNegDoubleProduct k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd) h hh

include hR hProd in
theorem fiber_hprod2_lower : ∀ g ∈ UK[2 • -a], ∃ h : (Dₚ).pinning.base.support → SL3K,
    (∀ b ∈ Oₐ, SplitPinning.IsCentralLowerSL3 (h b)) ∧ (Dπ).IsPairFamily h ∧
      (Dπ).pairOrbitSL3 hAdj (Dₚ).rootMaps h = g := fun _ hg =>
  (Dπ).exists_isCentralLower_pairOrbitSL3_eq hAdj (Dₚ).rootMaps eπ _
    (fiberNegDoubleProduct k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd) hg

end Products

end Enumerations

section Characters

attribute [local instance] rootsGaloisAction

local notation "p₀" => basePoint k K f j hP hf hcent hT ν hν hGK hi ha
local notation "β₀" => baseRoot k K f j hP hf hcent hT ν hν hGK hi ha
local notation "L₀" => fiberField k K f j hP hf hcent hT ν hν hGK hi ha
local notation "E₀" => pairField k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a
local notation "τₐ" => fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha

include hjc h2a in
/-- Every automorphism of `K` over the fiber field fixes the root of the partner of the base
point. -/
theorem galoisRepresentation_partnerRoot (σ : K ≃ₐ[L₀] K) :
    characterLattice.galoisRepresentation k K T (σ.restrictScalars k) (P.root (π p₀).1) =
      P.root (π p₀).1 := by
  have h0 := basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha
  have hβ := galoisRepresentation_rootOrbitField k K j β₀ σ
  have h1 : (Dₚ).action (σ.restrictScalars k) p₀ = p₀ := by
    apply Subtype.ext
    apply P.root.injective
    rw [fiberPinning_action_root k K f j hP hf hcent hT ν hν hGK hi]
    exact hβ
  rw [← fiberPinning_action_root k K f j hP hf hcent hT ν hν hGK hi,
    ← partner_action k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a _ h0, h1]

/-- The root of the partner of the base point, descended to the fiber field. -/
def partnerCharacter :
    rationalCharacters (GaloisPointComparison.baseChanged k L₀ T.toGrp) :=
  fixedDescend T.toGrp L₀ K (baseChangedCharacter k K T (P.root (π p₀).1)) (fun σ => by
    rw [tensorConj_tensorValue_baseChangedCharacter,
      galoisRepresentation_partnerRoot k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a σ])

/-- At a rational point, the partner character takes the conjugate of the value of the
root-orbit character of the base root. -/
theorem partnerCharacter_eval (z : rationalPoints T.toGrp) :
    (rationalCharacterEval (partnerCharacter k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a)
        (GaloisPointComparison.rationalExtend k L₀ T.toGrp z) : L₀) =
      SU3Root.conjugation E₀ L₀ (rationalCharacterEval (rootOrbitCharacter k K j β₀)
        (GaloisPointComparison.rationalExtend k L₀ T.toGrp z) : L₀) := by
  have h0 := basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha
  apply Subtype.val_injective
  have h1 := rationalCharacterEval_fixedDescend T.toGrp L₀ K
    (baseChangedCharacter k K T (P.root (π p₀).1)) (fun σ => by
      rw [tensorConj_tensorValue_baseChangedCharacter,
        galoisRepresentation_partnerRoot k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a σ]) z
  change ((rationalCharacterEval (partnerCharacter k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a)
      (GaloisPointComparison.rationalExtend k L₀ T.toGrp z) : L₀) : K) = _
  refine h1.trans ?_
  rw [← fiberEmbedding_basePoint k K f j hP hf hcent hT ν hν hGK hi hjc ha,
    ← fiberEmbedding_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a h0,
    fiberEmbedding_rootOrbitCharacter k K f j hP hf hcent hT ν hν hGK hi hjc ha _
      (partner_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a h0)]
  rfl

/-- The embeddings of the inverse partner character are the inverse values of the partner
roots. -/
theorem fiberEmbedding_neg_partnerCharacter {b : (Dₚ).pinning.base.support} (hb : b ∈ Oₐ)
    (z : rationalPoints T.toGrp) :
    τₐ b (rationalCharacterEval (-partnerCharacter k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a)
        (GaloisPointComparison.rationalExtend k L₀ T.toGrp z) : L₀) =
      (((rationalCharacterEval ((rationalCharacters.equivCharacterLattice T_K).symm
        (P.root (π b).1)) (GaloisPointComparison.rationalExtend k K T.toGrp z))⁻¹ : Kˣ) : K) := by
  rw [rationalCharacterEval_neg, Units.val_inv_eq_inv_val, map_inv₀,
    partnerCharacter_eval k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a,
    ← fiberEmbedding_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hb,
    fiberEmbedding_rootOrbitCharacter k K f j hP hf hcent hT ν hν hGK hi hjc ha _
      (partner_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hb), Units.val_inv_eq_inv_val]

end Characters

end SimpleRootFiber

end Langlands.GroupScheme
