import Langlands.GroupScheme.Rational.OrthogonalOrbitSpecialLinear
import Langlands.GroupScheme.Rational.AdjacentSimpleRootSpecialLinearStatement

/-! # Ternary special linear homomorphisms over partnered orbits of simple roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitPinning

open SpecialLinear

local notation "SL3" A => Matrix.SpecialLinearGroup (Fin 3) A

section Split

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G}
  (hAdj : AdjacentSimpleRootSpecialLinearStatement.{u})
  (x : p.NormalizedSimpleRootParametrizations)

open Classical in
/-- The ternary homomorphism of an ordered pair of simple roots, chosen by the adjacent-root
statement when both pairings are `-1`, and trivial otherwise. -/
def pairSL3 (a b : p.base.support) : (SL3 k) →* rationalPoints G :=
  if h : p.rootDatum.pairing a b = -1 ∧ p.rootDatum.pairing b a = -1 then
    Classical.choose (hAdj k G p x a b h.1 h.2)
  else 1

section Pair

variable {a b : p.base.support} (hab : p.rootDatum.pairing a b = -1)
  (hba : p.rootDatum.pairing b a = -1)

include hab hba in
theorem pairSL3_spec :
    (pairSL3 hAdj x a b).comp TernaryPresentation.left = rootSL2 x a ∧
      (pairSL3 hAdj x a b).comp TernaryPresentation.right = rootSL2 x b := by
  unfold pairSL3
  rw [dite_eq_left ⟨hab, hba⟩]
  exact Classical.choose_spec (hAdj k G p x a b hab hba)

include hab hba in
theorem pairSL3_left (g : Matrix.SpecialLinearGroup (Fin 2) k) :
    pairSL3 hAdj x a b (TernaryPresentation.left g) = rootSL2 x a g :=
  DFunLike.congr_fun (pairSL3_spec hAdj x hab hba).1 g

include hab hba in
theorem pairSL3_right (g : Matrix.SpecialLinearGroup (Fin 2) k) :
    pairSL3 hAdj x a b (TernaryPresentation.right g) = rootSL2 x b g :=
  DFunLike.congr_fun (pairSL3_spec hAdj x hab hba).2 g

include hab hba in
/-- Uniqueness: a homomorphism with the same block restrictions is the chosen one. -/
theorem eq_pairSL3 {φ : (SL3 k) →* rationalPoints G}
    (hl : φ.comp TernaryPresentation.left = rootSL2 x a)
    (hr : φ.comp TernaryPresentation.right = rootSL2 x b) : φ = pairSL3 hAdj x a b :=
  TernaryPresentation.hom_ext (hl.trans (pairSL3_spec hAdj x hab hba).1.symm)
    (hr.trans (pairSL3_spec hAdj x hab hba).2.symm)

include hab hba in
/-- Swapping the two roots composes with the outer involution. -/
theorem pairSL3_swap :
    pairSL3 hAdj x b a = (pairSL3 hAdj x a b).comp TernaryPresentation.outer := by
  symm
  apply eq_pairSL3 hAdj x hba hab
  · rw [MonoidHom.comp_assoc, TernaryPresentation.outer_comp_left]
    exact (pairSL3_spec hAdj x hab hba).2
  · rw [MonoidHom.comp_assoc, TernaryPresentation.outer_comp_right]
    exact (pairSL3_spec hAdj x hab hba).1

include hab hba in
/-- The values lie in the join of the two rank-one root subgroups. -/
theorem pairSL3_mem (g : SL3 k) :
    pairSL3 hAdj x a b g ∈ (rankData x a).rootSubgroup ⊔ (rankData x b).rootSubgroup := by
  have hg : g ∈ (TernaryPresentation.left (R := k)).range ⊔
      (TernaryPresentation.right (R := k)).range := by
    rw [TernaryPresentation.range_left_sup_range_right]
    exact Subgroup.mem_top g
  have hle : (TernaryPresentation.left (R := k)).range ⊔
      (TernaryPresentation.right (R := k)).range ≤
      ((rankData x a).rootSubgroup ⊔ (rankData x b).rootSubgroup).comap
        (pairSL3 hAdj x a b) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨h, rfl⟩
      rw [Subgroup.mem_comap, pairSL3_left hAdj x hab hba]
      exact Subgroup.mem_sup_left (rootSL2_mem x a h)
    · rintro _ ⟨h, rfl⟩
      rw [Subgroup.mem_comap, pairSL3_right hAdj x hab hba]
      exact Subgroup.mem_sup_right (rootSL2_mem x b h)
  exact hle hg

end Pair

/-- Root subgroups of distinct orthogonal simple roots centralize each other. -/
theorem rootSubgroup_le_centralizer {a c : p.base.support} (hac : a ≠ c)
    (ho : p.rootDatum.IsOrthogonal a c) :
    (rankData x a).rootSubgroup ≤ Subgroup.centralizer (rankData x c).rootSubgroup := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hO : ∀ u ∈ ({a, c} : Set p.base.support), ∀ v ∈ ({a, c} : Set p.base.support),
      u ≠ v → p.rootDatum.IsOrthogonal u v := by
    rintro u (rfl | rfl) v (rfl | rfl) huv
    · exact absurd rfl huv
    · exact ho
    · exact ho.symm
    · exact absurd rfl huv
  have hne : (⟨c, Or.inr rfl⟩ : ({a, c} : Set p.base.support)) ≠ ⟨a, Or.inl rfl⟩ :=
    fun h => hac (congrArg Subtype.val h).symm
  exact ((rootsCommute_of_orthogonal x {a, c} hO).subgroups hne z y hz hy).eq

/-- Values of ternary homomorphisms at two pairs of simple roots commute when every root of
the first pair is distinct from and orthogonal to every root of the second pair. -/
theorem pairSL3_commute {a b c d : p.base.support} (hab : p.rootDatum.pairing a b = -1)
    (hba : p.rootDatum.pairing b a = -1) (hcd : p.rootDatum.pairing c d = -1)
    (hdc : p.rootDatum.pairing d c = -1)
    (hca : c ≠ a) (hda : d ≠ a) (hcb : c ≠ b) (hdb : d ≠ b)
    (oca : p.rootDatum.IsOrthogonal c a) (oda : p.rootDatum.IsOrthogonal d a)
    (ocb : p.rootDatum.IsOrthogonal c b) (odb : p.rootDatum.IsOrthogonal d b)
    (g g' : SL3 k) :
    Commute (pairSL3 hAdj x a b g) (pairSL3 hAdj x c d g') := by
  have hle : (rankData x a).rootSubgroup ⊔ (rankData x b).rootSubgroup ≤
      Subgroup.centralizer (((rankData x c).rootSubgroup ⊔ (rankData x d).rootSubgroup :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le (rootSubgroup_le_centralizer x hca oca)
        (rootSubgroup_le_centralizer x hda oda)
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le (rootSubgroup_le_centralizer x hcb ocb)
        (rootSubgroup_le_centralizer x hdb odb)
  exact (Subgroup.mem_centralizer_iff.mp (hle (pairSL3_mem hAdj x hab hba g)) _
    (pairSL3_mem hAdj x hcd hdc g')).symm

/-- A partner structure on a set `O` of simple roots: an involution of `O` without fixed points
pairing every root with an `A₂` partner, all other members of `O` being orthogonal to it. -/
structure PartnerData (O : Set p.base.support) where
  /-- The partner map. -/
  partner : p.base.support → p.base.support
  mem : ∀ a ∈ O, partner a ∈ O
  partner_partner : ∀ a ∈ O, partner (partner a) = a
  ne : ∀ a ∈ O, partner a ≠ a
  pairing : ∀ a ∈ O, p.rootDatum.pairing a (partner a) = -1 ∧
    p.rootDatum.pairing (partner a) a = -1
  orthogonal : ∀ a ∈ O, ∀ b ∈ O, b ≠ a → b ≠ partner a → p.rootDatum.IsOrthogonal a b

namespace PartnerData

variable {O : Set p.base.support} (D : PartnerData O)

/-- A choice of one member in each pair: those preceding their partner in a fixed well
order. -/
def orientation : Set p.base.support :=
  {a | a ∈ O ∧ WellOrderingRel a (D.partner a)}

theorem mem_of_mem_orientation {a : p.base.support} (ha : a ∈ D.orientation) : a ∈ O := ha.1

/-- Exactly one member of each pair lies in the orientation. -/
theorem mem_orientation_iff {a : p.base.support} (ha : a ∈ O) :
    a ∈ D.orientation ↔ D.partner a ∉ D.orientation := by
  constructor
  · rintro ⟨-, h⟩ ⟨-, h'⟩
    rw [D.partner_partner a ha] at h'
    exact (asymm_of WellOrderingRel h) h'
  · intro h
    refine ⟨ha, ?_⟩
    rcases trichotomous_of WellOrderingRel a (D.partner a) with h1 | h1 | h1
    · exact h1
    · exact absurd h1.symm (D.ne a ha)
    · exact absurd ⟨D.mem a ha, by rw [D.partner_partner a ha]; exact h1⟩ h

theorem partner_mem_orientation {a : p.base.support} (ha : a ∈ O) (h : a ∉ D.orientation) :
    D.partner a ∈ D.orientation := by
  by_contra h'
  exact h ((D.mem_orientation_iff ha).mpr h')

open Classical in
/-- The member of the orientation in the pair of `a`. -/
def normalize (a : p.base.support) : p.base.support :=
  if a ∈ D.orientation then a else D.partner a

theorem normalize_mem {a : p.base.support} (ha : a ∈ O) : D.normalize a ∈ D.orientation := by
  unfold normalize
  split_ifs with h
  · exact h
  · exact D.partner_mem_orientation ha h

theorem normalize_of_mem {a : p.base.support} (ha : a ∈ D.orientation) : D.normalize a = a := by
  unfold normalize
  rw [ite_eq_left ha]

theorem normalize_eq (a : p.base.support) :
    D.normalize a = a ∨ D.normalize a = D.partner a := by
  unfold normalize
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Different members of the orientation give commuting values. -/
theorem commute {r r' : p.base.support} (hr : r ∈ D.orientation) (hr' : r' ∈ D.orientation)
    (hne : r ≠ r') (g g' : SL3 k) :
    Commute (pairSL3 hAdj x r (D.partner r) g) (pairSL3 hAdj x r' (D.partner r') g') := by
  have hrO := D.mem_of_mem_orientation hr
  have hr'O := D.mem_of_mem_orientation hr'
  have hpr : D.partner r ∉ D.orientation := (D.mem_orientation_iff hrO).mp hr
  have hpr' : D.partner r' ∉ D.orientation := (D.mem_orientation_iff hr'O).mp hr'
  have h1 : r' ≠ r := fun h => hne h.symm
  have h2 : r' ≠ D.partner r := fun h => hpr (h ▸ hr')
  have h3 : D.partner r' ≠ r := fun h => hpr' (h ▸ hr)
  have h4 : D.partner r' ≠ D.partner r := by
    intro h
    apply hne
    rw [← D.partner_partner r hrO, ← h, D.partner_partner r' hr'O]
  have h5 : r' ≠ D.partner (D.partner r) := by rwa [D.partner_partner r hrO]
  have h6 : D.partner r' ≠ D.partner (D.partner r) := by rwa [D.partner_partner r hrO]
  exact pairSL3_commute hAdj x (D.pairing r hrO).1 (D.pairing r hrO).2
    (D.pairing r' hr'O).1 (D.pairing r' hr'O).2 h1 h3 h2 h4
    (D.orthogonal r hrO r' hr'O h1 h2).symm (D.orthogonal r hrO _ (D.mem r' hr'O) h3 h4).symm
    (D.orthogonal _ (D.mem r hrO) r' hr'O h2 h5).symm
    (D.orthogonal _ (D.mem r hrO) _ (D.mem r' hr'O) h4 h6).symm g g'

instance : Fintype D.orientation := Fintype.ofFinite _

/-- The product over the orientation of the ternary homomorphisms of the pairs. -/
def pairOrbitSL3 : (p.base.support → SL3 k) →* rationalPoints G :=
  (MonoidHom.noncommPiCoprod (fun r : D.orientation => pairSL3 hAdj x r (D.partner r))
    (fun r r' hne g g' => D.commute hAdj x r.2 r'.2 (fun h => hne (Subtype.ext h)) g g')).comp
    (MonoidHom.pi fun r : D.orientation =>
      Pi.evalMonoidHom (fun _ => SL3 k) (r : p.base.support))

theorem pairOrbitSL3_apply (h : p.base.support → SL3 k) :
    D.pairOrbitSL3 hAdj x h = Finset.univ.noncommProd
      (fun r : D.orientation => pairSL3 hAdj x r (D.partner r) (h r))
      (fun r _ r' _ hne => D.commute hAdj x r.2 r'.2 (fun h => hne (Subtype.ext h)) _ _) :=
  rfl

/-- The product depends only on the values on the orientation. -/
theorem pairOrbitSL3_congr {h h' : p.base.support → SL3 k}
    (hh : ∀ a ∈ O, h a = h' a) : D.pairOrbitSL3 hAdj x h = D.pairOrbitSL3 hAdj x h' := by
  rw [pairOrbitSL3_apply, pairOrbitSL3_apply]
  congr 1
  funext r
  rw [hh r (D.mem_of_mem_orientation r.2)]

/-- Families compatible with the outer involution along the partner map. -/
def IsPairFamily (h : p.base.support → SL3 k) : Prop :=
  ∀ a ∈ O, h (D.partner a) = TernaryPresentation.outer (h a)

/-- On a pair family, both members of a pair give the same value. -/
theorem pairSL3_partner_eq {h : p.base.support → SL3 k} (hh : D.IsPairFamily h)
    {a : p.base.support} (ha : a ∈ O) :
    pairSL3 hAdj x (D.partner a) (D.partner (D.partner a)) (h (D.partner a)) =
      pairSL3 hAdj x a (D.partner a) (h a) := by
  rw [D.partner_partner a ha, hh a ha,
    pairSL3_swap hAdj x (D.pairing a ha).1 (D.pairing a ha).2, MonoidHom.comp_apply,
    TernaryPresentation.outer_outer]

theorem pairSL3_normalize_eq {h : p.base.support → SL3 k} (hh : D.IsPairFamily h)
    {a : p.base.support} (ha : a ∈ O) :
    pairSL3 hAdj x (D.normalize a) (D.partner (D.normalize a)) (h (D.normalize a)) =
      pairSL3 hAdj x a (D.partner a) (h a) := by
  rcases D.normalize_eq a with h1 | h1 <;> rw [h1]
  exact D.pairSL3_partner_eq hAdj x hh ha

end PartnerData

end Split

/-- Reindexing a commuting product over a finite type by a permutation. -/
theorem noncommProd_univ_equiv {I M : Type*} [Fintype I] [Monoid M] (e : I ≃ I) (f : I → M)
    (hc : ((Finset.univ : Finset I) : Set I).Pairwise (Function.onFun Commute f))
    (hc' : ((Finset.univ : Finset I) : Set I).Pairwise
      (Function.onFun Commute (fun i => f (e i)))) :
    Finset.univ.noncommProd (fun i => f (e i)) hc' = Finset.univ.noncommProd f hc := by
  unfold Finset.noncommProd
  congr 1
  have hm := Multiset.map_map f e Finset.univ.val
  rw [Multiset.map_univ_val_equiv] at hm
  exact hm.symm

section Galois

open GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G)

local instance partnerOrbitSpecialUnitaryIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (hAdj : AdjacentSimpleRootSpecialLinearStatement.{u})
    (p : Langlands.GroupScheme.SplitPinning
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map i)
    (x : p.NormalizedSimpleRootParametrizations)
    {ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support}
    (hx : RootMapsGaloisCompatible k K p x ρ)
    (hroot : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
      characterLattice.congr eT (p.rootDatum.root (ρ σ a)) =
        characterLattice.galoisRepresentation k K T σ
          (characterLattice.congr eT (p.rootDatum.root a)))
    (hρpair : ∀ (σ : K ≃ₐ[k] K) (a b : p.base.support),
      p.rootDatum.pairing (ρ σ a) (ρ σ b) = p.rootDatum.pairing a b)

include hT hx hroot hρpair in
/-- Conjugating the coefficients of a ternary homomorphism by a Galois automorphism gives
the ternary homomorphism of the permuted pair at the conjugated matrix. -/
theorem pairSL3_rationalConjugate (σ : K ≃ₐ[k] K) {a b : p.base.support}
    (hab : p.rootDatum.pairing a b = -1) (hba : p.rootDatum.pairing b a = -1) (g : SL3 K) :
    rationalConjugate k K G σ (pairSL3 hAdj x a b g) =
      pairSL3 hAdj x (ρ σ a) (ρ σ b) (Matrix.SpecialLinearGroup.map σ.toRingHom g) := by
  have hab' : p.rootDatum.pairing (ρ σ a) (ρ σ b) = -1 := (hρpair σ a b).trans hab
  have hba' : p.rootDatum.pairing (ρ σ b) (ρ σ a) = -1 := (hρpair σ b a).trans hba
  have h : (rationalConjugate k K G σ).toMonoidHom.comp (pairSL3 hAdj x a b) =
      (pairSL3 hAdj x (ρ σ a) (ρ σ b)).comp (Matrix.SpecialLinearGroup.map σ.toRingHom) := by
    apply TernaryPresentation.hom_ext
    · refine MonoidHom.ext fun g => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [pairSL3_left hAdj x hab hba, TernaryPresentation.map_left,
        pairSL3_left hAdj x hab' hba']
      exact rootSL2_rationalConjugate k K i p eT hT x hx hroot σ a g
    · refine MonoidHom.ext fun g => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [pairSL3_right hAdj x hab hba, TernaryPresentation.map_right,
        pairSL3_right hAdj x hab' hba']
      exact rootSL2_rationalConjugate k K i p eT hT x hx hroot σ b g
  exact DFunLike.congr_fun h g

variable {O : Set p.base.support} (D : PartnerData O)
    (hOs : ∀ (σ : K ≃ₐ[k] K) a, a ∈ O ↔ ρ σ a ∈ O)
    (hπρ : ∀ (σ : K ≃ₐ[k] K), ∀ a ∈ O, D.partner (ρ σ a) = ρ σ (D.partner a))

/-- Families of ternary matrices on the simple roots that are Galois equivariant and
compatible with the outer involution along the partner map. -/
def pairFamilies (D : PartnerData O) (ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support) :
    Subgroup (p.base.support → SL3 K) where
  carrier := {h | (∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
    h (ρ σ a) = Matrix.SpecialLinearGroup.map σ.toRingHom (h a)) ∧ D.IsPairFamily h}
  one_mem' := ⟨fun σ a => by simp, fun a _ => by simp⟩
  mul_mem' := fun {g h} hg hh => ⟨fun σ a => by
    simp only [Pi.mul_apply, hg.1 σ a, hh.1 σ a, map_mul], fun a ha => by
    simp only [Pi.mul_apply, hg.2 a ha, hh.2 a ha, map_mul]⟩
  inv_mem' := fun {g} hg => ⟨fun σ a => by
    simp only [Pi.inv_apply, hg.1 σ a, map_inv], fun a ha => by
    simp only [Pi.inv_apply, hg.2 a ha, map_inv]⟩

include hOs hπρ in
/-- The Galois action permutes the orientation after normalization. -/
theorem normalize_action_injective (σ : K ≃ₐ[k] K) :
    Function.Injective (fun r : D.orientation =>
      (⟨D.normalize (ρ σ r), D.normalize_mem ((hOs σ r).mp (D.mem_of_mem_orientation r.2))⟩ :
        D.orientation)) := by
  rintro ⟨r, hr⟩ ⟨r', hr'⟩ h
  have h' : D.normalize (ρ σ r) = D.normalize (ρ σ r') := congrArg Subtype.val h
  have hrO := D.mem_of_mem_orientation hr
  have hr'O := D.mem_of_mem_orientation hr'
  apply Subtype.ext
  change r = r'
  rcases D.normalize_eq (ρ σ r) with h1 | h1 <;>
    rcases D.normalize_eq (ρ σ r') with h2 | h2 <;>
    rw [h1, h2] at h'
  · exact (ρ σ).injective h'
  · rw [hπρ σ r' hr'O] at h'
    have := (ρ σ).injective h'
    exact absurd (this ▸ hr) ((D.mem_orientation_iff hr'O).mp hr')
  · rw [hπρ σ r hrO] at h'
    have := (ρ σ).injective h'
    exact absurd (this ▸ hr') ((D.mem_orientation_iff hrO).mp hr)
  · rw [hπρ σ r hrO, hπρ σ r' hr'O] at h'
    have := (ρ σ).injective h'
    rw [← D.partner_partner r hrO, this, D.partner_partner r' hr'O]

include hT hx hroot hρpair hOs hπρ in
/-- Pair families give Galois-fixed products. -/
theorem pairOrbitSL3_rationalConjugate {h : p.base.support → SL3 K}
    (hh : h ∈ pairFamilies k K p D ρ) (σ : K ≃ₐ[k] K) :
    rationalConjugate k K G σ (D.pairOrbitSL3 hAdj x h) = D.pairOrbitSL3 hAdj x h := by
  let e : D.orientation ≃ D.orientation := Equiv.ofBijective _
    (Finite.injective_iff_bijective.mp (normalize_action_injective k K p D hOs hπρ σ))
  have hval : ∀ r : D.orientation,
      rationalConjugate k K G σ (pairSL3 hAdj x r (D.partner r) (h r)) =
        pairSL3 hAdj x (e r) (D.partner (e r)) (h (e r)) := by
    intro r
    have hrO := D.mem_of_mem_orientation r.2
    rw [pairSL3_rationalConjugate k K i hAdj p eT hT x hx hroot hρpair σ (D.pairing r hrO).1
      (D.pairing r hrO).2, ← hh.1 σ, ← hπρ σ r hrO]
    exact (D.pairSL3_normalize_eq hAdj x hh.2 ((hOs σ r).mp hrO)).symm
  rw [PartnerData.pairOrbitSL3_apply, Finset.map_noncommProd]
  simp only [hval]
  exact noncommProd_univ_equiv e
    (fun r : D.orientation => pairSL3 hAdj x r (D.partner r) (h r)) _ _

section Descent

variable [FiniteDimensional k K] [IsGalois k K]

include hT hx hroot hρpair hOs hπρ in
theorem exists_pairOrbitSL3_eq_rationalExtend {h : p.base.support → SL3 K}
    (hh : h ∈ pairFamilies k K p D ρ) :
    ∃ g₀ : rationalPoints G, rationalExtend k K G g₀ = D.pairOrbitSL3 hAdj x h :=
  exists_rationalExtend_eq_of_fixed k K
    (pairOrbitSL3_rationalConjugate k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ hh)

/-- The descended pair-orbit homomorphism on pair families. -/
def pairOrbitRational : pairFamilies k K p D ρ →* rationalPoints G where
  toFun h := Classical.choose
    (exists_pairOrbitSL3_eq_rationalExtend k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ h.2)
  map_one' := by
    apply rationalExtend_injective_of_isAffineHom k K
    rw [Classical.choose_spec
      (exists_pairOrbitSL3_eq_rationalExtend k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ
        (1 : pairFamilies k K p D ρ).2), map_one]
    exact map_one _
  map_mul' g h := by
    apply rationalExtend_injective_of_isAffineHom k K
    rw [Classical.choose_spec
      (exists_pairOrbitSL3_eq_rationalExtend k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ
        (g * h).2), map_mul,
      Classical.choose_spec
        (exists_pairOrbitSL3_eq_rationalExtend k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ
          g.2),
      Classical.choose_spec
        (exists_pairOrbitSL3_eq_rationalExtend k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ
          h.2)]
    exact map_mul _ _ _

theorem rationalExtend_pairOrbitRational (h : pairFamilies k K p D ρ) :
    rationalExtend k K G (pairOrbitRational k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ h) =
      D.pairOrbitSL3 hAdj x h :=
  Classical.choose_spec
    (exists_pairOrbitSL3_eq_rationalExtend k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ h.2)

end Descent

section Field

variable {L : Type u} [Field L] [Algebra k L] (τ : p.base.support → (L →ₐ[k] K))
  (hτ : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support), a ∈ O → τ (ρ σ a) = σ.toAlgHom.comp (τ a))
  (c : SU3Root.RingInvolution L)
  (hτc : ∀ a ∈ O, ∀ y : L, τ (D.partner a) y = τ a (c.bar y))

omit [Algebra k L] in
theorem specialLinearMap_comp_three (f : L →+* K) (σ : K ≃ₐ[k] K) (g : SL3 L) :
    Matrix.SpecialLinearGroup.map (σ.toRingHom.comp f) g =
      Matrix.SpecialLinearGroup.map σ.toRingHom (Matrix.SpecialLinearGroup.map f g) := by
  ext r s
  simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

open Classical in
/-- Embedding coordinates of a ternary matrix over `L`, trivial off `O`. -/
def fieldFamilyThree : (SL3 L) →* (p.base.support → SL3 K) :=
  MonoidHom.pi fun a =>
    if a ∈ O then Matrix.SpecialLinearGroup.map (τ a).toRingHom else 1

open Classical in
theorem fieldFamilyThree_apply (g : SL3 L) (a : p.base.support) :
    fieldFamilyThree k K p (O := O) τ g a =
      if a ∈ O then Matrix.SpecialLinearGroup.map (τ a).toRingHom g else 1 := by
  simp only [fieldFamilyThree, MonoidHom.pi_apply]
  split_ifs <;> rfl

theorem fieldFamilyThree_of_mem (g : SL3 L) {a : p.base.support} (ha : a ∈ O) :
    fieldFamilyThree k K p (O := O) τ g a =
      Matrix.SpecialLinearGroup.map (τ a).toRingHom g := by
  rw [fieldFamilyThree_apply, ite_eq_left ha]

include hτ hOs hτc in
theorem fieldFamilyThree_mem (g : SL3 L) (hg : g ∈ SU3Root.twistFixedSubgroup c) :
    fieldFamilyThree k K p (O := O) τ g ∈ pairFamilies k K p D ρ := by
  refine ⟨fun σ a => ?_, fun a ha => ?_⟩
  · by_cases ha : a ∈ O
    · have ha' : ρ σ a ∈ O := (hOs σ a).mp ha
      rw [fieldFamilyThree_of_mem k K p τ g ha, fieldFamilyThree_of_mem k K p τ g ha',
        hτ σ a ha]
      exact specialLinearMap_comp_three k K (τ a).toRingHom σ g
    · have ha' : ρ σ a ∉ O := fun h => ha ((hOs σ a).mpr h)
      simp only [fieldFamilyThree_apply, ha, ha', ite_false, map_one]
  · rw [fieldFamilyThree_of_mem k K p τ g (D.mem a ha), fieldFamilyThree_of_mem k K p τ g ha,
      ← TernaryPresentation.map_outer,
      TernaryPresentation.outer_eq_map_of_mem_twistFixedSubgroup c g hg]
    ext r s
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hτc a ha]

variable [FiniteDimensional k K] [IsGalois k K]

/-- The ternary unitary homomorphism over `L`, descended to the rational points of `G`. -/
def fieldSU3 : SU3Root.twistFixedSubgroup c →* rationalPoints G :=
  (pairOrbitRational k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ).comp
    (((fieldFamilyThree k K p (O := O) τ).comp (SU3Root.twistFixedSubgroup c).subtype).codRestrict
      _ (fun g => fieldFamilyThree_mem k K p D hOs τ hτ c hτc g.1 g.2))

theorem rationalExtend_fieldSU3 (g : SU3Root.twistFixedSubgroup c) :
    rationalExtend k K G (fieldSU3 k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ τ hτ c hτc g) =
      D.pairOrbitSL3 hAdj x (fun a => Matrix.SpecialLinearGroup.map (τ a).toRingHom g.1) := by
  rw [fieldSU3, MonoidHom.comp_apply, rationalExtend_pairOrbitRational]
  apply PartnerData.pairOrbitSL3_congr
  intro a ha
  exact fieldFamilyThree_of_mem k K p τ g.1 ha

/-- The homomorphism on the special unitary group in its general linear form. -/
def unitaryRho : SU3Root.specialUnitarySubgroup c →* rationalPoints G :=
  (fieldSU3 k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ τ hτ c hτc).comp
    (SU3Root.fixedSpecialUnitaryEquiv c).symm.toMonoidHom

theorem rationalExtend_unitaryRho (g : SU3Root.specialUnitarySubgroup c) :
    rationalExtend k K G (unitaryRho k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ τ hτ c hτc g) =
      D.pairOrbitSL3 hAdj x (fun a => Matrix.SpecialLinearGroup.map (τ a).toRingHom
        ((SU3Root.fixedSpecialUnitaryEquiv c).symm g).1) :=
  rationalExtend_fieldSU3 k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ τ hτ c hτc _

end Field

end Galois

end SplitPinning

end Langlands.GroupScheme
