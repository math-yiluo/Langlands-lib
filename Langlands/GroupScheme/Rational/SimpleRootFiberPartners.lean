import Langlands.GroupScheme.Rational.SimpleRootFiberPinning
import Langlands.GroupScheme.Rational.QuasiSplitPinningOrbitPairs
import Langlands.GroupScheme.Rational.MultipliableRootNoncommutation
import Langlands.GroupScheme.Rational.RootPartnerFields

/-! # Partners in the simple-root fiber of a multipliable relative root -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace SimpleRootFiber

open Langlands.LinearAlgebra.RootDatumOrbitPairs

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
  (f : S ⟶ T) (j : T.toGrp ⟶ G)

local notation "bK" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange bK) T
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange bK) G
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange bK) j

local instance simpleRootFiberPartnersIsAffineHom : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom bK)
  infer_instance

attribute [local instance] rootsGaloisAction

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

local notation "Dₚ" => fiberPinning k K f j hP hf hcent hT ν hν hGK hi

section Action

/-- The simple-root action of the fiber pinning is pairing compatible. -/
theorem fiberPinning_isPairingCompatible :
    IsPairingCompatible (Dₚ).pinning.base (Dₚ).action :=
  GaloisCompatiblePinningData.ofRegularCocharacter_isPairingCompatible hGK hT hi

/-- The action of a Galois element on a simple root of the fiber pinning is ordinary Galois
transport of its root. -/
theorem fiberPinning_action_root (σ : K ≃ₐ[k] K) (t : (Dₚ).pinning.base.support) :
    P.root ((Dₚ).action σ t).1 =
      characterLattice.galoisRepresentation k K T σ (P.root t.1) :=
  IsRootDatumOf.descendedRegularCocharacterSimpleAction_root k K j hP _ _ σ t

/-- The action of the fiber pinning preserves the pairing of simple roots. -/
theorem fiberPinning_pairing_action (σ : K ≃ₐ[k] K) (t t' : (Dₚ).pinning.base.support) :
    P.pairing ((Dₚ).action σ t).1
        ((Dₚ).action σ t').1 = P.pairing t.1 t'.1 :=
  (fiberPinning_isPairingCompatible k K f j hP hf hcent hT ν hν hGK hi).pairing_apply σ t t'

end Action

section Partner

open Classical in
/-- The partner of a simple root: its unique non-orthogonal companion in its Galois orbit, if
there is one, and the root itself otherwise. -/
def partner (t : (Dₚ).pinning.base.support) : (Dₚ).pinning.base.support :=
  if h : ∃ σ : K ≃ₐ[k] K, (Dₚ).action σ t ≠ t ∧
      ¬ P.IsOrthogonal t.1 ((Dₚ).action σ t).1 then
    (Dₚ).action h.choose t
  else t

local notation "π" => partner k K f j hP hf hcent hT ν hν hGK hi

/-- If a simple root has a non-orthogonal companion in its orbit, the partner is such a
companion. -/
theorem partner_spec {t : (Dₚ).pinning.base.support}
    (h : ∃ σ : K ≃ₐ[k] K, (Dₚ).action σ t ≠ t ∧
      ¬ P.IsOrthogonal t.1 ((Dₚ).action σ t).1) :
    ∃ σ : K ≃ₐ[k] K, (Dₚ).action σ t = π t ∧ π t ≠ t ∧ ¬ P.IsOrthogonal t.1 (π t).1 := by
  have hp : π t = (Dₚ).action h.choose t := by
    unfold partner
    rw [dite_eq_left_of_eq_true (eq_true h)]
  refine ⟨h.choose, hp.symm, ?_, ?_⟩
  · rw [hp]
    exact h.choose_spec.1
  · rw [hp]
    exact h.choose_spec.2

end Partner

section Field

variable [IsGalois k K] (hjc : IsClosedSubgroup j)
  {a : characterLattice S} (ha : a ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν)

local notation "Oₐ" => fiberSet k K f j hP hf hcent hT ν hν hGK hi a
local notation "π" => partner k K f j hP hf hcent hT ν hν hGK hi
local notation "p₀" => basePoint k K f j hP hf hcent hT ν hν hGK hi ha

include hjc ha in
/-- Any two members of the fiber of a simple relative root are related by the action. -/
theorem exists_action_eq {t t' : (Dₚ).pinning.base.support} (ht : t ∈ Oₐ) (ht' : t' ∈ Oₐ) :
    ∃ σ : K ≃ₐ[k] K, (Dₚ).action σ t = t' := by
  have horb := baseRoot_orbit k K f j hP hf hcent hT ν hν hGK hi hjc ha
  have h1 : rootOf k K j hP t.1 ∈ MulAction.orbit (K ≃ₐ[k] K)
      (baseRoot k K f j hP hf hcent hT ν hν hGK hi ha) := by
    rw [horb]
    exact rootOf_mem_restrictionFiber k K f j hP hf hcent hT ν hν hGK hi t ht
  have h2 : rootOf k K j hP t'.1 ∈ MulAction.orbit (K ≃ₐ[k] K)
      (baseRoot k K f j hP hf hcent hT ν hν hGK hi ha) := by
    rw [horb]
    exact rootOf_mem_restrictionFiber k K f j hP hf hcent hT ν hν hGK hi t' ht'
  rw [← MulAction.orbit_eq_iff.mpr h1] at h2
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp h2
  refine ⟨σ, Subtype.ext (P.root.injective ?_)⟩
  rw [fiberPinning_action_root k K f j hP hf hcent hT ν hν hGK hi]
  exact congrArg Subtype.val hσ

variable (h2a : 2 • a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))

omit [LocallyOfFiniteType G.X.hom] [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
  [Finite J] [FiniteDimensional k K] [IsGalois k K] [P.IsReduced] in
include hP hT hGK hi in
/-- The absolute root datum has no root `2 • β`. -/
theorem root_add_root_notMem (r : J) : P.root r + P.root r ∉ Set.range P.root := by
  intro h
  apply RootPairNoncommutation.hasNoHigherRoots hGK hT hi hP r 2 le_rfl
  rw [two_nsmul, relativeRoots_eq_roots, ← hP.2.1]
  exact h

include hjc ha h2a in
/-- **Existence of a companion.** When `2 • a` is a relative root, every member of the fiber
of `a` has a non-orthogonal companion in its orbit. -/
theorem exists_companion {t : (Dₚ).pinning.base.support} (ht : t ∈ Oₐ) :
    ∃ σ : K ≃ₐ[k] K, (Dₚ).action σ t ≠ t ∧
      ¬ P.IsOrthogonal t.1 ((Dₚ).action σ t).1 := by
  have hS : IsSplitTorus S.toGrp := hf.1.1
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have hzero := root_restrict_ne_zero_of_torusCentralizer k K f j hS hT hcent
  obtain ⟨r, r', σ, ⟨hr, hr', hpair, -⟩, hσ, -⟩ :=
    MultipliableRootNoncommutation.exists_partner k K f j hS
      (hf.of_comp hjc).isLargestSplitSubtorus hT hi.2.1 hP hzero
      (root_add_root_notMem k K j hP hT hGK hi) ha.1.1 h2a
  obtain ⟨s, hs, hsr⟩ := exists_mem_fiberSet k K f j hP hf hcent hT ν hν hGK hi ha r
    ((restrictCharacter_eq_iff k K f hf.1.1 _ a).mpr hr)
  obtain ⟨s', hs', hsr'⟩ := exists_mem_fiberSet k K f j hP hf hcent hT ν hν hGK hi ha r'
    ((restrictCharacter_eq_iff k K f hf.1.1 _ a).mpr hr')
  have hσs : (Dₚ).action σ s = s' := by
    apply Subtype.ext
    apply P.root.injective
    rw [fiberPinning_action_root k K f j hP hf hcent hT ν hν hGK hi]
    rw [hsr, hsr', hσ]
  have hrr' : r ≠ r' := by
    rintro rfl
    rw [P.pairing_same] at hpair
    norm_num at hpair
  obtain ⟨γ, hγ⟩ := exists_action_eq k K f j hP hf hcent hT ν hν hGK hi hjc ha hs ht
  refine ⟨γ * σ * γ⁻¹, ?_, ?_⟩
  · rw [← hγ, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, map_inv,
      Equiv.Perm.inv_def, Equiv.symm_apply_apply, hσs]
    intro h
    apply hrr'
    rw [← hsr, ← hsr', (Equiv.injective _ h)]
  · rw [← hγ, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, map_inv,
      Equiv.Perm.inv_def, Equiv.symm_apply_apply, hσs]
    intro horth
    have h := horth.1
    rw [fiberPinning_pairing_action k K f j hP hf hcent hT ν hν hGK hi, hsr, hsr', hpair] at h
    norm_num at h


include hjc ha h2a in
/-- On the fiber of a multipliable simple relative root, the partner is a non-orthogonal
companion in the orbit. -/
theorem partner_spec_of_mem {t : (Dₚ).pinning.base.support} (ht : t ∈ Oₐ) :
    ∃ σ : K ≃ₐ[k] K, (Dₚ).action σ t = π t ∧ π t ≠ t ∧ ¬ P.IsOrthogonal t.1 (π t).1 :=
  partner_spec k K f j hP hf hcent hT ν hν hGK hi
    (exists_companion k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht)

include hjc ha h2a in
/-- The partner of a member of the fiber is different from it. -/
theorem partner_ne {t : (Dₚ).pinning.base.support} (ht : t ∈ Oₐ) : π t ≠ t :=
  (partner_spec_of_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht).choose_spec.2.1

include hjc ha h2a in
/-- A member of the fiber is not orthogonal to its partner. -/
theorem not_isOrthogonal_partner {t : (Dₚ).pinning.base.support} (ht : t ∈ Oₐ) :
    ¬ P.IsOrthogonal t.1 (π t).1 :=
  (partner_spec_of_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht).choose_spec.2.2

include hjc ha h2a in
/-- The partner of a member of the fiber lies in the fiber. -/
theorem partner_mem {t : (Dₚ).pinning.base.support} (ht : t ∈ Oₐ) : π t ∈ Oₐ := by
  obtain ⟨σ, hσ, -, -⟩ := partner_spec_of_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht
  rw [← hσ]
  exact (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a σ t).mp ht

include hjc ha h2a in
/-- A member of the fiber and its partner form an `A₂` pair: both pairings are `-1`. -/
theorem pairing_partner {t : (Dₚ).pinning.base.support} (ht : t ∈ Oₐ) :
    P.pairing t.1 (π t).1 = -1 ∧ P.pairing (π t).1 t.1 = -1 := by
  obtain ⟨σ, hσ, hne, ho⟩ := partner_spec_of_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht
  rw [← hσ] at hne ho ⊢
  exact pairing_eq_neg_one_of_not_isOrthogonal
    (fiberPinning_isPairingCompatible k K f j hP hf hcent hT ν hν hGK hi) t hne ho

include hjc ha h2a in
/-- A member of the fiber that is different from `t` and not orthogonal to it is the partner
of `t`. -/
theorem eq_partner_of_not_isOrthogonal {t t' : (Dₚ).pinning.base.support} (ht : t ∈ Oₐ)
    (ht' : t' ∈ Oₐ) (hne : t' ≠ t) (ho : ¬ P.IsOrthogonal t.1 t'.1) : t' = π t := by
  obtain ⟨σ, hσ, hσne, hσo⟩ := partner_spec_of_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht
  obtain ⟨γ, hγ⟩ := exists_action_eq k K f j hP hf hcent hT ν hν hGK hi hjc ha ht ht'
  rw [← hσ] at hσne hσo ⊢
  rw [← hγ] at hne ho ⊢
  exact eq_of_not_isOrthogonal
    (fiberPinning_isPairingCompatible k K f j hP hf hcent hT ν hν hGK hi) t hne hσne ho hσo

include hjc ha h2a in
/-- Two members of the fiber that are neither equal nor partners are orthogonal. -/
theorem isOrthogonal_of_ne_partner {t t' : (Dₚ).pinning.base.support} (ht : t ∈ Oₐ)
    (ht' : t' ∈ Oₐ) (hne : t' ≠ t) (hne' : t' ≠ π t) : P.IsOrthogonal t.1 t'.1 := by
  by_contra ho
  exact hne' (eq_partner_of_not_isOrthogonal k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a
    ht ht' hne ho)

include hjc ha h2a in
/-- The partner of the partner is the original member. -/
theorem partner_partner {t : (Dₚ).pinning.base.support} (ht : t ∈ Oₐ) : π (π t) = t := by
  have hp := partner_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht
  refine (eq_partner_of_not_isOrthogonal k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hp ht
    (partner_ne k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht).symm ?_).symm
  intro ho
  exact not_isOrthogonal_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht ho.symm

include hjc ha h2a in
/-- The partner map commutes with the Galois action on the fiber. -/
theorem partner_action (σ : K ≃ₐ[k] K) {t : (Dₚ).pinning.base.support} (ht : t ∈ Oₐ) :
    π ((Dₚ).action σ t) = (Dₚ).action σ (π t) := by
  have hσt := (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a σ t).mp ht
  have hσp := (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a σ (π t)).mp
    (partner_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht)
  refine (eq_partner_of_not_isOrthogonal k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a
    hσt hσp ?_ ?_).symm
  · intro h
    exact partner_ne k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht ((Equiv.injective _) h)
  · intro ho
    apply not_isOrthogonal_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht
    refine ⟨?_, ?_⟩
    · rw [← fiberPinning_pairing_action k K f j hP hf hcent hT ν hν hGK hi σ]
      exact ho.1
    · rw [← fiberPinning_pairing_action k K f j hP hf hcent hT ν hν hGK hi σ]
      exact ho.2

include hjc ha h2a in
/-- The sum of the roots of a member of the fiber and its partner is a root. -/
theorem exists_root_eq_add_partner {t : (Dₚ).pinning.base.support} (ht : t ∈ Oₐ) :
    ∃ m : J, P.root m = P.root t.1 + P.root (π t).1 := by
  obtain ⟨σ, hσ, hne, ho⟩ := partner_spec_of_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht
  rw [← hσ] at hne ho ⊢
  exact exists_root_eq_add_of_not_isOrthogonal
    (fiberPinning_isPairingCompatible k K f j hP hf hcent hT ν hν hGK hi) t hne ho

include hjc ha h2a in
/-- **Roots over `2 • a`.** Every absolute root restricting to `2 • a` is the sum of the roots
of a member of the fiber of `a` and of its partner. -/
theorem exists_mem_root_eq_add_partner (m : J)
    (hm : CategoryTheory.Functor.map (CommGroupScheme.baseChange bK) f ≫ P.root m =
      characterLattice.baseChange bK S (2 • a)) :
    ∃ t ∈ Oₐ, P.root m = P.root t.1 + P.root (π t).1 := by
  classical
  have : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  have hS : IsSplitTorus S.toGrp := hf.1.1
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have hzero := root_restrict_ne_zero_of_torusCentralizer k K f j hS hT hcent
  have hTt : IsTorus T.toGrp := ⟨K, inferInstance, inferInstance, hT⟩
  let ρ := IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k K j hT hi.2.1 hP
  have hsum : ∀ m : J, RootPairing.OrbitPartner.orbitSum P ρ m =
      CharacterAveraging.galoisOrbitSum k K T (P.root m) :=
    RootPartnerFields.orbitSum_eq_galoisOrbitSum k K hT hi.2.1 hP
  have hne : ∀ m : J, RootPairing.OrbitPartner.orbitSum P ρ m ≠ 0 :=
    RootPartnerFields.orbitSum_ne_zero k K hT hi.2.1 hP
      (fun γ => galoisOrbitSum_ne_zero_of_restrict_ne_zero k K f hS (hzero γ))
  have hrestrict : ∀ (σ : K ≃ₐ[k] K) (m : J),
      CategoryTheory.Functor.map (CommGroupScheme.baseChange bK) f ≫ P.root m =
          characterLattice.baseChange bK S a →
        CategoryTheory.Functor.map (CommGroupScheme.baseChange bK) f ≫ P.root (ρ σ • m) =
          characterLattice.baseChange bK S a := by
    intro σ m hm
    have h := rootsGaloisAction_mem_restrictionFiber k K j f a σ
      (β := rootOf k K j hP m) hm
    rw [RootPartnerFields.root_smul k K hT hi.2.1 hP σ m]
    exact h
  have h0 := basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha
  have hpa := (mem_fiberSet_iff k K f j hP hf hcent hT ν hν hGK hi a _).mp h0
  set p : J := p₀.1 with hp
  have horbit : RootPairing.OrbitPartner.orbitSum P ρ m =
      2 • RootPairing.OrbitPartner.orbitSum P ρ p := by
    rw [hsum, hsum]
    have h1 : CharacterAveraging.galoisOrbitSum k K T (P.root m) =
        CharacterAveraging.galoisOrbitSum k K T
          (2 • P.root p) :=
      IsLargestSplitSubtorus.galoisOrbitSum_eq_of_restrict_eq k K f
        (hf.of_comp hjc).isLargestSplitSubtorus hTt
        (by rw [hm, Preadditive.comp_nsmul,
          ← fiberPinning_root k K f j hP hf hcent hT ν hν hGK hi, hpa, map_nsmul])
    rw [h1]
    simp only [CharacterAveraging.galoisOrbitSum, CocharacterAveraging.orbitSum, map_nsmul,
      Finset.smul_sum]
  obtain ⟨g, q, hmq, hq⟩ :=
    RootPairing.OrbitPartner.exists_root_eq_add_of_orbitSum_eq_two_nsmul hne horbit
  have hqr : P.rootOrbitSum ρ q = P.rootOrbitSum ρ (ρ g • p) := by
    change RootPairing.OrbitPartner.orbitSum P ρ q =
      RootPairing.OrbitPartner.orbitSum P ρ (ρ g • p)
    rw [hq, RootPairing.OrbitPartner.orbitSum_smul]
  obtain ⟨σ, hσ⟩ := P.exists_smul_eq_of_rootOrbitSum_eq ρ hqr hne
  have hpartner : RootPairing.OrbitPartner.IsOrbitPartner P ρ
      (ρ g • p) q :=
    RootPairing.OrbitPartner.isOrbitPartner_of_root_eq_add
      (root_add_root_notMem k K j hP hT hGK hi) ⟨σ, hσ⟩ hmq
  have h1 := hrestrict g _ hpa
  have h2 : CategoryTheory.Functor.map (CommGroupScheme.baseChange bK) f ≫ P.root q =
      characterLattice.baseChange bK S a := by
    rw [← hσ]
    exact hrestrict σ _ h1
  obtain ⟨s, hs, hsr⟩ := exists_mem_fiberSet k K f j hP hf hcent hT ν hν hGK hi ha _
    ((restrictCharacter_eq_iff k K f hS _ a).mpr h1)
  obtain ⟨s', hs', hsr'⟩ := exists_mem_fiberSet k K f j hP hf hcent hT ν hν hGK hi ha q
    ((restrictCharacter_eq_iff k K f hS _ a).mpr h2)
  have hss' : s' = π s := by
    apply eq_partner_of_not_isOrthogonal k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hs hs'
    · intro h
      apply hpartner.2.1
      rw [← hsr, ← hsr', h]
    · intro ho
      have hp := hpartner.pairing_eq_neg_one hne
      rw [← hsr, ← hsr', ho.1] at hp
      norm_num at hp
  refine ⟨s, hs, ?_⟩
  rw [hmq, ← hsr, ← hsr', hss']

include hjc ha h2a in
/-- The sum of the roots of the base point and of its partner is an actual root. -/
theorem baseRoot_add_partner_mem :
    P.root p₀.1 + P.root (π p₀).1 ∈ roots (T := T_K) (G := G_K) j_K := by
  obtain ⟨m, hm⟩ := exists_root_eq_add_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a
    (basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha)
  rw [← hm]
  exact root_mem_roots k K j hP m

/-- The actual root `β₀ + β₀'` of the base point and its partner. Its restriction is
`2 • a`. -/
def pairRoot : roots (T := T_K) (G := G_K) j_K :=
  ⟨P.root p₀.1 + P.root (π p₀).1,
    baseRoot_add_partner_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a⟩

/-- The field of the pair root, the fixed field of its Galois stabilizer. -/
abbrev pairField : IntermediateField k K :=
  rootOrbitField k K j (pairRoot k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a)

local notation "β₀" => baseRoot k K f j hP hf hcent hT ν hν hGK hi ha
local notation "β₀'" => rootOf k K j hP (Subtype.val (π p₀))
local notation "E₀" => pairField k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a
local notation "L₀" => fiberField k K f j hP hf hcent hT ν hν hGK hi ha

include hjc ha h2a in
/-- The root of the base point and that of its partner are root partners. -/
theorem baseRoot_isRootPartner : RootPartnerFields.IsRootPartner k K j β₀ β₀' := by
  obtain ⟨σ, hσ, hne, -⟩ := partner_spec_of_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a
    (basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha)
  refine ⟨⟨σ, ?_⟩, ?_, baseRoot_add_partner_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a⟩
  · apply Subtype.ext
    rw [rootsGaloisAction_coe]
    change _ = P.root (π p₀).1
    rw [← hσ, fiberPinning_action_root k K f j hP hf hcent hT ν hν hGK hi]
    rfl
  · intro h
    apply hne
    apply Subtype.ext
    apply P.root.injective
    exact congrArg Subtype.val h

omit [IsGalois k K] [FiniteDimensional k K] in
include hf hcent hT in
/-- No actual root has zero Galois orbit sum. -/
theorem galoisOrbitSum_ne_zero [Fintype (K ≃ₐ[k] K)]
    (γ : roots (T := T_K) (G := G_K) j_K) :
    CharacterAveraging.galoisOrbitSum k K T γ.val ≠ 0 := by
  have hS : IsSplitTorus S.toGrp := hf.1.1
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  exact galoisOrbitSum_ne_zero_of_restrict_ne_zero k K f hS
    (root_restrict_ne_zero_of_torusCentralizer k K f j hS hT hcent γ)

include hjc ha h2a in
/-- The pair field lies in the fiber field. -/
theorem pairField_le : E₀ ≤ L₀ := by
  classical
  have : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  exact RootPartnerFields.rootOrbitField_le k K hT hi.2.1 hP
    (galoisOrbitSum_ne_zero k K f j hf hcent hT)
    (baseRoot_isRootPartner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a) rfl

/-- The fiber field is an algebra over the pair field through the inclusion. -/
instance pairAlgebra : Algebra E₀ L₀ :=
  Langlands.Algebra.QuadraticFixedFields.nestedAlgebra _ _
    (pairField_le k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a)

instance pairField_isScalarTower : IsScalarTower E₀ L₀ K :=
  Langlands.Algebra.QuadraticFixedFields.nestedAlgebra_isScalarTower _ _
    (pairField_le k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a)

instance pairField_isScalarTower_base : IsScalarTower k E₀ L₀ :=
  Langlands.Algebra.QuadraticFixedFields.isScalarTower_base _ _

/-- The fiber field is a quadratic extension of the pair field. -/
instance pairField_isQuadraticExtension : Algebra.IsQuadraticExtension E₀ L₀ := by
  classical
  have : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  exact RootPartnerFields.isQuadraticExtension k K hT hi.2.1 hP
    (galoisOrbitSum_ne_zero k K f j hf hcent hT)
    (baseRoot_isRootPartner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a) rfl

/-- The fiber field is separable over the pair field. -/
instance pairField_isSeparable : Algebra.IsSeparable E₀ L₀ :=
  RootPartnerFields.isSeparable k K (j := j)

include hjc ha h2a in
/-- **Partner embeddings.** The embedding of the fiber field attached to the partner of a
member `t` of the fiber is the embedding attached to `t` composed with the conjugation of the
fiber field over the pair field. -/
theorem fiberEmbedding_partner {t : (Dₚ).pinning.base.support} (ht : t ∈ Oₐ) (x : L₀) :
    fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha (π t) x =
      fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha t
        (SU3Root.conjugation E₀ L₀ x) := by
  classical
  have : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  have h0 := basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha
  obtain ⟨σ, hσ, -, -⟩ := partner_spec_of_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a h0
  obtain ⟨γ, hγ⟩ := exists_action_eq k K f j hP hf hcent hT ν hν hGK hi hjc ha h0 ht
  have hσβ : σ • β₀ = β₀' := by
    obtain ⟨⟨σ', hσ'⟩, -, -⟩ := baseRoot_isRootPartner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a
    apply Subtype.ext
    rw [rootsGaloisAction_coe]
    change _ = P.root (π p₀).1
    rw [← hσ, fiberPinning_action_root k K f j hP hf hcent hT ν hν hGK hi]
    rfl
  have hπ : π t = (Dₚ).action γ (π p₀) := by
    rw [← hγ, partner_action k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a γ h0]
  have hσ0 := (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a σ _).mp h0
  rw [hπ, ← hσ, fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha γ _ hσ0,
    fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha σ _ h0, ← hγ,
    fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha γ _ h0]
  simp only [AlgHom.comp_apply, fiberEmbedding_basePoint]
  congr 1
  exact (RootPartnerFields.conjugation_apply k K hT hi.2.1 hP
    (galoisOrbitSum_ne_zero k K f j hf hcent hT)
    (baseRoot_isRootPartner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a) rfl
    hσβ x).symm

include hjc ha h2a in
/-- A member of the fiber and its partner restrict to the same embedding of the pair field. -/
theorem fiberEmbedding_partner_algebraMap {t : (Dₚ).pinning.base.support} (ht : t ∈ Oₐ)
    (y : E₀) :
    fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha (π t) (algebraMap E₀ L₀ y) =
      fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha t (algebraMap E₀ L₀ y) := by
  rw [fiberEmbedding_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht, AlgEquiv.commutes]

end Field

end SimpleRootFiber

end Langlands.GroupScheme
