import Langlands.AlgebraicGeometry.FiniteEtale.CoverPointStabilizer
import Langlands.AlgebraicGeometry.FiniteEtale.KummerCyclicQuotient
import Langlands.AlgebraicGeometry.FiniteEtale.KummerFactorizationStatement
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Proof of Kummer factorization over a strictly Henselian regular local ring

This module proves `StrictlyHenselianKummerFactorizationStatement`. Write `ℓ^k` for the order
of the target group of `ρ` and take `N = ℓ^(k+1)`. For nontrivial `ρ`, the image of the product
of `ρ` with the level-`N` Kummer character is a nontrivial finite `ℓ`-group. The kernels of all
its order-`ℓ` quotients pull back to the kernel of the level-`ℓ` character, so the image is
cyclic. Any such quotient also gives nontriviality of the level-`ℓ` character and hence
surjectivity of the level-`N` character. The image has exponent dividing `N`, so its
surjective projection onto the `N`-th roots of unity is an isomorphism. This puts the
level-`N` kernel inside `ker ρ`. The image of the fundamental group of the pointed Kummer
cover lies in the level-`N` kernel because it fixes the chosen fibre point.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Langlands.AlgebraicGeometry.FiniteEtale

section GroupTheory

variable {G : Type*} [Group G]

/-- A subgroup of index `ℓ` of a finite `ℓ`-group is the kernel of a surjective homomorphism
onto any group of order `ℓ`. -/
theorem exists_surjective_ker_eq_of_index_eq {P : Type*} [Group P] [Finite P] {ℓ : ℕ}
    [hℓ : Fact ℓ.Prime] (hP : IsPGroup ℓ P) (M : Type*) [Group M] (hM : Nat.card M = ℓ)
    (Q : Subgroup P) (hQ : Q.index = ℓ) :
    ∃ χ : P →* M, Function.Surjective χ ∧ χ.ker = Q := by
  have := hP.isNilpotent
  have : Q.Normal := Subgroup.NormalizerCondition.normal_of_coatom Q
    Group.normalizerCondition_of_isNilpotent ((hP.isCoatom_iff_index_eq_prime).mpr hQ)
  let e : P ⧸ Q ≃* M := mulEquivOfPrimeCardEq (show Nat.card (P ⧸ Q) = ℓ from hQ) hM
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' Q),
    e.surjective.comp (QuotientGroup.mk'_surjective Q), ?_⟩
  ext g
  simp

/-- A nontrivial finite `ℓ`-group has a subgroup of index `ℓ`. -/
theorem exists_index_eq_prime {P : Type*} [Group P] [Finite P] [Nontrivial P] {ℓ : ℕ}
    [Fact ℓ.Prime] (hP : IsPGroup ℓ P) : ∃ Q : Subgroup P, Q.index = ℓ := by
  have := hP.isNilpotent
  obtain h | ⟨Q, hQ, -⟩ := IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup P)
  · exact absurd h bot_ne_top
  · exact ⟨Q, (hP.isCoatom_iff_index_eq_prime).mp hQ⟩

/-- **Cyclicity criterion.** Let `f : G →* P` be a surjective homomorphism onto a finite
`ℓ`-group and `M` a group of order `ℓ`. If every surjective homomorphism `P →* M` has kernel
pulling back along `f` to the same subgroup `K` of `G`, then `P` is cyclic. -/
theorem isCyclic_of_forall_ker_comp_eq {P : Type*} [Group P] [Finite P] {ℓ : ℕ}
    [Fact ℓ.Prime] (hP : IsPGroup ℓ P) (f : G →* P) (hf : Function.Surjective f) (M : Type*)
    [Group M] (hM : Nat.card M = ℓ) (K : Subgroup G)
    (hK : ∀ χ : P →* M, Function.Surjective χ → (χ.comp f).ker = K) : IsCyclic P := by
  have := hP.isNilpotent
  by_contra hcyc
  obtain ⟨Q₁, Q₂, hne, h₁, h₂⟩ := (hP.not_isCyclic_iff_exists_ne_index_eq_prime).mp hcyc
  have key : ∀ Q : Subgroup P, Q.index = ℓ → Q.comap f = K := by
    intro Q hQ
    obtain ⟨χ, hχ, hχQ⟩ := exists_surjective_ker_eq_of_index_eq hP M hM Q hQ
    rw [← hK χ hχ, ← hχQ, MonoidHom.comap_ker]
  apply hne
  rw [← Subgroup.map_comap_eq_self_of_surjective hf Q₁,
    ← Subgroup.map_comap_eq_self_of_surjective hf Q₂, key Q₁ h₁, key Q₂ h₂]

/-- Two homomorphisms to a group of prime order, the first surjective and the second
nontrivial, whose kernels are nested, have the same kernel. -/
theorem ker_eq_ker_of_le {M : Type*} [Group M] {ℓ : ℕ} (hℓ : ℓ.Prime) (hM : Nat.card M = ℓ)
    (χ κ : G →* M) (hχ : Function.Surjective χ) (hκ : κ ≠ 1) (hle : χ.ker ≤ κ.ker) :
    χ.ker = κ.ker := by
  have hχi : χ.ker.index = ℓ := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hχ, Subgroup.card_top, hM]
  have hκi : κ.ker.index = ℓ := by
    rw [Subgroup.index_ker]
    have hd : Nat.card κ.range ∣ ℓ := hM ▸ Subgroup.card_subgroup_dvd_card _
    rcases (Nat.dvd_prime hℓ).mp hd with h | h
    · exact absurd (MonoidHom.range_eq_bot_iff.mp (Subgroup.card_eq_one.mp h)) hκ
    · exact h
  refine le_antisymm hle ?_
  have h := Subgroup.relIndex_mul_index hle
  rw [hχi, hκi] at h
  exact Subgroup.relIndex_eq_one.mp (Nat.eq_of_mul_eq_mul_right hℓ.pos (h.trans (one_mul ℓ).symm))

/-- If `κ : G → M` is surjective, every element of `H` has order dividing `|M|`, and the image
of `(ρ, κ) : G → H × M` is cyclic, then `ker κ ≤ ker ρ`. -/
theorem ker_le_ker_of_isCyclic_range {H M : Type*} [Group H] [Group M] [Finite H] [Finite M]
    (ρ : G →* H) (κ : G →* M) (hκ : Function.Surjective κ)
    (hcyc : IsCyclic (ρ.prod κ).range) (hexp : ∀ h : H, h ^ Nat.card M = 1) :
    κ.ker ≤ ρ.ker := by
  have hPexp : ∀ p : (ρ.prod κ).range, p ^ Nat.card M = 1 := by
    intro p
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact Prod.ext ((map_pow (MonoidHom.fst H M) _ _).trans (hexp _))
      ((map_pow (MonoidHom.snd H M) _ _).trans pow_card_eq_one')
  have hcard : Nat.card (ρ.prod κ).range ≤ Nat.card M := by
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd Nat.card_pos (Monoid.exponent_dvd_of_forall_pow_eq_one hPexp)
  let π : (ρ.prod κ).range →* M := (MonoidHom.snd H M).comp (ρ.prod κ).range.subtype
  have hπ : ∀ g, π ((ρ.prod κ).rangeRestrict g) = κ g := fun g => rfl
  have hπs : Function.Surjective π := fun m => by
    obtain ⟨g, rfl⟩ := hκ m
    exact ⟨_, hπ g⟩
  have hπi := (hπs.bijective_of_nat_card_le hcard).1
  intro g hg
  rw [MonoidHom.mem_ker] at hg ⊢
  have h1 : (ρ.prod κ).rangeRestrict g = 1 := hπi (by rw [hπ, hg, map_one])
  have h2 := congrArg (fun p : (ρ.prod κ).range => (p : H × M).1) h1
  simpa using h2

end GroupTheory

section Surjective

theorem isUnit_natCast_prime_pow {R : Type*} [CommRing R] {ℓ : ℕ} (hℓR : IsUnit (ℓ : R))
    (k : ℕ) : IsUnit ((ℓ ^ k : ℕ) : R) := by
  rw [Nat.cast_pow]
  exact hℓR.pow k

variable {R : Type u} [CommRing R] [IsDomain R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)] (t : R) {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓR : IsUnit (ℓ : R))
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of (Localization.Away t)))

include hℓR in
/-- If the Kummer character of level `ℓ` of `t` is nontrivial, then the Kummer character of
level `ℓ^(k+1)` of `t` is surjective onto the `ℓ^(k+1)`-th roots of unity of `R`. -/
theorem parameterKummerCharacter_surjective (k : ℕ)
    (hne : parameterKummerCharacter t x ℓ hℓ.out.ne_zero hℓR ≠ 1) :
    Function.Surjective (parameterKummerCharacter t x (ℓ ^ (k + 1))
      (pow_ne_zero _ hℓ.out.ne_zero) (isUnit_natCast_prime_pow hℓR (k + 1))) := by
  have hℓ0 : ℓ ≠ 0 := hℓ.out.ne_zero
  have hN0 : ℓ ^ (k + 1) ≠ 0 := pow_ne_zero _ hℓ0
  have hNR := isUnit_natCast_prime_pow hℓR (k + 1)
  obtain ⟨g₀, hg₀⟩ := DFunLike.ne_iff.mp hne
  rw [MonoidHom.one_apply] at hg₀
  have hlev := kummerCharacter_level (algebraMap R (Localization.Away t) t)
    (IsLocalization.Away.algebraMap_isUnit t) (m := ℓ) (d := ℓ ^ k) (n := ℓ ^ (k + 1))
    (by ring) hℓ0 (isUnit_natCast_away t hℓR) hN0 (isUnit_natCast_away t hNR) x
    (geometricFiberFinite x) R hℓR hNR (card_rootsOfUnity_eq hℓR hℓ0)
    (card_rootsOfUnity_eq hNR hN0) g₀
  have hord : orderOf (parameterKummerCharacter t x (ℓ ^ (k + 1)) hN0 hNR g₀) =
      ℓ ^ (k + 1) := by
    apply orderOf_eq_prime_pow
    · intro h
      apply hg₀
      apply Subtype.ext
      apply Units.ext
      have h' := congrArg (fun ζ : rootsOfUnity (ℓ ^ (k + 1)) R => ((ζ : Rˣ) : R)) h
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one] at h'
      change ((parameterKummerCharacter t x ℓ hℓ0 hℓR g₀ : Rˣ) : R) = 1
      exact hlev.trans h'
    · have h := pow_card_eq_one' (x := parameterKummerCharacter t x (ℓ ^ (k + 1)) hN0 hNR g₀)
      rwa [card_rootsOfUnity_eq hNR hN0] at h
  have htop : Subgroup.zpowers (parameterKummerCharacter t x (ℓ ^ (k + 1)) hN0 hNR g₀) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, card_rootsOfUnity_eq hNR hN0])
  intro z
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top z)
  exact ⟨g₀ ^ j, by rw [map_zpow, hj]⟩

end Surjective

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsRegularLocalRing R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)] {t : R} (ht : t ∈ maximalIdeal R)
  (ht2 : t ∉ maximalIdeal R ^ 2) {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓR : IsUnit (ℓ : R))
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of (Localization.Away t)))

include ht ht2 in
/-- **Kummer factorization of characters.** For a continuous homomorphism `ρ` from
`π₁(Spec R[1/t], x)` to a finite discrete group of order `ℓ^k`, the kernel of the Kummer
character of level `ℓ^(k+1)` of `t` lies in the kernel of `ρ`. -/
theorem ker_parameterKummerCharacter_le_ker {H : Type v} [Group H] [Finite H]
    [TopologicalSpace H] [DiscreteTopology H] {k : ℕ} (hk : Nat.card H = ℓ ^ k)
    (ρ : FundamentalGroup x (geometricFiberFinite x) →* H) (hρ : Continuous ρ) :
    (parameterKummerCharacter t x (ℓ ^ (k + 1)) (pow_ne_zero _ hℓ.out.ne_zero)
      (isUnit_natCast_prime_pow hℓR (k + 1))).ker ≤ ρ.ker := by
  have hℓ0 : ℓ ≠ 0 := hℓ.out.ne_zero
  have hN0 : ℓ ^ (k + 1) ≠ 0 := pow_ne_zero _ hℓ0
  have hNR := isUnit_natCast_prime_pow hℓR (k + 1)
  by_cases hρ1 : ρ = 1
  · intro g _
    rw [hρ1, MonoidHom.mem_ker, MonoidHom.one_apply]
  have hNcard := card_rootsOfUnity_eq hNR hN0
  have hℓcard := card_rootsOfUnity_eq hℓR hℓ0
  have : Finite (rootsOfUnity (ℓ ^ (k + 1)) R) :=
    Nat.finite_of_card_ne_zero (by rw [hNcard]; exact hN0)
  have : Finite (rootsOfUnity ℓ R) := Nat.finite_of_card_ne_zero (by rw [hℓcard]; exact hℓ0)
  have hP : IsPGroup ℓ (ρ.prod (parameterKummerCharacter t x (ℓ ^ (k + 1)) hN0 hNR)).range :=
    (IsPGroup.of_card (n := k + (k + 1))
      (by rw [Nat.card_prod, hk, hNcard, ← pow_add])).to_subgroup _
  have hopen : IsOpen (((ρ.prod (parameterKummerCharacter t x (ℓ ^ (k + 1)) hN0 hNR)).ker :
      Subgroup (FundamentalGroup x (geometricFiberFinite x))) :
        Set (FundamentalGroup x (geometricFiberFinite x))) := by
    rw [MonoidHom.ker_prod, Subgroup.coe_inf]
    refine IsOpen.inter ?_ (isOpen_ker_kummerCharacter _ _ _ _ _ x _ R hNR hNcard)
    rw [MonoidHom.coe_ker]
    exact hρ.isOpen_preimage _ (isOpen_discrete _)
  have hχ : ∀ χ : (ρ.prod (parameterKummerCharacter t x (ℓ ^ (k + 1)) hN0 hNR)).range →*
      rootsOfUnity ℓ R, Function.Surjective χ →
      (χ.comp (ρ.prod (parameterKummerCharacter t x (ℓ ^ (k + 1)) hN0 hNR)).rangeRestrict).ker =
        (parameterKummerCharacter t x ℓ hℓ0 hℓR).ker ∧
      parameterKummerCharacter t x ℓ hℓ0 hℓR ≠ 1 := by
    intro χ hχs
    have hs : Function.Surjective
        (χ.comp (ρ.prod (parameterKummerCharacter t x (ℓ ^ (k + 1)) hN0 hNR)).rangeRestrict) :=
      hχs.comp (MonoidHom.rangeRestrict_surjective _)
    have ho : IsOpen ((χ.comp (ρ.prod
        (parameterKummerCharacter t x (ℓ ^ (k + 1)) hN0 hNR)).rangeRestrict).ker :
          Set (FundamentalGroup x (geometricFiberFinite x))) := by
      refine Subgroup.isOpen_mono ?_ hopen
      intro g hg
      rw [MonoidHom.mem_ker] at hg ⊢
      rw [MonoidHom.comp_apply,
        show (ρ.prod (parameterKummerCharacter t x (ℓ ^ (k + 1)) hN0 hNR)).rangeRestrict g = 1
          from Subtype.ext hg, map_one]
    obtain ⟨hle, hne⟩ := ker_le_ker_parameterKummerCharacter ht ht2 hℓR x _ hs ho
    exact ⟨ker_eq_ker_of_le hℓ.out hℓcard _ _ hs hne hle, hne⟩
  have hcyc := isCyclic_of_forall_ker_comp_eq hP _
    (MonoidHom.rangeRestrict_surjective _) (rootsOfUnity ℓ R) hℓcard _ (fun χ hχs => (hχ χ hχs).1)
  have hnt : Nontrivial (ρ.prod (parameterKummerCharacter t x (ℓ ^ (k + 1)) hN0 hNR)).range := by
    obtain ⟨g, hg⟩ := DFunLike.ne_iff.mp hρ1
    rw [MonoidHom.one_apply] at hg
    refine ⟨⟨(ρ.prod (parameterKummerCharacter t x (ℓ ^ (k + 1)) hN0 hNR)).rangeRestrict g, 1,
      fun h => hg ?_⟩⟩
    have h2 := congrArg (fun p : (ρ.prod
      (parameterKummerCharacter t x (ℓ ^ (k + 1)) hN0 hNR)).range => p.1.1) h
    simpa using h2
  obtain ⟨Q, hQ⟩ := exists_index_eq_prime hP
  obtain ⟨χ, hχs, -⟩ := exists_surjective_ker_eq_of_index_eq hP (rootsOfUnity ℓ R) hℓcard Q hQ
  have hκs := parameterKummerCharacter_surjective t hℓR x k (hχ χ hχs).2
  refine ker_le_ker_of_isCyclic_range ρ _ hκs hcyc fun h => ?_
  rw [hNcard, pow_succ, pow_mul, ← hk, pow_card_eq_one', one_pow]

end Main

/-- **Kummer factorization over a strictly Henselian regular local ring.** Every continuous
homomorphism from `π₁(Spec R[1/t], x)` to a finite discrete `ℓ`-group of order `ℓ^k` is
trivial on the image of the fundamental group of the Kummer cover of level `ℓ^(k+1)`. -/
theorem strictlyHenselianKummerFactorization :
    StrictlyHenselianKummerFactorizationStatement.{u, v} := by
  intro R _ _ _ _ _ t ht ht2 ℓ hℓ hℓR Ω _ _ x H _ _ _ _ hH ρ hρ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH
  have hℓ0 : ℓ ≠ 0 := hℓ.out.ne_zero
  have hN0 : ℓ ^ (k + 1) ≠ 0 := pow_ne_zero _ hℓ0
  have hNR := isUnit_natCast_prime_pow hℓR (k + 1)
  obtain ⟨p⟩ := kummerFiber_nonempty (algebraMap R (Localization.Away t) t) (ℓ ^ (k + 1)) hN0
    (isUnit_natCast_away t hNR) (IsLocalization.Away.algebraMap_isUnit t) x
  refine ⟨k + 1, p.left, Over.w p, ?_⟩
  ext g
  rw [MonoidHom.comp_apply, MonoidHom.one_apply, ← MonoidHom.mem_ker]
  apply ker_parameterKummerCharacter_le_ker ht ht2 hℓR x hk ρ hρ
  rw [parameterKummerCharacter, ker_kummerCharacter _ _ _ _ _ x _ R hNR _ p]
  exact fundamentalGroupMap_fixes_lift x (geometricFiberFinite x) _ p (geometricFiberFinite _) g

end Langlands.AlgebraicGeometry.FiniteEtale
