import Langlands.BushnellKutzko.SimpleCharacterClassCoverStatement
import Langlands.BushnellKutzko.SimpleCharacterHighIndex
import Langlands.BushnellKutzko.SimpleCharacterRestrictionHigh
import Langlands.BushnellKutzko.SimpleCharacterCovarianceStatement

/-! # Covering simple-character classes: the induction on the depth -/

open ValuativeRel
open Langlands.Group.RelativeWeyl

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uG

namespace CharacterPair

variable {G : Type uG} [Group G]

theorem ext_of_eq {P Q : CharacterPair G} (h : P.1 = Q.1)
    (hv : ∀ (g : G) (hP : g ∈ P.1) (hQ : g ∈ Q.1), P.2 ⟨g, hP⟩ = Q.2 ⟨g, hQ⟩) : P = Q := by
  obtain ⟨H, θ⟩ := P
  obtain ⟨K, χ⟩ := Q
  simp only at h
  subst h
  congr
  ext g
  exact congrArg Units.val (hv g g.2 g.2)

theorem mem_conj_fst {x : G} {P : CharacterPair G} {y : G} :
    y ∈ (P.conj x).1 ↔ x * y * x⁻¹ ∈ P.1 := by
  change y ∈ conjugateSubgroup x⁻¹ P.1 ↔ _
  rw [mem_conjSubgroup]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa [mul_assoc] using hj
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem conj_snd_apply (x : G) (P : CharacterPair G) (y : G) (hy : y ∈ (P.conj x).1)
    (h : x * y * x⁻¹ ∈ P.1) : (P.conj x).2 ⟨y, hy⟩ = P.2 ⟨x * y * x⁻¹, h⟩ := by
  change P.2 ((conjSubgroupEquiv x⁻¹ P.1).symm ⟨y, hy⟩) = _
  congr 1
  apply (conjSubgroupEquiv x⁻¹ P.1).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  simp [mul_assoc]

theorem conj_one (P : CharacterPair G) : P.conj 1 = P := by
  refine ext_of_eq ?_ ?_
  · ext y
    rw [mem_conj_fst]
    simp
  · intro g hP hQ
    rw [conj_snd_apply 1 P g hP (by simpa using hQ)]
    congr 1
    apply Subtype.ext
    simp

theorem conj_conj (x y : G) (P : CharacterPair G) : (P.conj x).conj y = P.conj (x * y) := by
  refine ext_of_eq ?_ ?_
  · ext z
    rw [mem_conj_fst, mem_conj_fst, mem_conj_fst]
    simp [mul_assoc]
  · intro g hP hQ
    have h1 : y * g * y⁻¹ ∈ (P.conj x).1 := mem_conj_fst.mp hP
    have h2 : x * (y * g * y⁻¹) * x⁻¹ ∈ P.1 := mem_conj_fst.mp h1
    rw [conj_snd_apply y _ g hP h1, conj_snd_apply x P _ h1 h2,
      conj_snd_apply (x * y) P g hQ (by simpa [mul_assoc] using h2)]
    congr 1
    apply Subtype.ext
    simp [mul_assoc]

section Conjugate

variable {U : Subgroup G}

theorem AreConjugateBy.refl (U : Subgroup G) (P : CharacterPair G) : AreConjugateBy U P P :=
  ⟨1, by simpa using conj_one P⟩

theorem AreConjugateBy.symm {P Q : CharacterPair G} (h : AreConjugateBy U P Q) :
    AreConjugateBy U Q P := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨x⁻¹, ?_⟩
  rw [conj_conj]
  simpa using conj_one P

theorem AreConjugateBy.trans {P Q R : CharacterPair G} (h : AreConjugateBy U P Q)
    (h' : AreConjugateBy U Q R) : AreConjugateBy U P R := by
  obtain ⟨x, rfl⟩ := h
  obtain ⟨y, rfl⟩ := h'
  exact ⟨x * y, by rw [conj_conj]; rfl⟩

theorem AreConjugateBy.of_conj (U : Subgroup G) (P : CharacterPair G) (x : U) :
    AreConjugateBy U P (P.conj x) :=
  ⟨x, rfl⟩

end Conjugate

/-- Restriction of a pair to the intersection of its subgroup with `K`. -/
def restrict (P : CharacterPair G) (K : Subgroup G) : CharacterPair G :=
  ⟨P.1 ⊓ K, P.2.comp (Subgroup.inclusion inf_le_left)⟩

theorem restrict_conj (P : CharacterPair G) (K : Subgroup G) (x : G)
    (hK : ∀ y, x * y * x⁻¹ ∈ K ↔ y ∈ K) :
    (P.conj x).restrict K = (P.restrict K).conj x := by
  refine ext_of_eq ?_ ?_
  · ext y
    change y ∈ (P.conj x).1 ⊓ K ↔ y ∈ ((P.restrict K).conj x).1
    rw [mem_conj_fst, Subgroup.mem_inf, mem_conj_fst]
    change _ ↔ x * y * x⁻¹ ∈ P.1 ⊓ K
    rw [Subgroup.mem_inf, hK]
  · intro g hP hQ
    have h1 : x * g * x⁻¹ ∈ P.1 ⊓ K := mem_conj_fst.mp hQ
    change (P.conj x).2 ⟨g, hP.1⟩ = _
    rw [conj_snd_apply x P g hP.1 h1.1, conj_snd_apply x (P.restrict K) g hQ h1]
    rfl

theorem AreConjugateBy.restrict {U : Subgroup G} {P Q : CharacterPair G} (K : Subgroup G)
    (hK : ∀ x ∈ U, ∀ y, x * y * x⁻¹ ∈ K ↔ y ∈ K) (h : AreConjugateBy U P Q) :
    AreConjugateBy U (P.restrict K) (Q.restrict K) := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨x, (restrict_conj P K x (hK x x.2)).symm⟩

end CharacterPair

namespace LatticeChain

variable {O : Type*} {K : Type*} {W : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W] (L : LatticeChain O K W)

/-- Conjugation by `U(𝔄)` preserves each `𝔓^j`. -/
theorem conj_mem_endFiltration {u : (Module.End K W)ˣ} (hu : u ∈ L.unitFiltration 0)
    {x : Module.End K W} {j : ℤ} (hx : x ∈ L.endFiltration j) :
    (↑u⁻¹ : Module.End K W) * x * (u : Module.End K W) ∈ L.endFiltration j := by
  have h1 := L.mul_mem_endFiltration ((L.mem_order_iff_mem_endFiltration).1 hu.2.1) hx
  have h2 := L.mul_mem_endFiltration h1 ((L.mem_order_iff_mem_endFiltration).1 hu.1)
  simpa using h2

private theorem conj_mem_unitFiltration_of_mem {v y : (Module.End K W)ˣ}
    (hv : v ∈ L.unitFiltration 0) {k : ℕ} (hy : y ∈ L.unitFiltration k) :
    v * y * v⁻¹ ∈ L.unitFiltration k := by
  have h0 : v * y * v⁻¹ ∈ L.unitFiltration 0 :=
    mul_mem (mul_mem hv (L.unitFiltration_antitone (Nat.zero_le k) hy)) (inv_mem hv)
  refine ⟨h0.1, h0.2.1, ?_⟩
  have h := L.conj_mem_endFiltration (inv_mem hv) hy.2.2
  have heq : ((v * y * v⁻¹ : (Module.End K W)ˣ) : Module.End K W) - 1 =
      (↑(v⁻¹)⁻¹ : Module.End K W) * ((y : Module.End K W) - 1) * ↑(v⁻¹) := by
    simp only [inv_inv, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]
  rw [heq]
  exact h

/-- `U^k(𝔄)` is normalized by `U(𝔄)`. -/
theorem conj_mem_unitFiltration_iff {u : (Module.End K W)ˣ} (hu : u ∈ L.unitFiltration 0)
    (k : ℕ) (y : (Module.End K W)ˣ) :
    u * y * u⁻¹ ∈ L.unitFiltration k ↔ y ∈ L.unitFiltration k := by
  refine ⟨fun h => ?_, L.conj_mem_unitFiltration_of_mem hu⟩
  have := L.conj_mem_unitFiltration_of_mem (inv_mem hu) h
  simpa [mul_assoc] using this

end LatticeChain

section Congruence

variable {O : Type*} {K : Type*} {W : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]

/-- `γ ≡ u⁻¹ β u (mod 𝔓^{-k})` for some `u ∈ U(𝔄)`. -/
def unitConjCongr (L : LatticeChain O K W) (k : ℤ) (β γ : Module.End K W) : Prop :=
  ∃ u ∈ L.unitFiltration 0,
    γ - (↑u⁻¹ : Module.End K W) * β * (u : Module.End K W) ∈ L.endFiltration (-k)

namespace unitConjCongr

variable {L : LatticeChain O K W} {k : ℤ}

theorem refl (L : LatticeChain O K W) (k : ℤ) (β : Module.End K W) : unitConjCongr L k β β :=
  ⟨1, one_mem _, by simp⟩

theorem symm {β γ : Module.End K W} (h : unitConjCongr L k β γ) : unitConjCongr L k γ β := by
  obtain ⟨u, hu, h⟩ := h
  refine ⟨u⁻¹, inv_mem hu, ?_⟩
  have h' := L.conj_mem_endFiltration (inv_mem hu) h
  have heq : β - (↑(u⁻¹)⁻¹ : Module.End K W) * γ * ↑(u⁻¹) =
      -((↑(u⁻¹)⁻¹ : Module.End K W) * (γ - (↑u⁻¹ : Module.End K W) * β * (u : Module.End K W)) *
        ↑(u⁻¹)) := by
    simp only [inv_inv, mul_sub, sub_mul, mul_assoc, Units.mul_inv, mul_one]
    simp only [← mul_assoc, Units.mul_inv, one_mul]
    abel
  rw [heq]
  exact neg_mem h'

theorem trans {β γ δ : Module.End K W} (h : unitConjCongr L k β γ)
    (h' : unitConjCongr L k γ δ) : unitConjCongr L k β δ := by
  obtain ⟨u, hu, h⟩ := h
  obtain ⟨v, hv, h'⟩ := h'
  refine ⟨u * v, mul_mem hu hv, ?_⟩
  have h2 := L.conj_mem_endFiltration hv h
  have heq : δ - (↑(u * v)⁻¹ : Module.End K W) * β * ↑(u * v) =
      (δ - (↑v⁻¹ : Module.End K W) * γ * (v : Module.End K W)) +
        (↑v⁻¹ : Module.End K W) * (γ - (↑u⁻¹ : Module.End K W) * β * (u : Module.End K W)) *
          (v : Module.End K W) := by
    simp only [mul_inv_rev, Units.val_mul, mul_sub, sub_mul, mul_assoc]
    abel
  rw [heq]
  exact add_mem h' h2

theorem mono {k' : ℤ} (hk : k ≤ k') {β γ : Module.End K W} (h : unitConjCongr L k β γ) :
    unitConjCongr L k' β γ := by
  obtain ⟨u, hu, h⟩ := h
  exact ⟨u, hu, L.endFiltration_antitone (by omega) h⟩

end unitConjCongr

end Congruence

/-- A representative function for the classes of an equivalence relation. -/
theorem exists_classRepresentative {α : Type*} (s : Setoid α) :
    ∃ f : α → α, (∀ a, s.r (f a) a) ∧ ∀ a b, s.r a b → f a = f b :=
  ⟨fun a => (Quotient.mk s a).out, fun a => Quotient.mk_out a,
    fun a b h => by simp only [Quotient.sound h]⟩

section Skeleton

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

variable (ψF : AddChar F ℂ) (L : LatticeChain 𝒪[F] F V) (n : ℤ)

/-- The conclusion of `SimpleCharacterClassCoverStatement` for fixed data and depth. -/
def ClassCoverAt (m : ℕ) : Prop :=
  ∃ Φ : SimpleStratumAt L n m → CharacterPair G,
    (∀ S, Φ S ∈ simpleCharacterPairs ψF S.1 m) ∧
    (∀ (S T : SimpleStratumAt L n m) (u : L.unitFiltration 0),
      let x : G := u
      T.1.b - ((↑x⁻¹ : A) * S.1.b * (↑x : A)) ∈ L.endFiltration (-(m : ℤ)) →
      CharacterPair.AreConjugateBy (L.unitFiltration 0) (Φ S) (Φ T)) ∧
    (∀ P ∈ simpleCharacterPairsAt ψF L n m,
      ∃ S : SimpleStratumAt L n m, CharacterPair.AreConjugateBy (L.unitFiltration 0) (Φ S) P)

/-- A choice of a simple stratum for each pair of `S^m_n(𝔄)` that is injective on classes. -/
def ClassInjectionAt (m : ℕ) : Prop :=
  ∃ κ : simpleCharacterPairsAt ψF L n m → SimpleStratumAt L n m,
    (∀ P, ∃ P' ∈ simpleCharacterPairs ψF (κ P).1 m,
      CharacterPair.AreConjugateBy (L.unitFiltration 0) P.1 P') ∧
    ∀ P Q, unitConjCongr L m (κ P).1.b (κ Q).1.b →
      CharacterPair.AreConjugateBy (L.unitFiltration 0) P.1 Q.1

/-- Restriction to `U^{m+2}(𝔄)` maps `S^m_n(𝔄)` into `S^{m+1}_n(𝔄)`. -/
def PairRestrictionAt (m : ℕ) : Prop :=
  ∀ P ∈ simpleCharacterPairsAt ψF L n m,
    P.restrict (L.unitFiltration (m + 2)) ∈ simpleCharacterPairsAt ψF L n (m + 1)

/-- For a simple stratum `[𝔄,n,m+1,γ]` on `L` and a pair `θ` of `Ĉ(𝔄,m+1,γ)`: on the pairs of
`S^m_n(𝔄)` whose restriction to `U^{m+2}(𝔄)` is `U(𝔄)`-conjugate to `θ`, a choice of a simple
stratum `[𝔄,n,m,β]` on `L` with `β ≡ γ (mod 𝔓^{-(m+1)})`, carrying a conjugate of the pair, that
is injective on classes. -/
def FibreInjectionAt (m : ℕ) : Prop :=
  ∀ (T : SimpleStratumAt L n ((m + 1 : ℕ) : ℤ)) (θ : CharacterPair G),
    θ ∈ simpleCharacterPairs ψF T.1 (m + 1) →
    ∃ κ : simpleCharacterPairsAt ψF L n m → SimpleStratumAt L n m,
      ∀ P : simpleCharacterPairsAt ψF L n m,
        CharacterPair.AreConjugateBy (L.unitFiltration 0)
          (P.1.restrict (L.unitFiltration (m + 2))) θ →
        (κ P).1.b - T.1.b ∈ L.endFiltration (-((m + 1 : ℕ) : ℤ)) ∧
        (∃ P' ∈ simpleCharacterPairs ψF (κ P).1 m,
          CharacterPair.AreConjugateBy (L.unitFiltration 0) P.1 P') ∧
        ∀ Q : simpleCharacterPairsAt ψF L n m,
          CharacterPair.AreConjugateBy (L.unitFiltration 0)
            (Q.1.restrict (L.unitFiltration (m + 2))) θ →
          unitConjCongr L m (κ P).1.b (κ Q).1.b →
          CharacterPair.AreConjugateBy (L.unitFiltration 0) P.1 Q.1

/-- An injective choice of strata on classes gives the cover. -/
theorem classCoverAt_of_injection (m : ℕ) (hinj : ClassInjectionAt ψF L n m)
    (htransport : ∀ (S T : SimpleStratumAt L n m) (u : G), u ∈ L.unitFiltration 0 →
      T.1.b - ((↑u⁻¹ : A) * S.1.b * (u : A)) ∈ L.endFiltration (-(m : ℤ)) →
      ∀ P ∈ simpleCharacterPairs ψF S.1 m, P.conj u ∈ simpleCharacterPairs ψF T.1 m)
    (hne : ∀ S : SimpleStratumAt L n m, (simpleCharacterPairs ψF S.1 m).Nonempty) :
    ClassCoverAt ψF L n m := by
  obtain ⟨κ, hκ₁, hκ₂⟩ := hinj
  have htr : ∀ S T : SimpleStratumAt L n m, unitConjCongr L m S.1.b T.1.b →
      ∀ P ∈ simpleCharacterPairs ψF S.1 m, ∃ P' ∈ simpleCharacterPairs ψF T.1 m,
        CharacterPair.AreConjugateBy (L.unitFiltration 0) P P' := by
    rintro S T ⟨u, hu, hST⟩ P hP
    exact ⟨P.conj u, htransport S T u hu hST P hP, ⟨⟨u, hu⟩, rfl⟩⟩
  have anchorSpec : ∀ R : SimpleStratumAt L n m, ∃ X : CharacterPair G,
      (∃ Y : SimpleStratumAt L n m, unitConjCongr L m Y.1.b R.1.b ∧
        X ∈ simpleCharacterPairs ψF Y.1 m) ∧
      ∀ P : simpleCharacterPairsAt ψF L n m, unitConjCongr L m (κ P).1.b R.1.b →
        CharacterPair.AreConjugateBy (L.unitFiltration 0) X P.1 := by
    intro R
    by_cases h : ∃ P : simpleCharacterPairsAt ψF L n m, unitConjCongr L m (κ P).1.b R.1.b
    · obtain ⟨P₀, hP₀⟩ := h
      obtain ⟨X, hX, hPX⟩ := hκ₁ P₀
      refine ⟨X, ⟨κ P₀, hP₀, hX⟩, fun P hP => ?_⟩
      exact hPX.symm.trans (hκ₂ P₀ P (hP₀.trans hP.symm))
    · obtain ⟨X, hX⟩ := hne R
      exact ⟨X, ⟨R, unitConjCongr.refl _ _ _, hX⟩, fun P hP => (h ⟨P, hP⟩).elim⟩
  choose anchor hanchorY hanchorP using anchorSpec
  have reprSpec : ∃ repr : SimpleStratumAt L n m → SimpleStratumAt L n m,
      (∀ S, unitConjCongr L m (repr S).1.b S.1.b) ∧
      ∀ S T, unitConjCongr L m S.1.b T.1.b → repr S = repr T :=
    exists_classRepresentative
      ⟨fun S T : SimpleStratumAt L n m => unitConjCongr L m S.1.b T.1.b,
        ⟨fun S => unitConjCongr.refl _ _ _, fun h => h.symm, fun h h' => h.trans h'⟩⟩
  obtain ⟨repr, hrepr, hreprEq⟩ := reprSpec
  have phiSpec : ∀ S : SimpleStratumAt L n m, ∃ X ∈ simpleCharacterPairs ψF S.1 m,
      CharacterPair.AreConjugateBy (L.unitFiltration 0) X (anchor (repr S)) := by
    intro S
    obtain ⟨Y, hY, hXY⟩ := hanchorY (repr S)
    obtain ⟨X, hX, hc⟩ := htr Y S (hY.trans (hrepr S)) _ hXY
    exact ⟨X, hX, hc.symm⟩
  choose Φ hΦ hΦa using phiSpec
  refine ⟨Φ, hΦ, ?_, ?_⟩
  · intro S T u x hST
    have hrel : unitConjCongr L m S.1.b T.1.b := ⟨u, u.2, hST⟩
    have h₁ := hΦa S
    rw [hreprEq S T hrel] at h₁
    exact h₁.trans (hΦa T).symm
  · intro P hP
    refine ⟨κ ⟨P, hP⟩, ?_⟩
    exact (hΦa _).trans (hanchorP _ ⟨P, hP⟩ (hrepr _).symm)

/-- **BK93 (3.2.4).** For `ψ_F` trivial on `𝔭_F` and nontrivial on `𝔬_F` and `⌊n/2⌋ ≤ m`,
every choice of a simple stratum `[𝔄,n,m,β]` with `P ∈ Ĉ(𝔄,m,β)` for each pair `P` of
`S^m_n(𝔄)` is injective on classes. -/
theorem classInjectionAt_of_half_le (hψ : IsBKAdditiveCharacter ψF) (m : ℕ)
    (hm : n / 2 ≤ (m : ℤ)) : ClassInjectionAt ψF L n m := by
  have hmem : ∀ P : simpleCharacterPairsAt ψF L n m,
      ∃ S : SimpleStratumAt L n m, P.1 ∈ simpleCharacterPairs ψF S.1 m :=
    fun P => Set.mem_iUnion.mp P.2
  choose κ hκ using hmem
  refine ⟨κ, fun P => ⟨P.1, hκ P, CharacterPair.AreConjugateBy.refl _ _⟩, ?_⟩
  have key : ∀ (S : SimpleStratumAt L n m), ∀ X ∈ simpleCharacterPairs ψF S.1 m,
      X.1 = L.unitFiltration (m + 1) ∧ ∀ (g : G) (hg : g ∈ X.1),
        (X.2 ⟨g, hg⟩ : ℂ) = elementCharacter (traceCharacter ψF) S.1.b g := by
    intro S X hX
    simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image] at hX
    obtain ⟨q, θ, hθ, rfl⟩ := hX
    obtain ⟨hS, hn, -, -⟩ := S.2
    have h := simpleCharacterHighIndex F V ψF hψ S.1 q m (by rw [hn]; exact hm)
    exact ⟨h.1.trans (congrArg (fun M => LatticeChain.unitFiltration M (m + 1)) hS),
      fun g hg => h.2 θ hθ ⟨g, hg⟩⟩
  rintro P Q ⟨u, hu, hPQ⟩
  obtain ⟨hP₁, hP₂⟩ := key (κ P) P.1 (hκ P)
  obtain ⟨hQ₁, hQ₂⟩ := key (κ Q) Q.1 (hκ Q)
  refine ⟨⟨u, hu⟩, CharacterPair.ext_of_eq ?_ ?_⟩
  · ext y
    rw [CharacterPair.mem_conj_fst, hP₁, hQ₁]
    exact L.conj_mem_unitFiltration_iff hu (m + 1) y
  · intro g hg₁ hg₂
    have hg' : u * g * u⁻¹ ∈ P.1.1 := CharacterPair.mem_conj_fst.mp hg₁
    rw [CharacterPair.conj_snd_apply _ _ _ hg₁ hg']
    apply Units.ext
    have hgU : g ∈ L.unitFiltration (m + 1) := hQ₁ ▸ hg₂
    have htriv := elementCharacter_eq_one_of_depth L ψF hψ hPQ (k := m + 1)
      (by push_cast; omega) hgU
    rw [hP₂ _ hg', hQ₂ _ hg₂]
    change elementCharacter (traceCharacter ψF) (κ P).1.b (u * g * u⁻¹) = _
    rw [elementCharacter_conj]
    calc elementCharacter (traceCharacter ψF) ((↑u⁻¹ : A) * (κ P).1.b * (u : A)) g
        = elementCharacter (traceCharacter ψF) ((↑u⁻¹ : A) * (κ P).1.b * (u : A)) g *
            elementCharacter (traceCharacter ψF)
              ((κ Q).1.b - (↑u⁻¹ : A) * (κ P).1.b * (u : A)) g := by
          rw [htriv, mul_one]
      _ = elementCharacter (traceCharacter ψF) (κ Q).1.b g := by
          rw [← elementCharacter_add]
          congr 1
          abel

/-- The induction step from depth `m + 1` to depth `m`. -/
theorem classInjectionAt_step (m : ℕ) (h₁ : ClassInjectionAt ψF L n (m + 1))
    (hres : PairRestrictionAt ψF L n m) (hfib : FibreInjectionAt ψF L n m) :
    ClassInjectionAt ψF L n m := by
  obtain ⟨κ₁, hκ₁a, hκ₁b⟩ := h₁
  have hnorm : ∃ κ : simpleCharacterPairsAt ψF L n (m + 1) →
        SimpleStratumAt L n ((m + 1 : ℕ) : ℤ),
      (∀ P, ∃ P' ∈ simpleCharacterPairs ψF (κ P).1 (m + 1),
        CharacterPair.AreConjugateBy (L.unitFiltration 0) P.1 P') ∧
      (∀ P Q, unitConjCongr L ((m + 1 : ℕ) : ℤ) (κ P).1.b (κ Q).1.b →
        CharacterPair.AreConjugateBy (L.unitFiltration 0) P.1 Q.1) ∧
      (∀ P Q, CharacterPair.AreConjugateBy (L.unitFiltration 0) P.1 Q.1 → κ P = κ Q) := by
    obtain ⟨rep, hrep, hrepEq⟩ := exists_classRepresentative
      ⟨fun P Q : simpleCharacterPairsAt ψF L n (m + 1) =>
          CharacterPair.AreConjugateBy (L.unitFiltration 0) P.1 Q.1,
        ⟨fun P => CharacterPair.AreConjugateBy.refl _ _, fun h => h.symm,
          fun h h' => h.trans h'⟩⟩
    refine ⟨fun P => κ₁ (rep P), fun P => ?_, fun P Q h => ?_, fun P Q h => ?_⟩
    · obtain ⟨P', hP', hc⟩ := hκ₁a (rep P)
      exact ⟨P', hP', (hrep P).symm.trans hc⟩
    · exact ((hrep P).symm.trans (hκ₁b _ _ h)).trans (hrep Q)
    · simp only [hrepEq P Q h]
  obtain ⟨κ₁', ha, hb, hc⟩ := hnorm
  have thetaSpec : ∀ T : SimpleStratumAt L n ((m + 1 : ℕ) : ℤ), ∃ θ : CharacterPair G,
      (∃ P, κ₁' P = T) → θ ∈ simpleCharacterPairs ψF T.1 (m + 1) ∧
        ∀ P, κ₁' P = T → CharacterPair.AreConjugateBy (L.unitFiltration 0) P.1 θ := by
    intro T
    by_cases h : ∃ P, κ₁' P = T
    · obtain ⟨P, rfl⟩ := h
      obtain ⟨θ, hθ, hPθ⟩ := ha P
      refine ⟨θ, fun _ => ⟨hθ, fun Q hQ => ?_⟩⟩
      exact (hb Q P (by rw [hQ]; exact unitConjCongr.refl _ _ _)).trans hPθ
    · exact ⟨⟨⊥, 1⟩, fun h' => (h h').elim⟩
  choose θ hθ using thetaSpec
  have fibSpec : ∀ T : SimpleStratumAt L n ((m + 1 : ℕ) : ℤ),
      ∃ κT : simpleCharacterPairsAt ψF L n m → SimpleStratumAt L n m,
      (∃ P, κ₁' P = T) → ∀ P : simpleCharacterPairsAt ψF L n m,
        CharacterPair.AreConjugateBy (L.unitFiltration 0)
          (P.1.restrict (L.unitFiltration (m + 2))) (θ T) →
        (κT P).1.b - T.1.b ∈ L.endFiltration (-((m + 1 : ℕ) : ℤ)) ∧
        (∃ P' ∈ simpleCharacterPairs ψF (κT P).1 m,
          CharacterPair.AreConjugateBy (L.unitFiltration 0) P.1 P') ∧
        ∀ Q : simpleCharacterPairsAt ψF L n m,
          CharacterPair.AreConjugateBy (L.unitFiltration 0)
            (Q.1.restrict (L.unitFiltration (m + 2))) (θ T) →
          unitConjCongr L m (κT P).1.b (κT Q).1.b →
          CharacterPair.AreConjugateBy (L.unitFiltration 0) P.1 Q.1 := by
    intro T
    by_cases h : ∃ P, κ₁' P = T
    · obtain ⟨κT, hκT⟩ := hfib T (θ T) (hθ T h).1
      exact ⟨κT, fun _ => hκT⟩
    · exact ⟨fun P => Classical.choose (Set.mem_iUnion.mp P.2), fun h' => (h h').elim⟩
  choose κT hκT using fibSpec
  have hR : ∀ P : simpleCharacterPairsAt ψF L n m,
      P.1.restrict (L.unitFiltration (m + 2)) ∈ simpleCharacterPairsAt ψF L n (m + 1) :=
    fun P => hres P.1 P.2
  have hRθ : ∀ P : simpleCharacterPairsAt ψF L n m,
      CharacterPair.AreConjugateBy (L.unitFiltration 0)
        (P.1.restrict (L.unitFiltration (m + 2))) (θ (κ₁' ⟨_, hR P⟩)) :=
    fun P => (hθ (κ₁' ⟨_, hR P⟩) ⟨⟨_, hR P⟩, rfl⟩).2 ⟨_, hR P⟩ rfl
  refine ⟨fun P => κT (κ₁' ⟨_, hR P⟩) P, fun P => ?_, fun P Q hPQ => ?_⟩
  · exact (hκT _ ⟨⟨_, hR P⟩, rfl⟩ P (hRθ P)).2.1
  · have hP := hκT _ ⟨⟨_, hR P⟩, rfl⟩ P (hRθ P)
    have hQ := hκT _ ⟨⟨_, hR Q⟩, rfl⟩ Q (hRθ Q)
    have hT : unitConjCongr L ((m + 1 : ℕ) : ℤ) (κ₁' ⟨_, hR P⟩).1.b (κ₁' ⟨_, hR Q⟩).1.b := by
      obtain ⟨u, hu, huPQ⟩ := hPQ
      refine ⟨u, hu, ?_⟩
      have h₁ := L.conj_mem_endFiltration hu hP.1
      have h₂ : (κT (κ₁' ⟨_, hR Q⟩) Q).1.b - (↑u⁻¹ : A) * (κT (κ₁' ⟨_, hR P⟩) P).1.b * (u : A) ∈
          L.endFiltration (-((m + 1 : ℕ) : ℤ)) :=
        L.endFiltration_antitone (by push_cast; omega) huPQ
      have heq : (κ₁' ⟨_, hR Q⟩).1.b - (↑u⁻¹ : A) * (κ₁' ⟨_, hR P⟩).1.b * (u : A) =
          -((κT (κ₁' ⟨_, hR Q⟩) Q).1.b - (κ₁' ⟨_, hR Q⟩).1.b) +
            ((κT (κ₁' ⟨_, hR Q⟩) Q).1.b -
              (↑u⁻¹ : A) * (κT (κ₁' ⟨_, hR P⟩) P).1.b * (u : A)) +
            (↑u⁻¹ : A) * ((κT (κ₁' ⟨_, hR P⟩) P).1.b - (κ₁' ⟨_, hR P⟩).1.b) * (u : A) := by
        simp only [mul_sub, sub_mul]
        abel
      rw [heq]
      exact add_mem (add_mem (neg_mem hQ.1) h₂) h₁
    have hTeq : κ₁' ⟨_, hR P⟩ = κ₁' ⟨_, hR Q⟩ := hc _ _ (hb _ _ hT)
    have hQ' := hRθ Q
    beta_reduce at hPQ
    rw [← hTeq] at hQ' hPQ
    exact hP.2.2 Q hQ' hPQ

/-- Downward induction on the depth. -/
theorem classInjectionAt_of_premises (hψ : IsBKAdditiveCharacter ψF)
    (hres : ∀ k : ℕ, (k : ℤ) + 1 < n → PairRestrictionAt ψF L n k)
    (hfib : ∀ k : ℕ, (k : ℤ) + 1 < n → FibreInjectionAt ψF L n k) :
    ∀ m : ℕ, (m : ℤ) < n → ClassInjectionAt ψF L n m := by
  suffices h : ∀ d : ℕ, ∀ m : ℕ, (m : ℤ) + 1 + d = n → ClassInjectionAt ψF L n m by
    intro m hm
    exact h (n - 1 - m).toNat m (by omega)
  intro d
  induction d with
  | zero =>
    intro m hm
    exact classInjectionAt_of_half_le ψF L n hψ m (by omega)
  | succ d ih =>
    intro m hm
    by_cases hhalf : n / 2 ≤ (m : ℤ)
    · exact classInjectionAt_of_half_le ψF L n hψ m hhalf
    · exact classInjectionAt_step ψF L n m (ih (m + 1) (by push_cast; omega))
        (hres m (by omega)) (hfib m (by omega))

/-- The cover at depth `m` from transport, nonemptiness, restriction and the fibres. -/
theorem classCoverAt_of_premises (hψ : IsBKAdditiveCharacter ψF) (m : ℕ) (hm : (m : ℤ) < n)
    (htransport : ∀ (S T : SimpleStratumAt L n m) (u : G), u ∈ L.unitFiltration 0 →
      T.1.b - ((↑u⁻¹ : A) * S.1.b * (u : A)) ∈ L.endFiltration (-(m : ℤ)) →
      ∀ P ∈ simpleCharacterPairs ψF S.1 m, P.conj u ∈ simpleCharacterPairs ψF T.1 m)
    (hne : ∀ S : SimpleStratumAt L n m, (simpleCharacterPairs ψF S.1 m).Nonempty)
    (hres : ∀ k : ℕ, (k : ℤ) + 1 < n → PairRestrictionAt ψF L n k)
    (hfib : ∀ k : ℕ, (k : ℤ) + 1 < n → FibreInjectionAt ψF L n k) :
    ClassCoverAt ψF L n m :=
  classCoverAt_of_injection ψF L n m
    (classInjectionAt_of_premises ψF L n hψ hres hfib m hm) htransport hne

end Skeleton

end Langlands.BushnellKutzko
