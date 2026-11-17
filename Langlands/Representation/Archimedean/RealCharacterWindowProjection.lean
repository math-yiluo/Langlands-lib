import Langlands.Representation.Archimedean.RealAdjacentWindowSpanning
import Langlands.Representation.Archimedean.RealCharacterPairReducible
import Langlands.Representation.Archimedean.RealStandardFiltration

/-! # Concrete low and high window projections on real character lists -/

noncomputable section

open scoped ComplexConjugate InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealCharacterWindowProjection

open RealBlockFrobeniusMap RealBlockMultiplier RealBlockJacquet
open RealCharacterPair RealCharacterPairReducible RealStandardFiltration
open RealAdjacentWindowSpanning PrincipalSeriesAnnihilator
open RealStrictCharacterLanglandsQuotient

section Pair

variable {n : ℕ} {pre post : List RealBlock} {c d : RealCharacterData} {ℓ : ℕ}
  (hn : realRank (pre ++ .character c :: .character d :: post) = n)

/-- The binomial map after its pointwise inverse, as an endomorphism of the original list. -/
def low : KF n (pre ++ .character c :: .character d :: post) →ₗ[ℂ]
    KF n (pre ++ .character c :: .character d :: post) :=
  (blockFrobMap (data_q0 (ℓ := ℓ) hn)).comp (blockFrobMap (data_B (ℓ := ℓ) hn))

/-- The complementary endomorphism. -/
def high : KF n (pre ++ .character c :: .character d :: post) →ₗ[ℂ]
    KF n (pre ++ .character c :: .character d :: post) :=
  LinearMap.id - low (ℓ := ℓ) hn

theorem low_fourier (hℓ : 0 < ℓ) (hpar : Even ((ℓ : ℤ) - 1 - pairParity c d))
    (f : KF n (pre ++ .character c :: .character d :: post))
    (j : ℤ) {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    blockFourierCoefficient n (realRank pre) j (low (ℓ := ℓ) hn f) k =
      lowMultiplier ℓ j * blockFourierCoefficient n (realRank pre) j f k := by
  change blockFourierCoefficient n (realRank pre) j
    (blockFrobMap (data_q0 (ℓ := ℓ) hn) (blockFrobMap (data_B (ℓ := ℓ) hn) f)) k = _
  rw [blockFourierCoefficient_blockFrobMap, blockFourierCoefficient_blockFrobMap]
  by_cases hj : Even (j - pairParity c d)
  · by_cases hlt : |j| < (ℓ : ℤ)
    · have hb := (binomialMultiplier_ne_zero_iff hℓ (pairParity_eq c d) hpar hj).mpr hlt
      rw [← mul_assoc, mul_inv_cancel₀ hb]
      simp [lowMultiplier, hlt]
    · have hb : binomialMultiplier ℓ (pairParity c d) j = 0 := by
        by_contra hb
        exact hlt ((binomialMultiplier_ne_zero_iff hℓ (pairParity_eq c d) hpar hj).mp hb)
      simp [hb, lowMultiplier, hlt]
  · rw [blockFourierCoefficient_eq_zero_of_not_even
      (data_B (ℓ := ℓ) hn).lt (data_B (ℓ := ℓ) hn).par f hj]
    simp
  all_goals exact hk

theorem fourier_sub {p : ℕ} (f g : KF n (pre ++ .character c :: .character d :: post))
    (j : ℤ) (k : Langlands.GeneralLinear n ℝ) :
    blockFourierCoefficient n p j (f - g) k =
      blockFourierCoefficient n p j f k - blockFourierCoefficient n p j g k := by
  have hfg : (f : Langlands.GeneralLinear n ℝ → ℂ) - g = f + (-1 : ℂ) • g := by
    ext x
    simp [sub_eq_add_neg]
  rw [hfg, blockFourierCoefficient_add p j (continuous_coe f)
    ((continuous_coe g).const_smul (-1 : ℂ)), blockFourierCoefficient_smul]
  ring

theorem high_fourier (hℓ : 0 < ℓ) (hpar : Even ((ℓ : ℤ) - 1 - pairParity c d))
    (f : KF n (pre ++ .character c :: .character d :: post))
    (j : ℤ) {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    blockFourierCoefficient n (realRank pre) j (high (ℓ := ℓ) hn f) k =
      highMultiplier ℓ j * blockFourierCoefficient n (realRank pre) j f k := by
  change blockFourierCoefficient n (realRank pre) j (f - low (ℓ := ℓ) hn f) k = _
  rw [fourier_sub, low_fourier hn hℓ hpar f j hk, highMultiplier]
  ring

theorem low_compact (k : Matrix.unitaryGroup (Fin n) ℝ)
    (f : KF n (pre ++ .character c :: .character d :: post)) :
    low (ℓ := ℓ) hn (realStandardRep n _ k f) =
      realStandardRep n _ k (low (ℓ := ℓ) hn f) := by
  change blockFrobMap (data_q0 (ℓ := ℓ) hn)
    (blockFrobMap (data_B (ℓ := ℓ) hn) (realStandardRep n _ k f)) = _
  rw [blockFrobMap_rightTranslation, blockFrobMap_rightTranslation]
  rfl

theorem high_compact (k : Matrix.unitaryGroup (Fin n) ℝ)
    (f : KF n (pre ++ .character c :: .character d :: post)) :
    high (ℓ := ℓ) hn (realStandardRep n _ k f) =
      realStandardRep n _ k (high (ℓ := ℓ) hn f) := by
  change realStandardRep n _ k f - low (ℓ := ℓ) hn (realStandardRep n _ k f) =
    realStandardRep n _ k (f - low (ℓ := ℓ) hn f)
  rw [low_compact, map_sub]

end Pair

section CharacterList

variable {n : ℕ} {ds : List RealBlock} (hds : IsCharacterList ds)

/-- Identity on functions identifies an all-character standard module with its principal series. -/
def principalEquiv : KF n ds ≃ₗ[ℂ] KFin n (realPositionCharacter ds) :=
  LinearEquiv.ofEq _ _ (congrArg
    (fun M => kFiniteFunctions M (unitaryCompact ℝ n)) (realStandardModule_eq hds))

@[simp] theorem principalEquiv_toFun (f : KF n ds) :
    (principalEquiv hds f).toFun = f := rfl

@[simp] theorem principalEquiv_symm_coe (x : KFin n (realPositionCharacter ds)) :
    ((principalEquiv hds).symm x : Langlands.GeneralLinear n ℝ → ℂ) = x.toFun := rfl

/-- Transport of an endomorphism to the principal-series compact model. -/
def transport (T : KF n ds →ₗ[ℂ] KF n ds) :
    KFin n (realPositionCharacter ds) →ₗ[ℂ] KFin n (realPositionCharacter ds) :=
  (principalEquiv hds).toLinearMap.comp (T.comp (principalEquiv hds).symm.toLinearMap)

theorem transport_compact (T : KF n ds →ₗ[ℂ] KF n ds)
    (hT : ∀ k x, T (realStandardRep n ds k x) = realStandardRep n ds k (T x))
    (k : unitaryCompact ℝ n) (x : KFin n (realPositionCharacter ds)) :
    transport hds T (rho k x) = rho k (transport hds T x) := by
  let κ : Matrix.unitaryGroup (Fin n) ℝ :=
    ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩
  have hk : Unitary.toUnits κ = (k : Langlands.GeneralLinear n ℝ) := Units.ext rfl
  have he : ∀ f : KF n ds, principalEquiv hds (realStandardRep n ds κ f) =
      rho k (principalEquiv hds f) := by
    intro f
    apply KFin.ext
    change Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
      (Unitary.toUnits κ) f = Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k f
    rw [hk]
  have he' : (principalEquiv hds).symm (rho k x) =
      realStandardRep n ds κ ((principalEquiv hds).symm x) := by
    apply (principalEquiv hds).injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
  change principalEquiv hds (T ((principalEquiv hds).symm (rho k x))) =
    rho k (principalEquiv hds (T ((principalEquiv hds).symm x)))
  rw [he', hT, he]

include hds in
/-- The principal-series spanning theorem on an actual all-character standard module. -/
theorem range_sup_eq_top (p m h : ℕ) (hp : p + 3 ≤ n) (hhm : h < m)
    (P Q : KF n ds →ₗ[ℂ] KF n ds)
    (hPK : ∀ k x, P (realStandardRep n ds k x) = realStandardRep n ds k (P x))
    (hQK : ∀ k x, Q (realStandardRep n ds k x) = realStandardRep n ds k (Q x))
    (hP : ∀ x j k, k ∈ unitaryCompact ℝ n →
      blockFourierCoefficient n p j (P x) k =
        lowMultiplier m j * blockFourierCoefficient n p j x k)
    (hQ : ∀ x j k, k ∈ unitaryCompact ℝ n →
      blockFourierCoefficient n (p + 1) j (Q x) k =
        highMultiplier h j * blockFourierCoefficient n (p + 1) j x k) :
    LinearMap.range P ⊔ LinearMap.range Q = ⊤ := by
  have hspan := range_low_sup_range_high p hp m h hhm
    (transport hds P) (transport hds Q)
    (transport_compact hds P hPK) (transport_compact hds Q hQK)
    (fun x j k hk => hP ((principalEquiv hds).symm x) j k hk)
    (fun x j k hk => hQ ((principalEquiv hds).symm x) j k hk)
  apply eq_top_iff.mpr
  intro x _
  have hx : principalEquiv hds x ∈
      LinearMap.range (transport hds P) ⊔ LinearMap.range (transport hds Q) := by
    rw [hspan]
    trivial
  obtain ⟨_, ⟨u, rfl⟩, _, ⟨v, rfl⟩, huv⟩ := Submodule.mem_sup.mp hx
  refine Submodule.mem_sup.mpr
    ⟨P ((principalEquiv hds).symm u), ⟨_, rfl⟩,
      Q ((principalEquiv hds).symm v), ⟨_, rfl⟩, ?_⟩
  apply (principalEquiv hds).injective
  rw [map_add]
  exact huv

end CharacterList

section Four

variable (a b c d : RealCharacterData)

abbrev four : List RealBlock := [.character a, .character b, .character c, .character d]

def lowLeft (m : ℕ) : KF 4 (four a b c d) →ₗ[ℂ] KF 4 (four a b c d) :=
  low (ℓ := m) (pre := []) (post := [.character c, .character d]) rfl

def highMiddle (h : ℕ) : KF 4 (four a b c d) →ₗ[ℂ] KF 4 (four a b c d) :=
  high (ℓ := h) (pre := [.character a]) (post := [.character d]) rfl

theorem four_spanning (m h : ℕ) (hm : 0 < m) (hh : 0 < h) (hhm : h < m)
    (hpar0 : Even ((m : ℤ) - 1 - pairParity a b))
    (hpar1 : Even ((h : ℤ) - 1 - pairParity b c)) :
    LinearMap.range (lowLeft a b c d m) ⊔
      LinearMap.range (highMiddle a b c d h) = ⊤ := by
  have hchars : IsCharacterList (four a b c d) := by
    intro e he
    simp only [four, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  apply range_sup_eq_top hchars 0 m h (by norm_num) hhm
  · exact low_compact (ℓ := m) (pre := [])
      (post := [.character c, .character d]) (c := a) (d := b) rfl
  · exact high_compact (ℓ := h) (pre := [.character a])
      (post := [.character d]) (c := b) (d := c) rfl
  · intro x j k hk
    exact low_fourier (pre := []) (post := [.character c, .character d])
      rfl hm hpar0 x j hk
  · intro x j k hk
    exact high_fourier (pre := [.character a]) (post := [.character d])
      rfl hh hpar1 x j hk

end Four
end RealCharacterWindowProjection

/-- Concrete binomial low and complementary middle-high Frobenius projections span the
actual four-character standard module when their positive cutoffs strictly decrease. -/
def RealCharacterWindowProjectionStatement : Prop :=
  ∀ (a b c d : RealCharacterData) (m h : ℕ),
    0 < m → 0 < h → h < m →
    Even ((m : ℤ) - 1 - RealCharacterPair.pairParity a b) →
    Even ((h : ℤ) - 1 - RealCharacterPair.pairParity b c) →
    LinearMap.range (RealCharacterWindowProjection.lowLeft a b c d m) ⊔
      LinearMap.range (RealCharacterWindowProjection.highMiddle a b c d h) = ⊤

theorem realCharacterWindowProjection : RealCharacterWindowProjectionStatement :=
  RealCharacterWindowProjection.four_spanning

end Langlands.Archimedean
