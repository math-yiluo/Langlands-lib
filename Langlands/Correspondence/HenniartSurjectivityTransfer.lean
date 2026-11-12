import Langlands.Correspondence.HenniartRankExtension
import Langlands.Correspondence.HenniartFiniteTwist
import Langlands.Correspondence.HenniartChoiceIndependenceStepProof

/-!
# Surjectivity of the stable images from surjectivity of the extension

Henniart (2000), §4.3, last sentence, in rank `n`. Suppose the extension of the
stable images of rank `n` by unramified twists is surjective. Let `π` be a
unitary supercuspidal class of rank `n` with central character of finite order.
Then `π = z · π₀`, where `π₀` is the stable image of a finite-image unitary
class `b₀`. The central character of `π₀` is the determinant of `b₀` through
reciprocity, of finite order, and `π` has central character `z^(ord) ω_(π₀)`,
so `z` is a root of unity. The twist `z · b₀` is then a finite-image class, and
a candidate for both classes sends it to `z · π₀ = π`. So `π` is a stable image.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap

universe uK uW uV uE

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartSurjectivityTransferFieldTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

local instance henniartSurjectivityTransferGLTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n K.Carrier) :=
  K.canonicalGeneralLinearTopology n

/-- The scalar by which `a` acts on a supercuspidal class is unique. -/
theorem supercuspidalCentralActsBy_unique {n : ℕ+}
    {π : SupercuspidalAutomorphicClass.{uK, uV} K n} {a : K.Carrierˣ} {c c' : ℂˣ}
    (h : SupercuspidalCentralActsBy K π a c) (h' : SupercuspidalCentralActsBy K π a c') :
    c = c' := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep π
  have hA := (supercuspidalCentralActsBy_iff K A a c).mp h
  have hA' := (supercuspidalCentralActsBy_iff K A a c').mp h'
  obtain ⟨v, hv⟩ := AssemblyDeterminant.exists_ne_zero_of_isIrreducible A.property.1
  exact Units.ext (smul_left_injective ℂ hv ((hA v).symm.trans (hA' v)))

/-- If `π = z · π₀`, where `π₀` is the stable image of `b₀` and `π` has central
character of finite order, then `z` is a root of unity. -/
theorem exists_pow_eq_one_of_stableTwist
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e)
    {b₀ : LocalWeil.UnitaryBasis.{uK, uW} K} {π₀ π : PadicSupercuspidal.UnitaryBasis.{uK, uV} K}
    {z : ℂˣ} (hst : IsStableImage.{uK, uW, uV, uE} K b₀ (generator π₀))
    (hπ : π.val = PadicSupercuspidal.unramifiedTwistBasisEquiv K z π₀.val)
    (hfin : HasFiniteOrderCentralCharacter K π) : ∃ N : ℕ, 0 < N ∧ z ^ N = 1 := by
  obtain ⟨Q, _, _, q, hσ, ⟨W, A, Φ, hΦ⟩, hall⟩ := hst
  have hΦx := hall W A Φ hΦ ⟨generator b₀, hΦ.1 hσ⟩ rfl
  obtain ⟨ω₀, hω₀, hω₀det⟩ := hΦ.2.2.1 e he ⟨generator b₀, hΦ.1 hσ⟩
  rw [hΦx, PadicSupercuspidal.isUnitaryCentralCharacter_generator_iff] at hω₀
  rw [LocalWeil.unitaryDeterminant_generator] at hω₀det
  obtain ⟨ω, hω, hωfin⟩ := hfin
  obtain ⟨N₁, hN₁, hωN⟩ := isOfFinOrder_iff_pow_eq_one.mp hωfin
  set T := K.canonicalTopologicalData
  obtain ⟨w₀, hw₀⟩ := reciprocityHom_surjective' K e T.uniformizerUnit
  have hdet : ω₀ T.uniformizerUnit ^ Nat.card Q = 1 := by
    have h1 := hω₀det w₀
    change ω₀ (reciprocityHom K e w₀) = FiniteRepresentation.determinantCharacterClass
      (Weil.underlyingClass _ b₀.val) w₀ at h1
    rw [← hw₀, h1]
    exact determinant_pow_card_eq_one _ (factorsThrough_of_mem K hσ) w₀
  have hωϖ : ω T.uniformizerUnit ^ N₁ = 1 := by
    rw [← MonoidHom.pow_apply, hωN, MonoidHom.one_apply]
  obtain ⟨⟨m, π'⟩, hπ'⟩ := π₀
  obtain ⟨⟨m', πc⟩, hπc⟩ := π
  have hpair : (⟨m', πc⟩ : PadicSupercuspidal.Basis.{uK, uV} K) =
      ⟨m, supercuspidalTwist K (fieldUnramified K z) π'⟩ := hπ
  obtain ⟨rfl, hheq⟩ := Sigma.mk.inj hpair
  have hπeq := eq_of_heq hheq
  subst hπeq
  have h1 : SupercuspidalCentralActsBy K (supercuspidalTwist K (fieldUnramified K z) π')
      T.uniformizerUnit (ω T.uniformizerUnit) := hω T.uniformizerUnit
  have h2 := supercuspidalCentralActsBy_twist K (hω₀ T.uniformizerUnit) (fieldUnramified K z)
  have heq := supercuspidalCentralActsBy_unique K h1 h2
  have hz : fieldUnramified K z T.uniformizerUnit = z := T.unramifiedCharacter_uniformizer z
  rw [hz] at heq
  have hzm : z ^ (m' : ℕ) = ω T.uniformizerUnit * (ω₀ T.uniformizerUnit)⁻¹ := by
    rw [heq, mul_inv_cancel_right]
  refine ⟨(m' : ℕ) * (N₁ * Nat.card Q),
    Nat.mul_pos m'.pos (Nat.mul_pos hN₁ Nat.card_pos), ?_⟩
  rw [pow_mul, hzm, mul_pow, inv_pow, pow_mul, hωϖ, one_pow, one_mul, mul_comm N₁,
    pow_mul, hdet, one_pow, inv_one]

/-- If the extension of the stable images of rank `n` is surjective, every unitary
supercuspidal class of rank `n` with central character of finite order is a
stable image. -/
theorem stableSurjectiveAt_of_surjective {n : ℕ+}
    (hS : StableExistsAt.{uK, uW, uV, uE} K n)
    (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e)
    (hsurj : Function.Surjective (rankExtension K hS)) :
    StableSurjectiveAt.{uK, uW, uV, uE} K n := by
  intro π hπn hfin
  obtain ⟨σ, hσ⟩ := hsurj (rankCast K π.val hπn)
  have hbasis : rankExtensionBasis K hS σ = π.val := by
    rw [← sigma_rankExtension K hS σ, hσ, sigma_rankCast]
  obtain ⟨z, π₀, b₀, h, he₁⟩ := rankExtensionBasis_spec K hS σ
  have hπ : π.val = PadicSupercuspidal.unramifiedTwistBasisEquiv K z π₀.val :=
    hbasis.symm.trans he₁
  obtain ⟨N, hN, hzN⟩ := exists_pow_eq_one_of_stableTwist K he h.2 hπ hfin
  have hw : ‖(z : ℂ)‖ = 1 := norm_eq_one_of_unramifiedTwist_unitary K π₀ π hπ
  let b₁ := weilUnitaryTwist K e (fieldUnramified K z) (norm_fieldUnramified K hw) b₀
  have hb₁val : b₁.val =
      Weil.twistBasisEquiv (Weil.Local.localUnramifiedCharacter K z) b₀.val :=
    (unitaryFieldCharacterTwist_fieldUnramified_val K he hw b₀).2
  have hb₀fin : IsFiniteFactoring K b₀ := by
    obtain ⟨Q, hQ, hQf, q, hq, -, -⟩ := h.2
    exact ⟨Q, hQ, hQf, q, hq⟩
  have hχN : ∀ g, Weil.Local.localUnramifiedCharacter K z g ^ N = 1 := by
    intro g
    change (z ^ (Weil.Local.localDegree K g).toAdd) ^ N = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzN, one_zpow]
  have hb₁fin : IsFiniteFactoring K b₁ :=
    isFiniteFactoring_twist K hb₀fin _ hN hχN hb₁val
  have hb₁rank : b₁.val.1 = n := by
    rw [hb₁val]
    exact congrArg Sigma.fst h.1
  obtain ⟨y, hy⟩ := hS b₁ hb₁rank hb₁fin
  obtain ⟨W, A, Φ, hΦ, ⟨x, hx, hΦx⟩, ⟨x', hx', hΦx'⟩⟩ := exists_common_candidate₂ K hCE h.2 hy
  obtain ⟨x'', hx'', hΦx''⟩ := candidate_twist_generator K hΦ he (fieldUnramified K z)
    (norm_fieldUnramified K hw) x hx hΦx
  have hxx : x'' = x' := Subtype.ext (hx''.trans hx'.symm)
  rw [hxx, hΦx'] at hΦx''
  have hsc : supercuspidalUnitaryTwist K (fieldUnramified K z) (norm_fieldUnramified K hw) π₀ =
      π := Subtype.ext hπ.symm
  rw [hsc] at hΦx''
  exact ⟨b₁, hb₁rank, hΦx'' ▸ hy⟩

end Langlands.Henniart.Extension
