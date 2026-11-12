import Langlands.Correspondence.HenniartTwistIndependenceProof
import Langlands.Weil.Local.GaloisCorrectionProof
import Langlands.Correspondence.RankOneDeterminantCompatibility

/-!
# The rank-one stage of Henniart's induction

Henniart (2000), §4.3, base case. A unitary rank-one Weil class is the pullback
`χ ∘ rec` of a field character `χ` of modulus one. The character clause of every
candidate sends it to the `GL₁` class of `χ`, so its stable image is that class.
Conversely, a unitary rank-one supercuspidal class with central character of
finite order is the class of a character `χ` of finite order; `χ ∘ rec` has
finite image, hence factors through a finite quotient of the absolute Galois
group, and its stable image is the given class. Candidate existence and a
geometric reciprocity candidate are the only inputs.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap
open LocalFactor LocalFactor.CommonClosure

universe uK uW uV uE

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartRankOneStageFieldTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

/-- The inclusion of a unitary supercuspidal generator is the generator of its
underlying class. -/
theorem PadicSupercuspidal.includeUnitary_generator
    (π : PadicSupercuspidal.UnitaryBasis.{uK, uV} K) :
    PadicSupercuspidal.includeUnitary K (generator π) = generator π.val := by
  simp [PadicSupercuspidal.includeUnitary, Supercuspidal.includeUnitary, includeSubset,
    VirtualRepresentation.map, generator]

/-- The twist of the trivial rank-one class by `χ ∘ rec` is the rank-one class of `χ`. -/
theorem twist_trivialWeilBasis (e : ReciprocityCandidate K) (χ : QuasiCharacter K) :
    Weil.twistBasisEquiv (LocalFactor.RankOne.weilCharacter K e χ)
        (trivialWeilBasis.{uK, uW} K e) =
      ⟨1, rankOneWeilCharacterClass.{uK, uW} K e χ⟩ := by
  have h1 := IsRankOneWeilCharacter.twist K (rankOneWeilCharacterClass_spec.{uK, uW} K e 1)
    (LocalFactor.RankOne.weilCharacter K e χ)
  have hchar : (LocalFactor.RankOne.weilCharacter K e χ).toMonoidHom * weilCharacter K e 1 =
      weilCharacter K e χ := by
    ext g
    change ((LocalFactor.RankOne.weilCharacter K e χ g *
      (1 : QuasiCharacter K) (reciprocityHom K e g) : ℂˣ) : ℂ) =
        ((LocalFactor.RankOne.weilCharacter K e χ g : ℂˣ) : ℂ)
    change ((LocalFactor.RankOne.weilCharacter K e χ g * 1 : ℂˣ) : ℂ) = _
    rw [mul_one]
  rw [hchar] at h1
  exact congrArg (Sigma.mk 1)
    (IsRankOneWeilCharacter.class_unique K h1 (rankOneWeilCharacterClass_spec K e χ))

/-- If the rank-one class of `χ ∘ rec` is unitary, then `χ` has modulus one. -/
theorem norm_eq_one_of_rankOne_isUnitary {e : ReciprocityCandidate K} (χ : QuasiCharacter K)
    (h : Weil.IsUnitaryClass _
      (⟨1, rankOneWeilCharacterClass.{uK, uW} K e χ⟩ : LocalWeil.Basis.{uK, uW} K))
    (a : K.Carrierˣ) : ‖(χ a : ℂ)‖ = 1 := by
  obtain ⟨g, rfl⟩ := reciprocityHom_surjective' K e a
  rw [← twist_trivialWeilBasis K e χ] at h
  exact Weil.norm_eq_one_of_isUnitaryClass_twist (LocalFactor.RankOne.weilCharacter K e χ)
    (trivialWeilBasis_isUnitary K e) h g

/-- A candidate sends the rank-one class of a modulus-one character `χ` to the
`GL₁` class of `χ`. -/
theorem candidate_rankOne {W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K)}
    {A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)} {Φ : W ≃ₗ[ℤ] A}
    (hΦ : LatticeMap.HenniartProperties.{uK, uW, uV, uE} K Φ) {e : ReciprocityCandidate K}
    (he : IsGeometricReciprocity K e) (χ : QuasiCharacter K) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1)
    (σ : LocalWeil.UnitaryBasis.{uK, uW} K)
    (hσ : σ.val = ⟨1, rankOneWeilCharacterClass K e χ⟩) (x : W)
    (hx : (x : LocalWeil.UnitaryLattice.{uK, uW} K) = generator σ) :
    ∃ π : PadicSupercuspidal.UnitaryBasis.{uK, uV} K,
      π.val = ⟨1, rankOneSupercuspidalClass K χ⟩ ∧
        (Φ x : PadicSupercuspidal.UnitaryLattice.{uK, uV} K) = generator π := by
  obtain ⟨x', hx', hΦx'⟩ := (hΦ.1.2.2.2 e he χ hχ).2
  have hxx : x' = x := by
    apply Subtype.ext
    apply Weil.includeUnitary_injective (Weil.Local.localWeilGroup K)
    change LocalWeil.includeUnitary K x' = LocalWeil.includeUnitary K x
    rw [hx', hx, ← hσ]
    exact (Weil.includeUnitary_generator σ).symm
  subst hxx
  obtain ⟨π, hπ, -⟩ := IsCandidate.exists_generator K hΦ σ x' hx
  refine ⟨π, ?_, hπ⟩
  rw [hπ, PadicSupercuspidal.includeUnitary_generator] at hΦx'
  exact Finsupp.single_left_injective one_ne_zero hΦx'

/-- The stable image of the rank-one class of a modulus-one character `χ`,
when that class factors through a finite quotient, is the `GL₁` class of `χ`. -/
theorem isStableImage_rankOne (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e) (χ : QuasiCharacter K)
    (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) (σ : LocalWeil.UnitaryBasis.{uK, uW} K)
    (hσ : σ.val = ⟨1, rankOneWeilCharacterClass K e χ⟩) (hfin : IsFiniteFactoring K σ) :
    ∃ π : PadicSupercuspidal.UnitaryBasis.{uK, uV} K,
      π.val = ⟨1, rankOneSupercuspidalClass K χ⟩ ∧
        IsStableImage.{uK, uW, uV, uE} K σ (generator π) := by
  obtain ⟨Q, _, _, q, hq⟩ := hfin
  obtain ⟨W, A, Φ, hΦ⟩ := hCE p K Q q
  obtain ⟨π, hπ, -⟩ := candidate_rankOne K hΦ.2 he χ hχ σ hσ ⟨generator σ, hΦ.1 hq⟩ rfl
  refine ⟨π, hπ, Q, inferInstance, inferInstance, q, hq, ⟨W, A, Φ, hΦ⟩, ?_⟩
  intro W' A' Φ' hΦ' x hx
  obtain ⟨π', hπ', hΦx⟩ := candidate_rankOne K hΦ'.2 he χ hχ σ hσ x hx
  rw [hΦx, Subtype.ext (hπ'.trans hπ.symm)]

/-- The rank-one class of a character of finite order factors through a finite
quotient of the absolute Galois group. -/
theorem rankOne_isFiniteFactoring {e : ReciprocityCandidate K} (χ : QuasiCharacter K)
    {N : ℕ} (hN : 0 < N) (hχN : ∀ a, χ a ^ N = 1) (σ : LocalWeil.UnitaryBasis.{uK, uW} K)
    (hσ : σ.val = ⟨1, rankOneWeilCharacterClass K e χ⟩) : IsFiniteFactoring K σ := by
  let χW := LocalFactor.RankOne.weilCharacter K e χ
  let B : Weil.Local.LocalWeilRepresentation.{uK, uW} K :=
    FiniteRepresentation.characterLine χW.toMonoidHom
  have hc : B.IsContinuous := FiniteRepresentation.characterLine_isContinuous χW
  have hf : B.HasFiniteImage := by
    have : NeZero N := ⟨hN.ne'⟩
    have hS : ({ζ : ℂˣ | ζ ^ N = 1} : Set ℂˣ).Finite := by
      have hset : ({ζ : ℂˣ | ζ ^ N = 1} : Set ℂˣ) = ((rootsOfUnity N ℂ : Subgroup ℂˣ) : Set ℂˣ) := by
        ext ζ
        simp [mem_rootsOfUnity]
      rw [hset]
      exact Set.finite_coe_iff.mp (inferInstanceAs (Finite (rootsOfUnity N ℂ)))
    apply (hS.image (fun ζ : ℂˣ => (ζ : ℂ) • (LinearMap.id : Module.End ℂ (ULift.{uW} ℂ)))).subset
    rintro _ ⟨g, rfl⟩
    refine ⟨χW g, hχN (reciprocityHom K e g), ?_⟩
    ext v
    rfl
  have hG : Weil.Local.IsLocalGaloisType K B :=
    ((Weil.Local.localWeilGaloisTypeFor K B).1).mpr ⟨hc, hf⟩
  obtain ⟨Q, _, _, q, ρ, hρ⟩ := LocalWeil.exists_finiteQuotient_of_isLocalGaloisType K B hG
  refine ⟨Q, inferInstance, inferInstance, q, Finsupp.single_mem_supported ℤ _ ?_⟩
  refine ⟨FiniteRepresentation.of ρ, ?_⟩
  change FiniteRepresentation.classOf
      (FiniteRepresentation.of (ρ.comp (q.comp (Weil.Local.localProjection K).toMonoidHom))) = _
  rw [hρ, hσ]
  rfl

/-- The rank-one class of a modulus-one character is unitary. -/
theorem rankOneWeil_isUnitary (e : ReciprocityCandidate K) (χ : QuasiCharacter K)
    (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) :
    Weil.IsUnitaryClass _
      (⟨1, rankOneWeilCharacterClass.{uK, uW} K e χ⟩ : LocalWeil.Basis.{uK, uW} K) := by
  rw [← twist_trivialWeilBasis K e χ]
  exact (weilUnitaryTwist K e χ hχ (trivialWeilUnitary K e)).property

/-- The central character of the `GL₁` class of `χ` is `χ`. -/
theorem rankOneSupercuspidalClass_centralActsBy_unique {χ : QuasiCharacter K}
    {a : K.Carrierˣ} {c : ℂˣ}
    (h : SupercuspidalCentralActsBy K (rankOneSupercuspidalClass.{uK, uV} K χ) a c) :
    c = χ a := by
  have h₁ := (supercuspidalCentralActsBy_iff K (n := 1) (rankOneSupercuspidalObject K χ) a c).mp h
  have h₂ := (supercuspidalCentralActsBy_iff K (n := 1) (rankOneSupercuspidalObject K χ) a
    (χ a)).mp (IsRankOneCharacter.centralActsBy K (rankOneSupercuspidalClass_spec K χ) a)
  have hv := congrArg ULift.down ((h₁ (ULift.up 1)).symm.trans (h₂ (ULift.up 1)))
  change (c : ℂ) * 1 = (χ a : ℂ) * 1 at hv
  rw [mul_one, mul_one] at hv
  exact Units.ext hv

/-- Henniart's 4.2 (a) in rank one. -/
theorem stableExistsAt_one (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e) :
    StableExistsAt.{uK, uW, uV, uE} K 1 := by
  intro σ hσ1 hfin
  obtain ⟨⟨m, σ'⟩, hσu⟩ := σ
  change m = 1 at hσ1
  subst hσ1
  obtain ⟨χ, rfl⟩ := rankOneWeilCharacterClass_surjective K e σ'
  have hχ := norm_eq_one_of_rankOne_isUnitary K χ hσu
  obtain ⟨π, -, hst⟩ := isStableImage_rankOne K hCE he χ hχ _ rfl hfin
  exact ⟨_, hst⟩

/-- Henniart's 4.2 (b), surjectivity in rank one. -/
theorem stableSurjectiveAt_one (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e) :
    StableSurjectiveAt.{uK, uW, uV, uE} K 1 := by
  intro π hπ1 hfo
  obtain ⟨⟨m, π'⟩, hπu⟩ := π
  change m = 1 at hπ1
  subst hπ1
  obtain ⟨χ, rfl⟩ := rankOneSupercuspidalClass_surjective K π'
  obtain ⟨ω, hω, hωfin⟩ := hfo
  have hωχ : ∀ a, ω a = χ a := fun a => rankOneSupercuspidalClass_centralActsBy_unique K (hω a)
  obtain ⟨N, hN, hωN⟩ := isOfFinOrder_iff_pow_eq_one.mp hωfin
  have hχN : ∀ a, χ a ^ N = 1 := by
    intro a
    rw [← hωχ a, ← MonoidHom.pow_apply, hωN, MonoidHom.one_apply]
  have hχ : ∀ a, ‖(χ a : ℂ)‖ = 1 := fun a =>
    Complex.norm_eq_one_of_pow_eq_one
      (by rw [← Units.val_pow_eq_pow_val, hχN a, Units.val_one]) hN.ne'
  let σ : LocalWeil.UnitaryBasis.{uK, uW} K :=
    ⟨⟨1, rankOneWeilCharacterClass K e χ⟩, rankOneWeil_isUnitary K e χ hχ⟩
  obtain ⟨π₀, hπ₀, hst⟩ := isStableImage_rankOne.{uK, uW, uV, uE} K hCE he χ hχ σ rfl
    (rankOne_isFiniteFactoring K χ hN hχN σ rfl)
  refine ⟨σ, rfl, ?_⟩
  have hπeq : π₀ = ⟨⟨1, rankOneSupercuspidalClass K χ⟩, hπu⟩ := Subtype.ext hπ₀
  rw [← hπeq]
  exact hst

/-- Henniart (2000), §4.3, base case: candidate existence and normalized local
reciprocity give both assertions of the induction in rank one. -/
theorem rankOneStage_of_reciprocity (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    (hrec : LocalClassField.CommonClosureReciprocityExistence.{uK}) :
    RankOneStageStatement.{uK, uW, uV, uE} := by
  intro p _ K
  obtain ⟨eC, heC⟩ := hrec p K K.canonicalTopologicalData
  have he := baseGeometricReciprocityProof K eC heC
  exact ⟨stableExistsAt_one K hCE he, stableSurjectiveAt_one K hCE he⟩

end Langlands.Henniart.Extension
