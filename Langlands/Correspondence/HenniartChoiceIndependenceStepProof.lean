import Langlands.Correspondence.HenniartRankOneStageProof
import Langlands.Correspondence.HenniartUnitaryTwistProof
import Langlands.Correspondence.HenniartExtensionFactors
import Langlands.Correspondence.SupercuspidalFiniteEpsilonProof
import Langlands.Correspondence.SupercuspidalEpsilonComparison
import Langlands.Representation.RankinSelberg.SupercuspidalLocalConverseProof
import Langlands.Representation.RankinSelberg.UnramifiedTwistEpsilonProof
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof

/-!
# The inductive step of Henniart's rank induction: stable images in rank `n ≥ 2`

Henniart (2000), §4.3. Let `σ` be a unitary irreducible Weil class of dimension
`n = k + 2` factoring through a finite quotient `q₀`, and fix a candidate `Φ₀` at
`q₀`. For every candidate `Φ` whose domain contains `σ`, the central character of
`Φ σ` pulled back along reciprocity is `det σ`, and the epsilon factor of the pair
`(Φ σ, 1)` is the Weil epsilon factor of `σ`, which does not depend on `Φ`. So all
images lie in one set `P`, finite by the conductor finiteness input. The local
converse theorem gives finitely many lower-rank tests separating `P`. Each test is
an unramified twist of a unitary class with central character of finite order,
which by surjectivity in lower rank is the stable image of some `σ_t`. At a finite
quotient through which `σ`, `q₀` and the stable-image quotients of all `σ_t`
factor, any two candidates have the same epsilon factors against all tests, by the
uniqueness of Weil epsilon factors and the unramified-twist law, so they agree
on `σ`.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap
open LocalFactor LocalFactor.CommonClosure

universe uK uW uV uE

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartChoiceStepFieldTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

/-- Twisting the second member of a supercuspidal pair by the unramified character
with value `z` multiplies an epsilon certificate `(c, m)` by `z ^ m`. -/
theorem isSupercuspidalPairEpsilonFactor_unramifiedTwist_right
    (hGLε : RankinSelberg.UnramifiedTwistEpsilonStatement.{uK, uV, uV}) {r n : ℕ}
    (ψ : NontrivialAdditiveCharacter K) (ν : LocalAdditiveHaarMeasure K)
    (hν : IsSelfDualMeasure K ψ ν)
    {π : SupercuspidalAutomorphicClass.{uK, uV} K r.succPNat}
    {τ : SupercuspidalAutomorphicClass.{uK, uV} K n.succPNat} {c : ℂˣ} {m : ℤ}
    (h : IsSupercuspidalPairEpsilonFactor K ψ ν π τ (c, m)) (z : ℂˣ) :
    IsSupercuspidalPairEpsilonFactor K ψ ν π (supercuspidalTwist K (fieldUnramified K z) τ)
      (c * z ^ m, m) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep π
  obtain ⟨B, rfl⟩ := Quotient.exists_rep τ
  obtain ⟨u, hu, hχ⟩ := exists_unramifiedExponent K z
  let ν' : LocalFactor.PadicAbelian.SelfDualHaar K.canonicalTopologicalData ψ := ⟨ν, hν⟩
  obtain ⟨e₁, he₁m, he₁c, h1, -⟩ := hGLε p K ψ ν' r n A.obj.representation
    B.obj.representation u (fieldUnramified K z).toMonoidHom hχ (c, m) h
  have he : e₁ = (c * z ^ m, m) := by
    refine Prod.ext (Units.ext ?_) he₁m
    rw [he₁c]
    simp only
    rw [mul_comm (m : ℂ) u, ← neg_mul, Complex.cpow_mul_int, hu]
    push_cast
    ring
  rw [he] at h1
  exact h1

/-- At one local-constant system, the Weil epsilon certificate of a pair of
generators is unique. -/
theorem unitaryPairEpsilon_generator_unique {eC : ReciprocityFamily K}
    {ε : NonabelianSystem.Assignment.{uK, uE} K} {hε : NonabelianSystem.IsSystem K eC ε}
    {ψ : NontrivialAdditiveCharacter K} {a b : LocalWeil.UnitaryBasis.{uK, uW} K}
    {e e' : ℂˣ × ℤ}
    (h : LocalWeil.IsUnitaryPairEpsilonFactor K eC ε hε ψ (generator a) (generator b) e)
    (h' : LocalWeil.IsUnitaryPairEpsilonFactor K eC ε hε ψ (generator a) (generator b) e') :
    e = e' := by
  have h₁ := LocalWeil.isArithmeticPairEpsilonFactor_of_generator K h
  have h₂ := LocalWeil.isArithmeticPairEpsilonFactor_of_generator K h'
  obtain ⟨hc, hm⟩ := h₁.unique K h₂
  exact Prod.ext hc hm

/-- A candidate sends the rank-one class of a modulus-one character `χ`, which
lies in its domain, to the `GL₁` class of `χ`. -/
theorem candidate_character_generator {W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K)}
    {A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)} {Φ : W ≃ₗ[ℤ] A}
    (hΦ : LatticeMap.HenniartProperties.{uK, uW, uV, uE} K Φ) {e : ReciprocityCandidate K}
    (he : IsGeometricReciprocity K e) (χ : QuasiCharacter K) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1)
    (σ : LocalWeil.UnitaryBasis.{uK, uW} K)
    (hσ : σ.val = ⟨1, rankOneWeilCharacterClass K e χ⟩) :
    ∃ (x : W) (π : PadicSupercuspidal.UnitaryBasis.{uK, uV} K),
      (x : LocalWeil.UnitaryLattice.{uK, uW} K) = generator σ ∧
        π.val = ⟨1, rankOneSupercuspidalClass K χ⟩ ∧
          (Φ x : PadicSupercuspidal.UnitaryLattice.{uK, uV} K) = generator π := by
  obtain ⟨x, hx, -⟩ := (hΦ.1.2.2.2 e he χ hχ).2
  have hxσ : (x : LocalWeil.UnitaryLattice.{uK, uW} K) = generator σ := by
    apply Weil.includeUnitary_injective (Weil.Local.localWeilGroup K)
    change LocalWeil.includeUnitary K x = LocalWeil.includeUnitary K (generator σ)
    rw [hx, ← hσ]
    exact (Weil.includeUnitary_generator σ).symm
  obtain ⟨π, hπ, hΦx⟩ := candidate_rankOne K hΦ he χ hχ σ hσ x hxσ
  exact ⟨x, π, hxσ, hπ, hΦx⟩

/-- The central character of the image of `σ` under a candidate, pulled back
along reciprocity, is the determinant of `σ`. -/
theorem candidate_centralCharacter {W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K)}
    {A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)} {Φ : W ≃ₗ[ℤ] A}
    (hΦ : LatticeMap.HenniartProperties.{uK, uW, uV, uE} K Φ) {e : ReciprocityCandidate K}
    (he : IsGeometricReciprocity K e) (σ : LocalWeil.UnitaryBasis.{uK, uW} K)
    {π : PadicSupercuspidal.UnitaryBasis.{uK, uV} K} (x : W)
    (hx : (x : LocalWeil.UnitaryLattice.{uK, uW} K) = generator σ)
    (hΦx : (Φ x : PadicSupercuspidal.UnitaryLattice.{uK, uV} K) = generator π) :
    ∃ ω : K.Carrierˣ →* ℂˣ, PadicSupercuspidal.IsUnitaryBasisCentralCharacter K π ω ∧
      ∀ w, ω (reciprocityHom K e w) =
        Additive.toMul (LocalWeil.unitaryDeterminant K (generator σ)) w := by
  obtain ⟨ω, hω, hdet⟩ := hΦ.2.1 e he x
  rw [hΦx, PadicSupercuspidal.isUnitaryCentralCharacter_generator_iff] at hω
  rw [hx] at hdet
  exact ⟨ω, hω, hdet⟩

/-- A candidate gives one epsilon certificate for a pair of generators in its
domain and for the pair of their images. -/
theorem candidate_pairEpsilon {W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K)}
    {A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)} {Φ : W ≃ₗ[ℤ] A}
    (hΦ : LatticeMap.HenniartProperties.{uK, uW, uV, uE} K Φ) {eC : ReciprocityFamily K}
    {ε : NonabelianSystem.Assignment.{uK, uE} K} (hε : NonabelianSystem.IsSystem K eC ε)
    (ψ : NontrivialAdditiveCharacter K) (ν : LocalAdditiveHaarMeasure K)
    (hν : IsSelfDualMeasure K ψ ν) {a b : LocalWeil.UnitaryBasis.{uK, uW} K}
    {π τ : PadicSupercuspidal.UnitaryBasis.{uK, uV} K} (x y : W)
    (hx : (x : LocalWeil.UnitaryLattice.{uK, uW} K) = generator a)
    (hy : (y : LocalWeil.UnitaryLattice.{uK, uW} K) = generator b)
    (hΦx : (Φ x : PadicSupercuspidal.UnitaryLattice.{uK, uV} K) = generator π)
    (hΦy : (Φ y : PadicSupercuspidal.UnitaryLattice.{uK, uV} K) = generator τ) :
    ∃ c : ℂˣ × ℤ,
      LocalWeil.IsUnitaryPairEpsilonFactor K eC ε hε ψ (generator a) (generator b) c ∧
        PadicSupercuspidal.IsUnitaryBasisPairEpsilonFactor K ψ ν π τ c := by
  obtain ⟨c, hW, hG⟩ := ((hΦ.2.2 ψ).2 ν hν x y).2 eC ε hε
  rw [hx, hy] at hW
  rw [hΦx, hΦy] at hG
  exact ⟨c, hW, PadicSupercuspidal.isUnitaryBasisPairEpsilonFactor_of_generator K hG⟩

/-- The image of `σ` under any candidate has central character `ω₀` and an
epsilon factor against the trivial character of `GL₁` with exponent `c₀.2`,
where `ω₀ ∘ rec = det σ` and `c₀` is the Weil epsilon certificate of `σ`. -/
theorem candidate_image_mem {W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K)}
    {A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)} {Φ : W ≃ₗ[ℤ] A}
    (hΦ : LatticeMap.HenniartProperties.{uK, uW, uV, uE} K Φ) {e : ReciprocityCandidate K}
    (he : IsGeometricReciprocity K e) {eC : ReciprocityFamily K}
    {ε : NonabelianSystem.Assignment.{uK, uE} K} (hε : NonabelianSystem.IsSystem K eC ε)
    (ψ : NontrivialAdditiveCharacter K) (ν : LocalAdditiveHaarMeasure K)
    (hν : IsSelfDualMeasure K ψ ν) (σ : LocalWeil.UnitaryBasis.{uK, uW} K)
    (ω₀ : K.Carrierˣ →* ℂˣ)
    (hω₀ : ∀ w, ω₀ (reciprocityHom K e w) =
      Additive.toMul (LocalWeil.unitaryDeterminant K (generator σ)) w)
    (c₀ : ℂˣ × ℤ)
    (hW₀ : LocalWeil.IsUnitaryPairEpsilonFactor K eC ε hε ψ (generator σ)
      (generator (trivialWeilUnitary K e)) c₀)
    {k : ℕ} (x : W) (hx : (x : LocalWeil.UnitaryLattice.{uK, uW} K) = generator σ)
    (π : SupercuspidalAutomorphicClass.{uK, uV} K (k + 1).succPNat)
    (hπu : Supercuspidal.IsUnitaryClass _
      (⟨(k + 1).succPNat, π⟩ : PadicSupercuspidal.Basis.{uK, uV} K))
    (hΦx : (Φ x : PadicSupercuspidal.UnitaryLattice.{uK, uV} K) =
      generator (⟨⟨(k + 1).succPNat, π⟩, hπu⟩ : PadicSupercuspidal.UnitaryBasis.{uK, uV} K)) :
    (∀ a, SupercuspidalCentralActsBy K π a (ω₀ a)) ∧
      ∃ c : ℂˣ, IsSupercuspidalPairEpsilonFactor K ψ ν (r := k + 1) (n := 0) π
        (rankOneSupercuspidalClass.{uK, uV} K 1) (c, c₀.2) := by
  constructor
  · obtain ⟨ω, hω, hωdet⟩ := candidate_centralCharacter K hΦ he σ x hx hΦx
    have hωω : ω = ω₀ := by
      refine MonoidHom.ext fun a => ?_
      obtain ⟨w, rfl⟩ := reciprocityHom_surjective' K e a
      rw [hωdet, hω₀]
    subst hωω
    exact hω
  · have h1 : ∀ a : K.Carrierˣ, ‖((1 : QuasiCharacter K) a : ℂ)‖ = 1 := fun _ => by simp
    obtain ⟨x₁, π₁, hx₁, hπ₁, hΦx₁⟩ :=
      candidate_character_generator K hΦ he 1 h1 (trivialWeilUnitary K e) rfl
    obtain ⟨c, hW, hG⟩ := candidate_pairEpsilon K hΦ hε ψ ν hν x x₁ hx hx₁ hΦx hΦx₁
    have hc := unitaryPairEpsilon_generator_unique K hW hW₀
    subst hc
    obtain ⟨⟨m₁, τ₁⟩, hτ₁⟩ := π₁
    obtain ⟨rfl, hτ⟩ := Sigma.mk.inj_iff.mp hπ₁
    cases hτ
    exact ⟨c.1, hG⟩

/-- Two classes of `GL_(k+2)` with a common epsilon certificate against a unitary
class `t₀` agree, in the sense of the finite separation statement, at every
unramified twist of `t₀`. -/
theorem agree_of_unitaryBasisPairEpsilon
    (hGLε : RankinSelberg.UnramifiedTwistEpsilonStatement.{uK, uV, uV})
    (ψ : NontrivialAdditiveCharacter K) (ν : LocalAdditiveHaarMeasure K)
    (hν : IsSelfDualMeasure K ψ ν) {k : ℕ}
    (π π' : SupercuspidalAutomorphicClass.{uK, uV} K (k + 1).succPNat)
    (hπu : Supercuspidal.IsUnitaryClass _
      (⟨(k + 1).succPNat, π⟩ : PadicSupercuspidal.Basis.{uK, uV} K))
    (hπu' : Supercuspidal.IsUnitaryClass _
      (⟨(k + 1).succPNat, π'⟩ : PadicSupercuspidal.Basis.{uK, uV} K))
    (t : FiniteEpsilon.SupercuspidalTest.{uK, uV} K k) (z : ℂˣ)
    (t₀ : PadicSupercuspidal.UnitaryBasis.{uK, uV} K)
    (htw : PadicSupercuspidal.unramifiedTwistBasisEquiv K z t₀.val =
      (⟨t.1.val.succPNat, t.2⟩ : PadicSupercuspidal.Basis.{uK, uV} K))
    (c : ℂˣ × ℤ)
    (h : PadicSupercuspidal.IsUnitaryBasisPairEpsilonFactor K ψ ν ⟨⟨_, π⟩, hπu⟩ t₀ c)
    (h' : PadicSupercuspidal.IsUnitaryBasisPairEpsilonFactor K ψ ν ⟨⟨_, π'⟩, hπu'⟩ t₀ c) :
    FiniteEpsilon.Agree K ψ ν π π' t := by
  obtain ⟨⟨m, τ₀⟩, hτ₀⟩ := t₀
  obtain ⟨r, τ⟩ := t
  have hm : m = r.val.succPNat := congrArg Sigma.fst htw
  subst hm
  have hτ : supercuspidalTwist K (fieldUnramified K z) τ₀ = τ := eq_of_heq (Sigma.mk.inj htw).2
  subst hτ
  have hr : r.val ≤ k + 1 := by
    have := r.isLt
    omega
  refine ⟨(c.1 * z ^ c.2, c.2), ?_, ?_⟩
  · exact (isSupercuspidalPairEpsilonFactor_iff_class K ψ ν hr _ _ _).mp
      (isSupercuspidalPairEpsilonFactor_unramifiedTwist_right K hGLε ψ ν hν
        (r := k + 1) (n := r.val) (c := c.1) (m := c.2) h z)
  · exact (isSupercuspidalPairEpsilonFactor_iff_class K ψ ν hr _ _ _).mp
      (isSupercuspidalPairEpsilonFactor_unramifiedTwist_right K hGLε ψ ν hν
        (r := k + 1) (n := r.val) (c := c.1) (m := c.2) h' z)

/-- Every lower-rank test is an unramified twist of a unitary class which, by
surjectivity in lower rank, is the stable image of a unitary Weil class. -/
theorem exists_lift_of_lowerRank {k : ℕ}
    (ih : ∀ r : ℕ+, r < (k + 1).succPNat → RankStage.{uK, uW, uV, uE} K r)
    (t : FiniteEpsilon.SupercuspidalTest.{uK, uV} K k) :
    ∃ (z : ℂˣ) (t₀ : PadicSupercuspidal.UnitaryBasis.{uK, uV} K)
      (σt : LocalWeil.UnitaryBasis.{uK, uW} K),
      PadicSupercuspidal.unramifiedTwistBasisEquiv K z t₀.val =
          (⟨t.1.val.succPNat, t.2⟩ : PadicSupercuspidal.Basis.{uK, uV} K) ∧
        IsStableImage.{uK, uW, uV, uE} K σt (generator t₀) := by
  obtain ⟨z, t₀, hfo, htw⟩ := exists_unitaryFiniteOrderTwist K ⟨t.1.val.succPNat, t.2⟩
  have hrank : t₀.val.1 = t.1.val.succPNat := congrArg Sigma.fst htw
  have hlt : t.1.val.succPNat < (k + 1).succPNat := Nat.succPNat_lt_succPNat.mpr t.1.isLt
  obtain ⟨σt, -, hst⟩ := (ih _ hlt).2 t₀ hrank hfo
  exact ⟨z, t₀, σt, htw, hst⟩

/-- Henniart (2000), §4.3: given stable images and surjectivity in all ranks below
`k + 2`, every finite-image unitary irreducible class of dimension `k + 2` has a
stable image. -/
theorem stableExistsAt_succ_succ (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    (hfinite : SupercuspidalEpsilonConductorFinitenessStatement.{uK, uV})
    (hGLε : RankinSelberg.UnramifiedTwistEpsilonStatement.{uK, uV, uV})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e) {eC : ReciprocityFamily K}
    {ε : NonabelianSystem.Assignment.{uK, uE} K} (hε : NonabelianSystem.IsSystem K eC ε)
    (k : ℕ) (ih : ∀ r : ℕ+, r < (k + 1).succPNat → RankStage.{uK, uW, uV, uE} K r) :
    StableExistsAt.{uK, uW, uV, uE} K (k + 1).succPNat := by
  classical
  intro σ hσn hσfin
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists K K.canonicalTopologicalData
  obtain ⟨Q₀, _, _, q₀, hq₀⟩ := hσfin
  obtain ⟨W₀, A₀, Φ₀, hΦ₀⟩ := hCE p K Q₀ q₀
  obtain ⟨ν, hν⟩ := (hΦ₀.2.2.2 ψ).1
  -- The central character and the epsilon exponent shared by all candidate images.
  let x₀ : W₀ := ⟨generator σ, hΦ₀.1 hq₀⟩
  obtain ⟨π₀, hΦx₀, -⟩ := IsCandidate.exists_generator K hΦ₀.2 σ x₀ rfl
  obtain ⟨ω₀, -, hω₀⟩ := candidate_centralCharacter K hΦ₀.2 he σ x₀ rfl hΦx₀
  have h1 : ∀ a : K.Carrierˣ, ‖((1 : QuasiCharacter K) a : ℂ)‖ = 1 := fun _ => by simp
  obtain ⟨x₁, π₁, hx₁, -, hΦx₁⟩ :=
    candidate_character_generator K hΦ₀.2 he 1 h1 (trivialWeilUnitary K e) rfl
  obtain ⟨c₀, hW₀, -⟩ := candidate_pairEpsilon K hΦ₀.2 hε ψ ν hν x₀ x₁ rfl hx₁ hΦx₀ hΦx₁
  -- The finite set of possible images and a finite separating family of tests.
  let P : Set (SupercuspidalAutomorphicClass.{uK, uV} K (k + 1).succPNat) :=
    {π | (∀ a, SupercuspidalCentralActsBy K π a (ω₀ a)) ∧
      ∃ c : ℂˣ, IsSupercuspidalPairEpsilonFactor K ψ ν (r := k + 1) (n := 0) π
        (rankOneSupercuspidalClass.{uK, uV} K 1) (c, c₀.2)}
  have hPfin : P.Finite := hfinite p K ψ ν hν (k + 1) ω₀ c₀.2
  obtain ⟨D, hD⟩ := finiteSupercuspidalEpsilonSeparation_of_localConverse.{uK, uV, uV} K
    RankinSelberg.supercuspidalLocalConverse.{uK, uV, uV} ψ ν hν k P hPfin
  -- Lift the tests and pass to a quotient through which all lifts factor.
  choose z t₀ σt htw hst using exists_lift_of_lowerRank.{uK, uW, uV, uE} K ih
  choose Qt hQt hQtf qt hqt hallt using fun t => (hst t).exists_quotient K
  let := hQt
  let := hQtf
  let T : Fin D.card → FiniteEpsilon.SupercuspidalTest.{uK, uV} K k :=
    fun i => (D.equivFin.symm i).val
  let R := Q₀ × ((i : Fin D.card) → Qt (T i))
  let r : Field.absoluteGaloisGroup K.Carrier →* R := q₀.prod (MonoidHom.pi fun i => qt (T i))
  have hσr : generator σ ∈ LocalWeil.unitaryFiniteFactoringSupported.{uK, uW, uK} K r := by
    have hle := unitaryFiniteFactoringSupported_comp_le.{uK, uW, uK, uK} K r
      (MonoidHom.fst Q₀ ((i : Fin D.card) → Qt (T i)))
    rw [MonoidHom.fst_comp_prod] at hle
    exact hle hq₀
  obtain ⟨Wq, Aq, Φq, hΦq⟩ := hCE p K R r
  let x' : Wq := ⟨generator σ, hΦq.1 hσr⟩
  obtain ⟨π', hΦx', hπ'n⟩ := IsCandidate.exists_generator K hΦq.2 σ x' rfl
  refine ⟨generator π', R, inferInstance, inferInstance, r, hσr, ⟨Wq, Aq, Φq, hΦq⟩, ?_⟩
  intro W A Φ hΦ x hx
  obtain ⟨π, hΦx, hπn⟩ := IsCandidate.exists_generator K hΦ.2 σ x hx
  rw [hΦx]
  obtain ⟨⟨m, πc⟩, hπu⟩ := π
  obtain ⟨⟨m', πc'⟩, hπu'⟩ := π'
  have hm : m = (k + 1).succPNat := hπn.trans hσn
  have hm' : m' = (k + 1).succPNat := hπ'n.trans hσn
  subst hm hm'
  have hmem := candidate_image_mem K hΦ.2 he hε ψ ν hν σ ω₀ hω₀ c₀ hW₀ x hx πc hπu hΦx
  have hmem' := candidate_image_mem K hΦq.2 he hε ψ ν hν σ ω₀ hω₀ c₀ hW₀ x' rfl πc' hπu' hΦx'
  have hπc : πc = πc' := by
    refine hD πc hmem πc' hmem' fun t ht => ?_
    obtain ⟨i, rfl⟩ : ∃ i, T i = t := ⟨D.equivFin ⟨t, ht⟩, by simp [T]⟩
    let f : R →* Qt (T i) :=
      (Pi.evalMonoidHom (fun j => Qt (T j)) i).comp (MonoidHom.snd _ _)
    have hf : f.comp r = qt (T i) := by
      ext g
      rfl
    obtain ⟨xt, hxt, hΦxt⟩ := hallt (T i) r f hf W A Φ hΦ
    obtain ⟨xt', hxt', hΦxt'⟩ := hallt (T i) r f hf Wq Aq Φq hΦq
    obtain ⟨c, hWc, hGc⟩ := candidate_pairEpsilon K hΦ.2 hε ψ ν hν x xt hx hxt hΦx hΦxt
    obtain ⟨c', hWc', hGc'⟩ :=
      candidate_pairEpsilon K hΦq.2 hε ψ ν hν x' xt' rfl hxt' hΦx' hΦxt'
    have hcc := unitaryPairEpsilon_generator_unique K hWc hWc'
    subst hcc
    exact agree_of_unitaryBasisPairEpsilon K hGLε ψ ν hν πc πc' hπu hπu' (T i) (z (T i))
      (t₀ (T i)) (htw (T i)) c hGc hGc'
  subst hπc
  rfl

/-- Henniart (2000), §4.3, inductive step for 4.2 (a): candidate existence, the
conductor finiteness of candidate sets, normalized local reciprocity and local
constants for every normalized family give `ChoiceIndependenceStepStatement`. -/
theorem choiceIndependenceStep_of_inputs
    (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    (hfinite : SupercuspidalEpsilonConductorFinitenessStatement.{uK, uV})
    (hrec : LocalClassField.CommonClosureReciprocityExistence.{uK})
    (hsys : ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (eC : ReciprocityFamily K),
      NonabelianSystem.Exists.{uK, uE} K eC) :
    ChoiceIndependenceStepStatement.{uK, uW, uV, uE} := by
  intro p _ K n hn ih
  obtain ⟨eC, heC⟩ := hrec p K K.canonicalTopologicalData
  have he := baseGeometricReciprocityProof K eC heC
  obtain ⟨ε, hε⟩ := hsys p K eC heC
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k + 1).succPNat = n := by
    refine ⟨(n : ℕ) - 2, PNat.coe_injective ?_⟩
    have : 1 < (n : ℕ) := hn
    simp only [Nat.succPNat_coe]
    omega
  exact stableExistsAt_succ_succ K hCE hfinite RankinSelberg.unramifiedTwistEpsilon he hε k ih

end Langlands.Henniart.Extension
