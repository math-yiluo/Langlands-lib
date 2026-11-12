import Langlands.Correspondence.HenniartSurjectivityTransfer
import Langlands.Correspondence.HenniartConductorFinitenessProof
import Langlands.Correspondence.HenniartArithmeticTwistProof
import Langlands.Correspondence.RankOneEpsilonCharacterTransport
import Langlands.LocalFactor.ConductorExponentStatement
import Langlands.HarmonicAnalysis.ConductorTransport

/-!
# Conductors of the extension of the stable images

Henniart (2000), §4.3 with Henniart (1988), Théorème 1.2: the extension of the
stable images of rank `n` sends a Weil class of Artin conductor `a` to a
supercuspidal class of conductor `a`. Both conductors are read off from the
exponent of one epsilon factor against the trivial character: on the Weil side
by Tate's (3.4.5) and Deligne's (5.5.2), on the side of `GL_n` by
Jacquet–Piatetski-Shapiro–Shalika (5.1) and Bushnell–Henniart–Kutzko.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap
open Weil.Local LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne

universe uK uW uV uE

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartRankConductorFieldTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

local instance henniartRankConductorBottomTopology :
    TopologicalSpace (baseExtension K).field :=
  (fieldData K (baseExtension K)).topology

/-! ### Presentations along equivalences -/

/-- A finite inertia presentation transports along an equivalence of
representations, with the same Artin conductor. -/
theorem exists_presentation_of_equiv {A : LocalWeilRepresentation.{uK, uW} K}
    {B : FiniteRepresentation.{0, uK, uV} ℂ (localWeilGroup K)}
    (e : FiniteRepresentation.Equiv A B) (P : Ramification.Padic.FiniteInertiaPresentation K A)
    (hsurj : Function.Surjective (Ramification.Padic.weilInertiaRestriction K P.extension)) :
    ∃ (P' : Ramification.Padic.FiniteInertiaPresentation K B)
      (hsurj' : Function.Surjective (Ramification.Padic.weilInertiaRestriction K P'.extension)),
      P'.artinConductor hsurj' = P.artinConductor hsurj := by
  have hker : (Ramification.Padic.weilInertiaRestriction K P.extension).toMonoidHom.ker ≤
      (Ramification.Padic.localInertiaRepresentation K B).ker := by
    intro w hw
    have hA : A.representation w = 1 := P.kernel_le hw
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro v
    have h := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap w (e.symm v)
    rw [Representation.Equiv.coe_toIntertwiningMap] at h
    change B.representation w v = v
    have h' : e (A.representation w (e.symm v)) = B.representation w v := by
      rw [h]
      congr 1
      exact EquivLike.apply_inv_apply e v
    rw [← h', hA, Module.End.one_apply]
    exact EquivLike.apply_inv_apply e v
  refine ⟨⟨P.extension, hker⟩, hsurj, ?_⟩
  let eI : (Ramification.Padic.localInertiaRepresentation K A).Equiv
      (Ramification.Padic.localInertiaRepresentation K B) :=
    Representation.Equiv.mk e.toLinearEquiv (fun g => e.toIntertwiningMap.isIntertwining' g)
  exact (Ramification.Padic.artinConductorOfQuotient_equiv _ _ _ hsurj P.kernel_le hker
    eI).symm

/-! ### Exponents from epsilon monomials -/

/-- If `c q^(-ms) = d q^(-ts)` for every `s`, with `t` real, then `m = t`. -/
theorem exponent_eq_of_monomial {q : ℕ} (hq : 1 < q) {c : ℂˣ} {m : ℤ} {d : ℂ} {t : ℝ}
    (h : ∀ s : ℂ, RankinSelberg.epsilonMonomial q c m s = d * (q : ℂ) ^ (-((t : ℂ)) * s)) :
    (m : ℝ) = t := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast lt_trans Nat.zero_lt_one hq
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have h0 := h 0
  have h1 := h 1
  simp only [RankinSelberg.epsilonMonomial, RankinSelberg.spectralPoint, neg_zero,
    Complex.cpow_zero, one_zpow, mul_one, mul_zero] at h0
  simp only [RankinSelberg.epsilonMonomial, RankinSelberg.spectralPoint, mul_one,
    Complex.cpow_neg_one] at h1
  rw [← h0] at h1
  have h2 : ((q : ℂ)⁻¹) ^ m = (q : ℂ) ^ (-(t : ℂ)) := mul_left_cancel₀ c.ne_zero h1
  have hr : (q : ℂ) ^ (-(t : ℂ)) = (((q : ℝ) ^ (-t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hq0.le]
    push_cast
    rfl
  have hl : ((q : ℂ)⁻¹) ^ m = ((((q : ℝ)⁻¹) ^ m : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hl, hr] at h2
  have h3 : ((q : ℝ)⁻¹) ^ m = (q : ℝ) ^ (-t) := by exact_mod_cast h2
  rw [← Real.rpow_intCast, Real.inv_rpow hq0.le, ← Real.rpow_neg hq0.le] at h3
  have h4 := congrArg Real.log h3
  rw [Real.log_rpow hq0, Real.log_rpow hq0] at h4
  have hlog : Real.log q ≠ 0 := (Real.log_pos hq1).ne'
  have h5 := mul_right_cancel₀ hlog h4
  linarith

/-! ### The additive conductor of the bottom-field character -/

/-- The bottom-field character corresponding to `ψ` has the same additive conductor. -/
theorem additiveConductor_base_eq (ψ : NontrivialAdditiveCharacter K)
    (ψ₁ : AdditiveCharacter K (baseExtension K)) (h : IsBaseCharacter K ψ ψ₁) :
    (fieldData K (baseExtension K)).additiveConductor ψ₁ =
      K.canonicalTopologicalData.additiveConductor ψ := by
  let B := (baseExtension K).asPadicField (p := p)
  let _ := B.algebra
  let ψ₁' : @HarmonicAnalysis.UnitaryAdditiveCharacter B.Carrier _
      B.canonicalTopologicalData.topology := ψ₁
  have hψ : PadicField.ConductorTransport.additiveCharacter B K (baseFieldPadicEquiv K) ψ₁' =
      ψ := by
    apply HarmonicAnalysis.UnitaryAdditiveCharacter.ext
    intro y
    change ψ₁.toAddChar ((baseFieldPadicEquiv K).symm y) = ψ.toAddChar y
    have hy := h ((baseFieldPadicEquiv K).symm y)
    have he : IntermediateField.botEquiv K.Carrier (AlgebraicClosure K.Carrier)
        ((baseFieldPadicEquiv K).symm y) = y :=
      (baseFieldPadicEquiv K).apply_symm_apply y
    rw [he] at hy
    exact hy
  have key := PadicField.ConductorTransport.additiveConductor_eq B K (baseFieldPadicEquiv K) ψ₁'
  calc (fieldData K (baseExtension K)).additiveConductor ψ₁
      = B.canonicalTopologicalData.additiveConductor ψ₁' := rfl
    _ = K.canonicalTopologicalData.additiveConductor
          (PadicField.ConductorTransport.additiveCharacter B K (baseFieldPadicEquiv K) ψ₁') :=
        key.symm
    _ = K.canonicalTopologicalData.additiveConductor ψ := congrArg _ hψ

/-! ### The Weil side -/

/-- Tate (3.4.5) and Deligne (5.5.2): the exponent `m` of an arithmetic epsilon
factor `c q^(-ms)` of `A₀` against the trivial character is `a(A₀) + n(ψ) dim A₀`,
for the Artin conductor `a(A₀)` at any actual finite inertia presentation. -/
theorem exponent_of_isArithmeticPairEpsilonFactor
    (hSC : ConductorExponent.SpectralConductorStatement.{uK, uW} K)
    (e : ReciprocityCandidate K) (eC : ReciprocityFamily K)
    (ε : NonabelianSystem.Assignment.{uK, uW} K) (hε : NonabelianSystem.IsSystem K eC ε)
    (ψ : NontrivialAdditiveCharacter K) (A₀ : LocalWeilRepresentation.{uK, uW} K)
    (P : Ramification.Padic.FiniteInertiaPresentation K A₀)
    (hsurj : Function.Surjective (Ramification.Padic.weilInertiaRestriction K P.extension))
    (c : ℂˣ) (m : ℤ)
    (h : IsArithmeticPairEpsilonFactor K eC ε hε ψ
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom A₀))
      (weilPairClass K (rankOneWeilCharacterClass.{uK, uW} K e 1)) c m) :
    (m : ℝ) = ((P.artinConductor hsurj : ℚ) : ℝ) +
      (K.canonicalTopologicalData.additiveConductor ψ : ℝ) * A₀.rank := by
  obtain ⟨⟨ψ₁, μ₁, A, B, ⟨hψ₁, hμ₁, hAr, hBr⟩, hAc, hBc⟩, ⟨Φ⟩, hall⟩ := h
  obtain ⟨fA⟩ := IsBaseRestriction.nonempty_equiv K rfl hAr
  obtain ⟨fB⟩ := IsBaseRestriction.nonempty_equiv_rankOneWeilCharacterClass K e 1 hBr
  have hA0 : A.monodromy = 0 := monodromy_eq_zero_of_isBaseRestriction K A₀ hAr
  have hB0 : B.monodromy = 0 := monodromy_eq_zero_of_equiv fB.symm rfl
  set χ₀ := baseRestrictedWeilCharacter K (LocalFactor.RankOne.weilCharacter K e 1)
  have hχ₀ : χ₀.toMonoidHom = 1 := by
    ext g
    rfl
  let eT : FiniteRepresentation.Equiv
      (FiniteRepresentation.tensor A.toFiniteRepresentation B.toFiniteRepresentation)
      A.toFiniteRepresentation :=
    ((FiniteRepresentation.tensorEquiv (Representation.Equiv.refl _)
      fB.representationEquiv).trans
      (FiniteRepresentation.tensorCharacterLineEquiv A.toFiniteRepresentation
        χ₀.toMonoidHom)).trans
      ((FiniteRepresentation.twistEquivOfEq hχ₀ _).trans
        (FiniteRepresentation.twistOneEquiv _))
  let fT := WeilDeligneRepresentation.zeroMonodromyEquivOfEquiv _
    (A := WeilDeligneRepresentation.tensor A B) (B := A)
    (WeilDeligneRepresentation.tensor_monodromy_eq_zero hA0 hB0) hA0 eT
  have hval : ∀ s : ℂ,
      (CommonClosureGamma.conditionalPairEpsilonValue K eC ε hε (baseExtension K) ψ₁ μ₁
        A B hAc hBc Φ s : ℂ) =
      (CommonClosureSpectral.conditionalDeligneValue K eC ε hε (baseExtension K) ψ₁ μ₁
        (underlyingClass K (baseExtension K) A hAc) s : ℂ) := by
    intro s
    change (conditionalEpsilonValue K eC ε hε (baseExtension K) ψ₁ μ₁
      (WeilDeligneRepresentation.tensor A B)
      (CommonClosureGamma.tensor_isContinuous K (baseExtension K) A B hAc hBc) Φ s : ℂ) = _
    rw [conditionalEpsilonValue_eq_of_equiv K eC ε hε (baseExtension K) ψ₁ μ₁ _ hAc fT Φ s,
      conditionalEpsilonValue_of_monodromy_zero K eC ε hε (baseExtension K) ψ₁ μ₁ A hAc hA0
        Φ s]
  let eA : FiniteRepresentation.Equiv A₀
      (FiniteRepresentation.restrict (ConductorExponent.baseInclusion K).toMonoidHom
        A.toFiniteRepresentation) :=
    Representation.Equiv.mk fA.representationEquiv.toLinearEquiv
      (fun g => fA.representationEquiv.toIntertwiningMap.isIntertwining'
        (ConductorExponent.baseInclusion K g))
  obtain ⟨P', hsurj', hP'⟩ := exists_presentation_of_equiv K eA P hsurj
  have hspec := hSC eC ε hε ψ₁ μ₁ A.toFiniteRepresentation hAc P' hsurj'
  have hrank : A.toFiniteRepresentation.rank = A₀.rank :=
    (FiniteRepresentation.rank_eq_of_equiv eA).symm
  have hn : ConductorExponent.additiveConductor K ψ₁ =
      K.canonicalTopologicalData.additiveConductor ψ :=
    additiveConductor_base_eq K ψ ψ₁ hψ₁
  apply exponent_eq_of_monomial K.canonicalTopologicalData.residueCardinality_gt_one
    (c := c) (d := (CommonClosureSpectral.conditionalDeligneValue K eC ε hε (baseExtension K) ψ₁ μ₁
        (underlyingClass K (baseExtension K) A hAc) 0 : ℂ))
  intro s
  rw [← hall ψ₁ μ₁ A B ⟨hψ₁, hμ₁, hAr, hBr⟩ hAc hBc Φ s, hval s]
  have h1 := hspec s
  change (CommonClosureSpectral.conditionalDeligneValue K eC ε hε (baseExtension K) ψ₁ μ₁
      (underlyingClass K (baseExtension K) A hAc) s : ℂ) = _ at h1
  rw [h1, hP', hn]
  refine congrArg₂ (· * ·) rfl ?_
  show (CommonClosureSpectral.baseCardinality K : ℂ) ^
      (-(((P.artinConductor hsurj : ℚ) : ℂ) +
        ((K.canonicalTopologicalData.additiveConductor ψ : ℤ) : ℂ) *
          ((A.toFiniteRepresentation.rank : ℕ) : ℂ)) * s) = _
  rw [hrank]
  simp only [CommonClosureSpectral.baseCardinality, Complex.ofReal_natCast]
  push_cast
  ring_nf

/-- The exponent of an arithmetic epsilon factor of an unramified twist `σ = z · σ₀`
against the trivial character, computed from an epsilon factor of `σ₀`: it is
`a(σ) + n(ψ) (k+1)` for the Artin conductor `a(σ)`. -/
theorem weil_exponent_of_twist
    (hSC : ConductorExponent.SpectralConductorStatement.{uK, uW} K)
    (e : ReciprocityCandidate K) (eC : ReciprocityFamily K)
    (ε : NonabelianSystem.Assignment.{uK, uW} K) (hε : NonabelianSystem.IsSystem K eC ε)
    (ψ : NontrivialAdditiveCharacter K) {k : ℕ}
    (σ₀ σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) (z : ℂˣ)
    (hσ : σ = FiniteRepresentation.continuousIrreducibleTwistEquiv
      (localUnramifiedCharacter K z) _ σ₀)
    {a : ℕ} (ha : Numerical.HasArtinConductor K σ a) {c : ℂˣ} {m : ℤ}
    (h : IsArithmeticPairEpsilonFactor K eC ε hε ψ (weilPairClass K σ₀)
      (weilPairClass K (rankOneWeilCharacterClass.{uK, uW} K e 1)) c m) :
    (m : ℝ) = a + (K.canonicalTopologicalData.additiveConductor ψ : ℝ) * (k + 1) := by
  have h' := (arithmeticPairUnramifiedTwist p K eC ε hε ψ k 0 σ₀
    (rankOneWeilCharacterClass.{uK, uW} K e 1) z 1).2 c m h
  have h1 : localUnramifiedCharacter K 1 = 1 := by
    ext g
    simp [localUnramifiedCharacter]
  rw [h1, FiniteRepresentation.continuousIrreducibleTwistEquiv_one] at h'
  change IsArithmeticPairEpsilonFactor K eC ε hε ψ
    (weilPairClass K (FiniteRepresentation.continuousIrreducibleTwistEquiv
      (localUnramifiedCharacter K z) _ σ₀))
    (weilPairClass K (rankOneWeilCharacterClass.{uK, uW} K e 1)) (c * (z * 1) ^ m) m at h'
  rw [← hσ] at h'
  obtain ⟨A, P, hsurj, hA, hP⟩ := ha
  have hX : weilPairClass K σ = WeilDeligneRepresentation.classOf
      (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom A) := by
    unfold weilPairClass
    rw [← hA]
    rfl
  rw [hX] at h'
  have hm := exponent_of_isArithmeticPairEpsilonFactor K hSC e eC ε hε ψ A P hsurj _ m h'
  have hrank : A.rank = k + 1 := by
    have h2 := σ.property
    have h3 : FiniteRepresentation.classRank (FiniteRepresentation.classOf A) =
        (k.succPNat : ℕ) := by
      rw [hA]
      exact h2
    exact h3
  rw [hm, hP, hrank]
  push_cast
  ring

/-! ### The side of `GL_n` -/

/-- A newvector conductor is the first fixed level. -/
theorem firstFixedLevel_eq_of_isNewvectorConductor {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module ℂ V] {ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V} {b : ℕ}
    (h : letI := K.canonicalTopologicalData.valuativeRel; Conductor.IsNewvectorConductor ρ b) :
    (letI := K.canonicalTopologicalData.valuativeRel; Conductor.firstFixedLevel ρ) = b := by
  let := K.canonicalTopologicalData.valuativeRel
  have hh : Conductor.HasNewvectorLevel ρ := ⟨b, h.1⟩
  rw [Conductor.firstFixedLevel_of_hasNewvectorLevel ρ hh,
    (Conductor.newvectorConductor_eq_iff ρ hh b).2 h]

/-- The conductor of a supercuspidal class with an epsilon factor `c q^(-ms)`
against the trivial character of `GL₁` is `m - (k+1) n(ψ)`. -/
theorem conductor_eq_of_pairEpsilon
    (hBHK : RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0})
    (hJPSS : Conductor.ConductorExponentStatement.{uK, uV})
    (ψ : NontrivialAdditiveCharacter K) (ν : LocalAdditiveHaarMeasure K)
    (hν : IsSelfDualMeasure K ψ ν) {k : ℕ}
    (π : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) {c : ℂˣ} {m : ℤ}
    (h : IsSupercuspidalPairEpsilonFactor K ψ ν (r := k) (n := 0) π
      (rankOneSupercuspidalClass.{uK, uV} K 1) (c, m)) :
    ∃ b : ℕ, (b : ℤ) = m - ((k + 1 : ℕ) : ℤ) * K.canonicalTopologicalData.additiveConductor ψ ∧
      Numerical.conductor K π = b := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep π
  obtain ⟨b, hb, hnew⟩ := exists_newvectorConductor_of_pairEpsilon K hBHK hJPSS ψ ν hν A h
  exact ⟨b, hb, firstFixedLevel_eq_of_isNewvectorConductor K hnew⟩

/-- Twisting the first member of a supercuspidal pair by an unramified character
keeps the exponent of its epsilon factor. -/
theorem isSupercuspidalPairEpsilonFactor_unramifiedTwist_left
    (hGLε : RankinSelberg.UnramifiedTwistEpsilonStatement.{uK, uV, uV}) {r n : ℕ}
    (ψ : NontrivialAdditiveCharacter K) (ν : LocalAdditiveHaarMeasure K)
    (hν : IsSelfDualMeasure K ψ ν)
    {π : SupercuspidalAutomorphicClass.{uK, uV} K r.succPNat}
    {τ : SupercuspidalAutomorphicClass.{uK, uV} K n.succPNat} {c : ℂˣ} {m : ℤ}
    (h : IsSupercuspidalPairEpsilonFactor K ψ ν π τ (c, m)) (z : ℂˣ) :
    ∃ c' : ℂˣ, IsSupercuspidalPairEpsilonFactor K ψ ν
      (supercuspidalTwist K (fieldUnramified K z) π) τ (c', m) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep π
  obtain ⟨B, rfl⟩ := Quotient.exists_rep τ
  obtain ⟨u, -, hχ⟩ := exists_unramifiedExponent K z
  let ν' : LocalFactor.PadicAbelian.SelfDualHaar K.canonicalTopologicalData ψ := ⟨ν, hν⟩
  obtain ⟨e₁, he₁m, -, -, h2⟩ := hGLε p K ψ ν' r n A.obj.representation
    B.obj.representation u (fieldUnramified K z).toMonoidHom hχ (c, m) h
  have he : e₁ = (e₁.1, m) := Prod.ext rfl he₁m
  rw [he] at h2
  exact ⟨e₁.1, h2⟩

/-! ### Conductors of the extension -/

/-- The extension of the stable images of rank `k + 1` sends a Weil class of Artin
conductor `a` to a supercuspidal class of conductor `a`. -/
theorem rankExtension_conductor
    (hSC : ConductorExponent.SpectralConductorStatement.{uK, uW} K)
    (hBHK : RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0})
    (hJPSS : Conductor.ConductorExponentStatement.{uK, uV})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e)
    {eC : ReciprocityFamily K} {ε : NonabelianSystem.Assignment.{uK, uW} K}
    (hε : NonabelianSystem.IsSystem K eC ε) {k : ℕ}
    (hS : StableExistsAt.{uK, uW, uV, uW} K k.succPNat)
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) {a : ℕ}
    (ha : Numerical.HasArtinConductor K σ a) :
    Numerical.conductor K (rankExtension K hS σ) = a := by
  obtain ⟨z, π₀, b₀, hdec, he₁⟩ := rankExtensionBasis_spec K hS σ
  have hrank₀ : π₀.val.1 = k.succPNat := by
    have := rankExtensionBasis_rank K hS σ
    rw [he₁] at this
    exact this
  obtain ⟨Q, _, _, q, hσq, ⟨W, A, Φ, hΦ⟩, hall⟩ := hdec.2
  have hΦx := hall W A Φ hΦ ⟨generator b₀, hΦ.1 hσq⟩ rfl
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists K K.canonicalTopologicalData
  obtain ⟨ν, hν⟩ := (hΦ.2.2.2 ψ).1
  have h1 : ∀ a : K.Carrierˣ, ‖((1 : QuasiCharacter K) a : ℂ)‖ = 1 := fun _ => by simp
  obtain ⟨x₁, π₁, hx₁, hπ₁, hΦx₁⟩ :=
    candidate_character_generator K hΦ.2 he 1 h1 (trivialWeilUnitary K e) rfl
  obtain ⟨c₀, hW, hG⟩ := candidate_pairEpsilon K hΦ.2 hε ψ ν hν ⟨generator b₀, hΦ.1 hσq⟩ x₁
    rfl hx₁ hΦx hΦx₁
  have hWA := LocalWeil.isArithmeticPairEpsilonFactor_of_generator K hW
  -- the Weil side
  obtain ⟨⟨m', σ₀⟩, hb₀u⟩ := b₀
  have hdec1 := hdec.1
  obtain ⟨rfl, hσheq⟩ := Sigma.mk.inj hdec1
  have hσ := eq_of_heq hσheq
  have hweil := weil_exponent_of_twist K hSC e eC ε hε ψ σ₀ σ z hσ.symm ha hWA
  -- the side of `GL_n`
  obtain ⟨⟨m₀, π₀'⟩, hπ₀u⟩ := π₀
  obtain rfl : m₀ = k.succPNat := hrank₀
  obtain ⟨⟨m₁, τ₁⟩, hτ₁⟩ := π₁
  obtain ⟨rfl, hτ⟩ := Sigma.mk.inj_iff.mp hπ₁
  cases hτ
  obtain ⟨c', hG'⟩ := isSupercuspidalPairEpsilonFactor_unramifiedTwist_left K
    RankinSelberg.unramifiedTwistEpsilon ψ ν hν (r := k) (n := 0) hG z
  obtain ⟨b, hb, hcond⟩ := conductor_eq_of_pairEpsilon K hBHK hJPSS ψ ν hν _ hG'
  have hφ : rankExtension K hS σ = supercuspidalTwist K (fieldUnramified K z) π₀' := by
    have h2 := (sigma_rankExtension K hS σ).trans he₁
    exact eq_of_heq (Sigma.mk.inj h2).2
  rw [hφ, hcond]
  have hbr : (b : ℝ) = a := by
    have hb' : (b : ℝ) = (c₀.2 : ℝ) - ((k + 1 : ℕ) : ℝ) *
        (K.canonicalTopologicalData.additiveConductor ψ : ℝ) := by
      exact_mod_cast hb
    rw [hb', hweil]
    push_cast
    ring
  have hba : b = a := by exact_mod_cast hbr
  rw [hba]

end Langlands.Henniart.Extension
