import Langlands.Correspondence.HenniartExtensionTwist
import Langlands.Representation.RankinSelberg.UnramifiedTwistLFactorProof

/-!
# Pair factors and the extended stable map

Henniart (1993), §4.4. For a pair of stable decompositions `σ = z · b₀` and
`τ = z' · b₀'`, a common candidate for `b₀` and `b₀'` matches the pair L- and
epsilon factors of `(b₀, b₀')` with those of their stable images. Twisting both
members by unramified characters substitutes `X ↦ z z' X` in the L-factor and
multiplies an epsilon certificate `(c, m)` by `(z z') ^ m`, on both sides. The
GL-side L-factor law is the published `RankinSelberg.unramifiedTwistLFactor`;
the GL-side epsilon law and the Weil-side laws are explicit inputs.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap Polynomial

universe uK uW uV uE

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartExtensionFactorsFieldTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

/-- The unramified character with value `z` at the uniformizer is `|·|^u` for a
complex `u` with `q^(-u) = z`. -/
theorem exists_unramifiedExponent (z : ℂˣ) :
    ∃ u : ℂ, (K.canonicalTopologicalData.residueCardinality : ℂ) ^ (-u) = z ∧
      ∀ x : K.Carrierˣ, (fieldUnramified K z x : ℂ) =
        ((K.canonicalTopologicalData.normalizedAbs (x : K.Carrier) : ℝ) : ℂ) ^ u := by
  set T := K.canonicalTopologicalData
  set q := T.residueCardinality
  have hq : (1 : ℝ) < q := by exact_mod_cast T.residueCardinality_gt_one
  have hq0 : (0 : ℝ) < q := lt_trans zero_lt_one hq
  set L := Real.log q
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hq).ne'
  have hlogq : Complex.log (q : ℂ) = (L : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hq0.le]
  refine ⟨-(Complex.log z) / L, ?_, ?_⟩
  · have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
    rw [Complex.cpow_def_of_ne_zero hq', hlogq, neg_div, neg_neg, mul_div_cancel₀ _ hL,
      Complex.exp_log z.ne_zero]
  · intro x
    have hx : (x : K.Carrier) ≠ 0 := x.ne_zero
    have hpos : (0 : ℝ) < T.normalizedAbs (x : K.Carrier) := T.normalizedAbs_pos hx
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le,
      T.normalizedAbs_of_ne_zero hx, Real.log_zpow, fieldUnramified_apply,
      Units.val_zpow_eq_zpow_val]
    push_cast
    rw [hlogq]
    rw [show (-(T.ord (x : K.Carrier) : ℂ) * (L : ℂ)) * (-Complex.log z / L) =
        (T.ord (x : K.Carrier) : ℂ) * Complex.log z by field_simp,
      Complex.exp_int_mul, Complex.exp_log z.ne_zero]

theorem comp_C_mul_X_comp (P : ℂ[X]) (a b : ℂ) :
    (P.comp (C a * X)).comp (C b * X) = P.comp (C (a * b) * X) := by
  rw [Polynomial.comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul]

/-- Twisting both members of a supercuspidal pair by unramified characters with
values `z` and `z'` substitutes `X ↦ z z' X` in the JPSS L-polynomial. -/
theorem isSupercuspidalPairLPolynomial_unramifiedTwist {r n : ℕ}
    (ψ : NontrivialAdditiveCharacter K) (ν : LocalAdditiveHaarMeasure K)
    (hν : IsSelfDualMeasure K ψ ν)
    {π : SupercuspidalAutomorphicClass.{uK, uV} K r.succPNat}
    {τ : SupercuspidalAutomorphicClass.{uK, uV} K n.succPNat} {P : ℂ[X]}
    (h : IsSupercuspidalPairLPolynomial K ψ ν π τ P) (z z' : ℂˣ) :
    IsSupercuspidalPairLPolynomial K ψ ν (supercuspidalTwist K (fieldUnramified K z) π)
      (supercuspidalTwist K (fieldUnramified K z') τ) (P.comp (C ((z : ℂ) * z') * X)) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep π
  obtain ⟨B, rfl⟩ := Quotient.exists_rep τ
  obtain ⟨u, hu, hχ⟩ := exists_unramifiedExponent K z
  obtain ⟨u', hu', hχ'⟩ := exists_unramifiedExponent K z'
  let ν' : LocalFactor.PadicAbelian.SelfDualHaar K.canonicalTopologicalData ψ := ⟨ν, hν⟩
  have h1 := (RankinSelberg.unramifiedTwistLFactor p K ψ ν' r n A.obj.representation
    B.obj.representation u (fieldUnramified K z).toMonoidHom hχ P h).2
  have h2 := (RankinSelberg.unramifiedTwistLFactor p K ψ ν' r n
    (Langlands.twist ((fieldUnramified K z).toMonoidHom.comp GeneralLinear.determinant)
      A.obj.representation) B.obj.representation u' (fieldUnramified K z').toMonoidHom hχ' _
      h1).1
  rw [hu, hu', comp_C_mul_X_comp] at h2
  exact h2

/-- Twisting both members of a supercuspidal pair by unramified characters with
values `z` and `z'` multiplies an epsilon certificate `(c, m)` by `(z z') ^ m`,
given the JPSS unramified-twist epsilon statement. -/
theorem isSupercuspidalPairEpsilonFactor_unramifiedTwist
    (hGLε : RankinSelberg.UnramifiedTwistEpsilonStatement.{uK, uV, uV}) {r n : ℕ}
    (ψ : NontrivialAdditiveCharacter K) (ν : LocalAdditiveHaarMeasure K)
    (hν : IsSelfDualMeasure K ψ ν)
    {π : SupercuspidalAutomorphicClass.{uK, uV} K r.succPNat}
    {τ : SupercuspidalAutomorphicClass.{uK, uV} K n.succPNat} {c : ℂˣ} {m : ℤ}
    (h : IsSupercuspidalPairEpsilonFactor K ψ ν π τ (c, m)) (z z' : ℂˣ) :
    IsSupercuspidalPairEpsilonFactor K ψ ν (supercuspidalTwist K (fieldUnramified K z) π)
      (supercuspidalTwist K (fieldUnramified K z') τ) (c * (z * z') ^ m, m) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep π
  obtain ⟨B, rfl⟩ := Quotient.exists_rep τ
  obtain ⟨u, hu, hχ⟩ := exists_unramifiedExponent K z
  obtain ⟨u', hu', hχ'⟩ := exists_unramifiedExponent K z'
  let ν' : LocalFactor.PadicAbelian.SelfDualHaar K.canonicalTopologicalData ψ := ⟨ν, hν⟩
  obtain ⟨e₁, he₁m, he₁c, -, h1⟩ := hGLε p K ψ ν' r n A.obj.representation
    B.obj.representation u (fieldUnramified K z).toMonoidHom hχ (c, m) h
  obtain ⟨e₂, he₂m, he₂c, h2, -⟩ := hGLε p K ψ ν' r n
    (Langlands.twist ((fieldUnramified K z).toMonoidHom.comp GeneralLinear.determinant)
      A.obj.representation) B.obj.representation u' (fieldUnramified K z').toMonoidHom hχ' e₁ h1
  have hq : (K.canonicalTopologicalData.residueCardinality : ℂ) ≠ 0 := by
    exact_mod_cast (lt_trans Nat.zero_lt_one
      K.canonicalTopologicalData.residueCardinality_gt_one).ne'
  have he : e₂ = (c * (z * z') ^ m, m) := by
    refine Prod.ext (Units.ext ?_) (he₂m.trans he₁m)
    rw [he₂c, he₁c, he₁m]
    simp only
    rw [mul_comm (m : ℂ) u, mul_comm (m : ℂ) u', ← neg_mul, ← neg_mul,
      Complex.cpow_mul_int, Complex.cpow_mul_int, hu, hu']
    push_cast
    rw [mul_zpow]
    ring
  rw [he] at h2
  exact h2

/-- On two generators, the virtual Weil epsilon relation is the actual arithmetic one. -/
theorem LocalWeil.isArithmeticPairEpsilonFactor_of_generator
    {eC : LocalFactor.CommonClosure.ReciprocityFamily K}
    {ε : LocalFactor.NonabelianSystem.Assignment.{uK, uE} K}
    {hε : LocalFactor.NonabelianSystem.IsSystem K eC ε} {ψ : NontrivialAdditiveCharacter K}
    {a b : LocalWeil.UnitaryBasis.{uK, uW} K} {e : ℂˣ × ℤ}
    (h : LocalWeil.IsUnitaryPairEpsilonFactor K eC ε hε ψ (generator a) (generator b) e) :
    IsArithmeticPairEpsilonFactor K eC ε hε ψ (LocalWeil.unitaryBasisPairClass K a)
      (LocalWeil.unitaryBasisPairClass K b) e.1 e.2 := by
  obtain ⟨f, hf, rfl⟩ := h
  have ha : a ∈ (generator a).support := by simp [generator]
  have hb : b ∈ (generator b).support := by simp [generator]
  convert hf a ha b hb using 1 <;> simp [generator, Finsupp.prod_single_index,
    Finsupp.sum_single_index]

/-- On two generators, the virtual supercuspidal epsilon relation is the actual
basis relation. -/
theorem PadicSupercuspidal.isUnitaryBasisPairEpsilonFactor_of_generator
    {ψ : NontrivialAdditiveCharacter K} {ν : LocalAdditiveHaarMeasure K}
    {a b : PadicSupercuspidal.UnitaryBasis.{uK, uV} K} {e : ℂˣ × ℤ}
    (h : PadicSupercuspidal.IsUnitaryPairEpsilonFactor K ψ ν (generator a) (generator b) e) :
    PadicSupercuspidal.IsUnitaryBasisPairEpsilonFactor K ψ ν a b e := by
  obtain ⟨f, hf, rfl⟩ := h
  have ha : a ∈ (generator a).support := by simp [generator]
  have hb : b ∈ (generator b).support := by simp [generator]
  convert hf a ha b hb using 1
  simp [generator, Finsupp.prod_single_index, Finsupp.sum_single_index]

/-- The components of a stable decomposition in one rank. -/
theorem extensionMap_components (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    (n : ℕ+) (σ : IrreducibleWeilClass.{uK, uW} K n) :
    ∃ (z : ℂˣ) (σ₀ : IrreducibleWeilClass.{uK, uW} K n)
      (π₀ : SupercuspidalAutomorphicClass.{uK, uV} K n)
      (hσ₀ : Weil.IsUnitaryClass _ (⟨n, σ₀⟩ : LocalWeil.Basis.{uK, uW} K))
      (hπ₀ : Supercuspidal.IsUnitaryClass _ (⟨n, π₀⟩ : PadicSupercuspidal.Basis.{uK, uV} K)),
      σ = FiniteRepresentation.continuousIrreducibleTwistEquiv
        (Weil.Local.localUnramifiedCharacter K z) _ σ₀ ∧
      extensionMap K hSC n σ = supercuspidalTwist K (fieldUnramified K z) π₀ ∧
      IsStableImage.{uK, uW, uV, uE} K ⟨⟨n, σ₀⟩, hσ₀⟩ (generator ⟨⟨n, π₀⟩, hπ₀⟩) := by
  obtain ⟨z, ⟨⟨m', π₀⟩, hπ₀⟩, ⟨⟨m, σ₀⟩, hσ₀⟩, h, he₁⟩ := extensionBasis_spec K hSC ⟨n, σ⟩
  have hm : m = n := (Sigma.mk.inj h.1).1
  subst hm
  have hσ : σ = FiniteRepresentation.continuousIrreducibleTwistEquiv
      (Weil.Local.localUnramifiedCharacter K z) _ σ₀ := (eq_of_heq (Sigma.mk.inj h.1).2).symm
  have hm' : m' = m := by
    have := extensionBasis_rank K hSC ⟨m, σ⟩
    rw [he₁] at this
    exact this
  subst hm'
  have hc : extensionMap K hSC m' σ = supercuspidalTwist K (fieldUnramified K z) π₀ := by
    have h1 := (sigma_extensionMap K hSC m' σ).trans he₁
    exact eq_of_heq (Sigma.mk.inj h1).2
  exact ⟨z, σ₀, π₀, hσ₀, hπ₀, hσ, hc, h.2⟩

/-- Pair-factor compatibility of the extended stable map for a supplied
local-constant system, given the unramified-twist laws of the factors. -/
theorem extensionMap_pairFactors (hCE : CandidateExistenceStatement.{uK, uW, uV, uW, uK})
    (hSC : StableCorrespondenceStatement.{uK, uW, uV, uW})
    (hGLε : RankinSelberg.UnramifiedTwistEpsilonStatement.{uK, uV, uV})
    (hWtw : ArithmeticPairUnramifiedTwistStatement.{uK, uW})
    (eC : LocalFactor.CommonClosure.ReciprocityFamily K)
    (ε : LocalFactor.NonabelianSystem.Assignment.{uK, uW} K)
    (hε : LocalFactor.NonabelianSystem.IsSystem K eC ε) :
    SupercuspidalPairFactorCompatibility K eC ε hε (extensionMap K hSC) := by
  intro ψ r n σ τ
  obtain ⟨z, σ₀, π₀, hσ₀, hπ₀, rfl, hcσ, hst⟩ := extensionMap_components K hSC r.succPNat σ
  obtain ⟨z', τ₀, ρ₀, hτ₀, hρ₀, rfl, hcτ, hst'⟩ := extensionMap_components K hSC n.succPNat τ
  obtain ⟨W, A, Φ, hΦ, ⟨x, hx, hΦx⟩, ⟨y, hy, hΦy⟩⟩ := exists_common_candidate₂ K hCE hst hst'
  have hPF := hΦ.2.2 ψ
  refine ⟨hPF.1, fun ν hν => ?_⟩
  obtain ⟨hL, hEps⟩ := hPF.2 ν hν x y
  rw [hΦx, hΦy, hx, hy] at hL
  rw [hcσ, hcτ]
  constructor
  · obtain ⟨P, hP, hLP⟩ := (PadicSupercuspidal.isUnitaryPairLFactor_generator_iff K ψ ν _ _ _).mp hL
    rw [LocalWeil.unitaryPairLFactor_generator] at hLP
    refine ⟨P.comp (C ((z : ℂ) * z') * X),
      isSupercuspidalPairLPolynomial_unramifiedTwist K ψ ν hν hP z z', ?_⟩
    exact (hWtw p K eC ε hε ψ r n σ₀ τ₀ z z').1 P hLP
  · obtain ⟨⟨c, m⟩, hW, hG⟩ := hEps eC ε hε
    rw [hx, hy] at hW
    rw [hΦx, hΦy] at hG
    have hW' := LocalWeil.isArithmeticPairEpsilonFactor_of_generator K hW
    have hG' := PadicSupercuspidal.isUnitaryBasisPairEpsilonFactor_of_generator K hG
    refine ⟨(c * (z * z') ^ m, m),
      isSupercuspidalPairEpsilonFactor_unramifiedTwist K hGLε ψ ν hν hG' z z', ?_⟩
    exact (hWtw p K eC ε hε ψ r n σ₀ τ₀ z z').2 c m hW'

end Langlands.Henniart.Extension
