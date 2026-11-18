import Langlands.Representation.Archimedean.RealBlockMultiplierOperators
import Langlands.Representation.Archimedean.RealRationalCompactFamilies
import Langlands.Representation.Archimedean.RealCharacterPairReducible

/-! # Actual generic character crossings in fixed compact polynomial models -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealGenericCompactCharacter

open Langlands.LocalFactor.Archimedean RealBlockFrobeniusMap RealBlockMultiplier
  RealStandardFiltration RealCharacterPair RealCharacterPairReducible RealKTypeCount
  RealCompactPolynomialFourierRelation RealSignedTailPolynomial
  RealOrthogonalUncertainty Polynomial Complex

abbrev G3 := Langlands.GeneralLinear 3 ℝ

/-- An actual map preserving one compact degree and represented by the indicated operator. -/
structure CompactAction (N : ℕ) {ds es : List RealBlock}
    (q : KF 3 ds →ₗ[ℂ] KF 3 es) (A : Module.End ℂ (degreeLE 3 N)) : Prop where
  degree : ∀ (f : KF 3 ds), restrictLinear 3 (f : G3 → ℂ) ∈ degreeLE 3 N →
    restrictLinear 3 (q f : G3 → ℂ) ∈ degreeLE 3 N
  apply_eq : ∀ (f : KF 3 ds) (hf : restrictLinear 3 (f : G3 → ℂ) ∈ degreeLE 3 N),
    vector (q f) (degree f hf) = A (vector (f : G3 → ℂ) hf)

theorem CompactAction.comp {N : ℕ} {ds es fs : List RealBlock}
    {q : KF 3 ds →ₗ[ℂ] KF 3 es} {r : KF 3 es →ₗ[ℂ] KF 3 fs}
    {A B : Module.End ℂ (degreeLE 3 N)} (hq : CompactAction N q A)
    (hr : CompactAction N r B) : CompactAction N (r.comp q) (B * A) := by
  refine ⟨fun f hf => hr.degree (q f) (hq.degree f hf), fun f hf => ?_⟩
  change vector (r (q f)) (hr.degree (q f) (hq.degree f hf)) = _
  rw [hr.apply_eq (q f) (hq.degree f hf), hq.apply_eq f hf]
  rfl

theorem CompactAction.eq_apply {N : ℕ} {ds es : List RealBlock}
    {q r : KF 3 ds →ₗ[ℂ] KF 3 es} {A B : Module.End ℂ (degreeLE 3 N)}
    (hq : CompactAction N q A) (hr : CompactAction N r B)
    (f : KF 3 ds) (hf : restrictLinear 3 (f : G3 → ℂ) ∈ degreeLE 3 N)
    (hAB : A (vector (f : G3 → ℂ) hf) = B (vector (f : G3 → ℂ) hf)) :
    q f = r f := by
  apply restrict_injective (fun _ h => h.1 :
    realStandardModule 3 es ≤ principalSeries ℝ 3 (realPositionCharacter es))
  change restrictLinear 3 (q f : G3 → ℂ) = restrictLinear 3 (r f : G3 → ℂ)
  exact congrArg Subtype.val ((hq.apply_eq f hf).trans (hAB.trans (hr.apply_eq f hf).symm))

theorem CompactAction.operator_eq {N : ℕ} {ds es : List RealBlock}
    {q r : KF 3 ds →ₗ[ℂ] KF 3 es} {A B : Module.End ℂ (degreeLE 3 N)}
    (hq : CompactAction N q A) (hr : CompactAction N r B) (hqr : q = r)
    (f : KF 3 ds) (hf : restrictLinear 3 (f : G3 → ℂ) ∈ degreeLE 3 N) :
    A (vector (f : G3 → ℂ) hf) = B (vector (f : G3 → ℂ) hf) := by
  rw [← hq.apply_eq f hf, ← hr.apply_eq f hf]
  subst r
  rfl

theorem frob_action (N : ℕ) {ds es : List RealBlock} {p : ℕ} {ε : ℤ}
    {τ : ℂ} {μ : ℤ → ℂ} (hdata : IsBlockFrobData 3 ds es p ε τ μ) :
    CompactAction N (blockFrobMap hdata)
      (spectralMultiplier (proj N hdata.lt) (Finset.Icc (-(N : ℤ)) N) μ) := by
  refine ⟨frob_mem_degree hdata, fun f hf => ?_⟩
  apply Subtype.ext
  exact frob_restrict_eq_spectral hdata f hf

/-- At integral generic parity, the inverse multiplier is a normalized polynomial operator. -/
theorem inverse_integral_action (N : ℕ) {ds es : List RealBlock} {p ℓ : ℕ}
    {ε : ℤ} {τ : ℂ} (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - ε))
    (hdata : IsBlockFrobData 3 ds es p ε τ (fun j => (genericMultiplier (ℓ : ℂ) ε j)⁻¹)) :
    CompactAction N (blockFrobMap hdata)
      (((RealTailMultiplierPolynomial.tailPolynomial ℓ).eval (ε : ℂ))⁻¹ •
        aeval (-I • gen N hdata.lt) (RealTailMultiplierPolynomial.tailPolynomial ℓ)) := by
  refine ⟨frob_mem_degree hdata, fun f hf => ?_⟩
  have hcoef : ∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 p j (blockFrobMap hdata f) x =
        ((RealTailMultiplierPolynomial.tailPolynomial ℓ).eval (ε : ℂ))⁻¹ *
          (RealTailMultiplierPolynomial.tailPolynomial ℓ).eval (j : ℂ) *
            blockFourierCoefficient 3 p j f x := by
    intro j x hx
    rw [blockFourierCoefficient_blockFrobMap hdata f hx]
    by_cases hj : Even (j - ε)
    · rw [RealIntegralGenericPolynomial.genericMultiplier_eq hℓ hε hpar hj]
      simp only [div_eq_mul_inv, mul_inv, inv_inv]
    · rw [RealBlockJacquet.blockFourierCoefficient_eq_zero_of_not_even
        hdata.lt hdata.par f hj x]
      ring
  have hop := (relation_iff hdata.lt (blockFrobMap hdata f) f
    (frob_mem_degree hdata f hf) hf 1
    (C (((RealTailMultiplierPolynomial.tailPolynomial ℓ).eval (ε : ℂ))⁻¹) *
      RealTailMultiplierPolynomial.tailPolynomial ℓ)).mp (by
        simpa only [eval_one, one_mul, eval_mul, eval_C] using hcoef)
  simpa only [map_one, Module.End.one_apply, map_mul, aeval_C,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, LinearMap.smul_apply] using hop

section Crossing

variable {n : ℕ} {pre post : List RealBlock} {c d : RealCharacterData}

theorem forward_data
    (hn : realRank (pre ++ .character c :: .character d :: post) = n) (ν : ℂ) :
    IsBlockFrobData n (pre ++ .character c :: .character d :: post)
      (pre ++ .character d :: .character c :: post) (realRank pre) (pairParity c d)
      ((-1 : ℂ) ^ (pairParity c d).natAbs) (genericMultiplier ν (pairParity c d)) :=
  by
    simpa only [sigma0, RealInducedSwapGeneric.pairParity_comm d c] using
      (RealBlockMultiplierOperators.parameterData pre post c d ν hn)

theorem inverse_data
    (hn : realRank (pre ++ .character c :: .character d :: post) = n) (ν : ℂ) :
    IsBlockFrobData n (pre ++ .character d :: .character c :: post)
      (pre ++ .character c :: .character d :: post) (realRank pre) (pairParity c d)
      (((-1 : ℂ) ^ (pairParity c d).natAbs)⁻¹)
      (fun j => (genericMultiplier ν (pairParity c d) j)⁻¹) := by
  have hn' : realRank (pre ++ .character d :: .character c :: post) = n := by
    simpa [dc] using realRank_dc_mid hn
  have hh := data_unswap (c := d) (d := c) (pre := pre) (post := post) hn'
    (isSymmetric_genericMultiplier ν (pairParity_eq d c))
  simpa only [dc, sigma0, RealInducedSwapGeneric.pairParity_comm d c, List.append_assoc, List.cons_append,
    List.nil_append] using hh

def crossing
    (hn : realRank (pre ++ .character c :: .character d :: post) = n) (ν : ℂ) :
    KF n (pre ++ .character c :: .character d :: post) →ₗ[ℂ]
      KF n (pre ++ .character d :: .character c :: post) :=
  blockFrobMap (forward_data hn ν)

def inverse
    (hn : realRank (pre ++ .character c :: .character d :: post) = n) (ν : ℂ) :
    KF n (pre ++ .character d :: .character c :: post) →ₗ[ℂ]
      KF n (pre ++ .character c :: .character d :: post) :=
  blockFrobMap (inverse_data hn ν)

theorem inverse_crossing
    (hn : realRank (pre ++ .character c :: .character d :: post) = n) {ν : ℂ}
    (hν : 0 < ν.re) (hne : ∀ m : ℕ, ν ≠ (pairParity c d : ℂ) + 2 * m + 1)
    (f : KF n (pre ++ .character c :: .character d :: post)) :
    inverse hn ν (crossing hn ν f) = f := by
  apply blockFrobMap_blockFrobMap_eq (forward_data hn ν) (inverse_data hn ν) f
  intro j _ hbad
  exact (hbad (inv_mul_cancel₀
    (genericMultiplier_ne_zero hν (pairParity_eq c d) hne j))).elim

theorem crossing_inverse
    (hn : realRank (pre ++ .character c :: .character d :: post) = n) {ν : ℂ}
    (hν : 0 < ν.re) (hne : ∀ m : ℕ, ν ≠ (pairParity c d : ℂ) + 2 * m + 1)
    (f : KF n (pre ++ .character d :: .character c :: post)) :
    crossing hn ν (inverse hn ν f) = f := by
  apply blockFrobMap_blockFrobMap_eq (inverse_data hn ν) (forward_data hn ν) f
  intro j _ hbad
  exact (hbad (mul_inv_cancel₀
    (genericMultiplier_ne_zero hν (pairParity_eq c d) hne j))).elim

theorem integral_nonresonant {ℓ : ℕ} {ε : ℤ} (hpar : Even ((ℓ : ℤ) - ε)) :
    ∀ m : ℕ, (ℓ : ℂ) ≠ (ε : ℂ) + 2 * m + 1 := by
  intro m h
  have hh : (ℓ : ℤ) = ε + 2 * m + 1 := by exact_mod_cast h
  rw [Int.even_iff] at hpar
  omega

end Crossing

section Words

def source (a b c : RealCharacterData) : List RealBlock :=
  [.character a, .character b, .character c]

def swap0 (a b c : RealCharacterData) (ν : ℂ) :
    KF 3 (source a b c) →ₗ[ℂ] KF 3 (source b a c) :=
  crossing (n := 3) (pre := []) (post := [.character c]) (c := a) (d := b) rfl ν

def swap1 (a b c : RealCharacterData) (ν : ℂ) :
    KF 3 (source a b c) →ₗ[ℂ] KF 3 (source a c b) :=
  crossing (n := 3) (pre := [.character a]) (post := []) (c := b) (d := c) rfl ν

def leftWord (a b c : RealCharacterData) (z : RealRationalCompactFamilies.Parameters) :
    KF 3 (source a b c) →ₗ[ℂ] KF 3 (source c b a) :=
  ((swap0 b c a (z 1)).comp (swap1 b a c (z 0 + z 1))).comp (swap0 a b c (z 0))

def rightWord (a b c : RealCharacterData) (z : RealRationalCompactFamilies.Parameters) :
    KF 3 (source a b c) →ₗ[ℂ] KF 3 (source c b a) :=
  ((swap1 c a b (z 0)).comp (swap0 a c b (z 0 + z 1))).comp (swap1 a b c (z 1))

theorem leftWord_action (N : ℕ) (a b c : RealCharacterData) (z : RealRationalCompactFamilies.Parameters) :
    CompactAction N (leftWord a b c z)
      (RealRationalCompactFamilies.leftWord N (pairParity a b) (pairParity b c) (pairParity a c) z) := by
  have hh := CompactAction.comp
    (frob_action N (forward_data (n := 3) (pre := []) (post := [.character c])
      (c := a) (d := b) rfl (z 0)))
    (CompactAction.comp
      (frob_action N (forward_data (n := 3) (pre := [.character b]) (post := [])
        (c := a) (d := c) rfl (z 0 + z 1)))
      (frob_action N (forward_data (n := 3) (pre := []) (post := [.character a])
        (c := b) (d := c) rfl (z 1))))
  simpa only [leftWord, swap0, swap1, crossing, RealRationalCompactFamilies.leftWord, RealRationalCompactFamilies.compactGeneric,
    MvPolynomial.eval_X, map_add] using hh

theorem rightWord_action (N : ℕ) (a b c : RealCharacterData) (z : RealRationalCompactFamilies.Parameters) :
    CompactAction N (rightWord a b c z)
      (RealRationalCompactFamilies.rightWord N (pairParity a b) (pairParity b c) (pairParity a c) z) := by
  have hh := CompactAction.comp
    (frob_action N (forward_data (n := 3) (pre := [.character a]) (post := [])
      (c := b) (d := c) rfl (z 1)))
    (CompactAction.comp
      (frob_action N (forward_data (n := 3) (pre := []) (post := [.character b])
        (c := a) (d := c) rfl (z 0 + z 1)))
      (frob_action N (forward_data (n := 3) (pre := [.character c]) (post := [])
        (c := a) (d := b) rfl (z 0))))
  simpa only [rightWord, swap0, swap1, crossing, RealRationalCompactFamilies.rightWord, RealRationalCompactFamilies.compactGeneric,
    MvPolynomial.eval_X, map_add] using hh

def sourceVectors (N : ℕ) (a b c : RealCharacterData) : Set (degreeLE 3 N) :=
  {v | ∃ (f : KF 3 (source a b c))
    (hf : restrictLinear 3 (f : G3 → ℂ) ∈ degreeLE 3 N), vector (f : G3 → ℂ) hf = v}

/-- An actual fixed-character generic grid identity extends throughout the positive half planes. -/
theorem braid_of_grid (a b c : RealCharacterData)
    (hgrid : ∀ z ∈ Set.pi Set.univ (RealRationalCompactFamilies.grid (pairParity a b) (pairParity b c)),
      leftWord a b c z = rightWord a b c z) (z : RealRationalCompactFamilies.Parameters)
    (hz0 : 0 < (z 0).re) (hz1 : 0 < (z 1).re) :
    leftWord a b c z = rightWord a b c z := by
  have hε : 0 ≤ pairParity a b := by rcases pairParity_eq a b with h | h <;> omega
  have hη : 0 ≤ pairParity b c := by rcases pairParity_eq b c with h | h <;> omega
  have hκ : 0 ≤ pairParity a c := by rcases pairParity_eq a c with h | h <;> omega
  apply LinearMap.ext
  intro f
  obtain ⟨N, hf⟩ :=
    RealPolynomialFourierPropagation.exists_degreeLE (RealBlockJacquet.continuous_coe f) f.2.2
  have hcompactgrid : ∀ x ∈ Set.pi Set.univ (RealRationalCompactFamilies.grid (pairParity a b) (pairParity b c)),
      ∀ v ∈ sourceVectors N a b c,
      RealRationalCompactFamilies.leftWord N (pairParity a b) (pairParity b c) (pairParity a c) x v =
        RealRationalCompactFamilies.rightWord N (pairParity a b) (pairParity b c) (pairParity a c) x v := by
    intro x hx v hv
    obtain ⟨g, hg, rfl⟩ := hv
    exact CompactAction.operator_eq (leftWord_action N a b c x) (rightWord_action N a b c x)
      (hgrid x hx) g hg
  apply CompactAction.eq_apply (leftWord_action N a b c z) (rightWord_action N a b c z) f hf
  exact RealRationalCompactFamilies.threeCrossing_eq_of_grid N hε hη hκ (sourceVectors N a b c) hcompactgrid z
    (RealRationalCompactFamilies.wordDenominator_ne_zero N hε hη hκ hz0 hz1)
    (vector (f : G3 → ℂ) hf) ⟨f, hf, rfl⟩

end Words

end Langlands.Archimedean.RealGenericCompactCharacter

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealCharacterPair RealGenericCompactCharacter

/-- The actual fixed-character generic braid extends from its positive integral parity grid. -/
def RealGenericCompactCharacterStatement : Prop :=
  ∀ (a b c : RealCharacterData),
    (∀ z ∈ Set.pi Set.univ
      (RealRationalCompactFamilies.grid (pairParity a b) (pairParity b c)),
      leftWord a b c z = rightWord a b c z) →
    ∀ z : RealRationalCompactFamilies.Parameters,
      0 < (z 0).re → 0 < (z 1).re → leftWord a b c z = rightWord a b c z

theorem realGenericCompactCharacter : RealGenericCompactCharacterStatement :=
  fun a b c hgrid z hz0 hz1 => braid_of_grid a b c hgrid z hz0 hz1

end Langlands.Archimedean
