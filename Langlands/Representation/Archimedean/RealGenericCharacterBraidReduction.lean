import Langlands.Representation.Archimedean.RealGenericCompactCharacter
import Langlands.Representation.Archimedean.RealDifferentialCharacterBraid

/-! # From a full compact polynomial braid to actual generic character words -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealGenericCharacterBraidReduction

open Langlands.LocalFactor.Archimedean RealStandardFiltration RealCharacterPair
  RealBlockFrobeniusMap RealGenericCompactCharacter RealKTypeCount
  RealCompactPolynomialFourierRelation RealOrthogonalUncertainty
  RealTailMultiplierPolynomial Polynomial Complex

def inversePolynomial (N : ℕ) {p : ℕ} (hp : p + 1 < 3) (ℓ : ℕ) (ε : ℤ) :
    Module.End ℂ (degreeLE 3 N) :=
  ((tailPolynomial ℓ).eval (ε : ℂ))⁻¹ • aeval (-I • gen N hp) (tailPolynomial ℓ)

def PolynomialBraid (N n m : ℕ) : Prop :=
  aeval (-I • gen N (p := 0) (by decide)) (tailPolynomial n) *
      aeval (-I • gen N (p := 1) (by decide)) (tailPolynomial (n + m)) *
      aeval (-I • gen N (p := 0) (by decide)) (tailPolynomial m) =
    aeval (-I • gen N (p := 1) (by decide)) (tailPolynomial m) *
      aeval (-I • gen N (p := 0) (by decide)) (tailPolynomial (n + m)) *
      aeval (-I • gen N (p := 1) (by decide)) (tailPolynomial n)

structure IntegralParameters (a b c : RealCharacterData) (n m : ℕ) : Prop where
  pos0 : 0 < n
  pos1 : 0 < m
  parity0 : Even ((n : ℤ) - pairParity a b)
  parity1 : Even ((m : ℤ) - pairParity b c)

theorem middle_parity {a b c : RealCharacterData} {n m : ℕ}
    (p : IntegralParameters a b c n m) :
    Even (((n + m : ℕ) : ℤ) - pairParity a c) := by
  have h0 := p.parity0
  have h1 := p.parity1
  rw [Int.even_iff] at h0 h1 ⊢
  simp only [pairParity] at h0 h1 ⊢
  omega

def inverse0 (a b c : RealCharacterData) (ν : ℂ) :
    KF 3 (source b a c) →ₗ[ℂ] KF 3 (source a b c) :=
  inverse (n := 3) (pre := []) (post := [.character c]) (c := a) (d := b) rfl ν

def inverse1 (a b c : RealCharacterData) (ν : ℂ) :
    KF 3 (source a c b) →ₗ[ℂ] KF 3 (source a b c) :=
  inverse (n := 3) (pre := [.character a]) (post := []) (c := b) (d := c) rfl ν

theorem inverse0_action (N : ℕ) (a b c : RealCharacterData) {ℓ : ℕ}
    (hℓ : 0 < ℓ) (hpar : Even ((ℓ : ℤ) - pairParity a b)) :
    CompactAction N (inverse0 a b c (ℓ : ℂ))
      (inversePolynomial N (p := 0) (by decide) ℓ (pairParity a b)) :=
  inverse_integral_action N hℓ (pairParity_eq a b) hpar
    (inverse_data (n := 3) (pre := []) (post := [.character c]) (c := a) (d := b) rfl (ℓ : ℂ))

theorem inverse1_action (N : ℕ) (a b c : RealCharacterData) {ℓ : ℕ}
    (hℓ : 0 < ℓ) (hpar : Even ((ℓ : ℤ) - pairParity b c)) :
    CompactAction N (inverse1 a b c (ℓ : ℂ))
      (inversePolynomial N (p := 1) (by decide) ℓ (pairParity b c)) :=
  inverse_integral_action N hℓ (pairParity_eq b c) hpar
    (inverse_data (n := 3) (pre := [.character a]) (post := []) (c := b) (d := c) rfl (ℓ : ℂ))

theorem inverse0_swap0 (a b c : RealCharacterData) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hpar : Even ((ℓ : ℤ) - pairParity a b)) (f : KF 3 (source a b c)) :
    inverse0 a b c (ℓ : ℂ) (swap0 a b c (ℓ : ℂ) f) = f :=
  inverse_crossing (n := 3) (pre := []) (post := [.character c]) (c := a) (d := b) rfl
    (by simpa using (show (0 : ℝ) < ℓ by exact_mod_cast hℓ)) (integral_nonresonant hpar) f

theorem inverse1_swap1 (a b c : RealCharacterData) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hpar : Even ((ℓ : ℤ) - pairParity b c)) (f : KF 3 (source a b c)) :
    inverse1 a b c (ℓ : ℂ) (swap1 a b c (ℓ : ℂ) f) = f :=
  inverse_crossing (n := 3) (pre := [.character a]) (post := []) (c := b) (d := c) rfl
    (by simpa using (show (0 : ℝ) < ℓ by exact_mod_cast hℓ)) (integral_nonresonant hpar) f

theorem swap0_inverse0 (a b c : RealCharacterData) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hpar : Even ((ℓ : ℤ) - pairParity a b)) (f : KF 3 (source b a c)) :
    swap0 a b c (ℓ : ℂ) (inverse0 a b c (ℓ : ℂ) f) = f :=
  crossing_inverse (n := 3) (pre := []) (post := [.character c]) (c := a) (d := b) rfl
    (by simpa using (show (0 : ℝ) < ℓ by exact_mod_cast hℓ)) (integral_nonresonant hpar) f

theorem swap1_inverse1 (a b c : RealCharacterData) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hpar : Even ((ℓ : ℤ) - pairParity b c)) (f : KF 3 (source a c b)) :
    swap1 a b c (ℓ : ℂ) (inverse1 a b c (ℓ : ℂ) f) = f :=
  crossing_inverse (n := 3) (pre := [.character a]) (post := []) (c := b) (d := c) rfl
    (by simpa using (show (0 : ℝ) < ℓ by exact_mod_cast hℓ)) (integral_nonresonant hpar) f

def inverseLeftWord (a b c : RealCharacterData) (n m : ℕ) :
    KF 3 (source c b a) →ₗ[ℂ] KF 3 (source a b c) :=
  ((inverse0 a b c (n : ℂ)).comp (inverse1 b a c ((n + m : ℕ) : ℂ))).comp
    (inverse0 b c a (m : ℂ))

def inverseRightWord (a b c : RealCharacterData) (n m : ℕ) :
    KF 3 (source c b a) →ₗ[ℂ] KF 3 (source a b c) :=
  ((inverse1 a b c (m : ℂ)).comp (inverse0 a c b ((n + m : ℕ) : ℂ))).comp
    (inverse1 c a b (n : ℂ))

def leftOperator (N : ℕ) (a b c : RealCharacterData) (n m : ℕ) :
    Module.End ℂ (degreeLE 3 N) :=
  inversePolynomial N (p := 0) (by decide) n (pairParity a b) *
    inversePolynomial N (p := 1) (by decide) (n + m) (pairParity a c) *
    inversePolynomial N (p := 0) (by decide) m (pairParity b c)

def rightOperator (N : ℕ) (a b c : RealCharacterData) (n m : ℕ) :
    Module.End ℂ (degreeLE 3 N) :=
  inversePolynomial N (p := 1) (by decide) m (pairParity b c) *
    inversePolynomial N (p := 0) (by decide) (n + m) (pairParity a c) *
    inversePolynomial N (p := 1) (by decide) n (pairParity a b)

theorem inverseLeftWord_action (N : ℕ) {a b c : RealCharacterData} {n m : ℕ}
    (p : IntegralParameters a b c n m) :
    CompactAction N (inverseLeftWord a b c n m) (leftOperator N a b c n m) :=
  CompactAction.comp (inverse0_action N b c a p.pos1 p.parity1)
    (CompactAction.comp (inverse1_action N b a c (by have := p.pos0; omega) (middle_parity p))
      (inverse0_action N a b c p.pos0 p.parity0))

theorem inverseRightWord_action (N : ℕ) {a b c : RealCharacterData} {n m : ℕ}
    (p : IntegralParameters a b c n m) :
    CompactAction N (inverseRightWord a b c n m) (rightOperator N a b c n m) :=
  CompactAction.comp (inverse1_action N c a b p.pos0 p.parity0)
    (CompactAction.comp (inverse0_action N a c b (by have := p.pos0; omega) (middle_parity p))
      (inverse1_action N a b c p.pos1 p.parity1))

theorem operators_eq (N : ℕ) (a b c : RealCharacterData) (n m : ℕ)
    (hB : PolynomialBraid N n m) : leftOperator N a b c n m = rightOperator N a b c n m := by
  unfold leftOperator rightOperator inversePolynomial
  simp only [smul_mul_smul]
  rw [hB]
  congr 1
  ring

theorem inverseWords_eq {a b c : RealCharacterData} {n m : ℕ}
    (p : IntegralParameters a b c n m) (hB : ∀ N, PolynomialBraid N n m) :
    inverseLeftWord a b c n m = inverseRightWord a b c n m := by
  apply LinearMap.ext
  intro f
  obtain ⟨N, hf⟩ :=
    RealPolynomialFourierPropagation.exists_degreeLE (RealBlockJacquet.continuous_coe f) f.2.2
  apply CompactAction.eq_apply (inverseLeftWord_action N p) (inverseRightWord_action N p) f hf
  exact LinearMap.congr_fun (operators_eq N a b c n m (hB N)) _

theorem inverseLeftWord_leftWord {a b c : RealCharacterData} {n m : ℕ}
    (p : IntegralParameters a b c n m) (f : KF 3 (source a b c)) :
    inverseLeftWord a b c n m (leftWord a b c ![(n : ℂ), (m : ℂ)] f) = f := by
  simp only [inverseLeftWord, leftWord, LinearMap.comp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Nat.cast_add]
  rw [inverse0_swap0 b c a p.pos1 p.parity1]
  rw [← Nat.cast_add]
  rw [inverse1_swap1 b a c (by have := p.pos0; omega) (middle_parity p),
    inverse0_swap0 a b c p.pos0 p.parity0]

theorem rightWord_inverseRightWord {a b c : RealCharacterData} {n m : ℕ}
    (p : IntegralParameters a b c n m) (f : KF 3 (source c b a)) :
    rightWord a b c ![(n : ℂ), (m : ℂ)] (inverseRightWord a b c n m f) = f := by
  simp only [inverseRightWord, rightWord, LinearMap.comp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Nat.cast_add]
  rw [swap1_inverse1 a b c p.pos1 p.parity1]
  rw [← Nat.cast_add]
  rw [swap0_inverse0 a c b (by have := p.pos0; omega) (middle_parity p),
    swap1_inverse1 c a b p.pos0 p.parity0]

/-- The full polynomial braid is used only through the displayed premise. -/
theorem integral_braid {a b c : RealCharacterData} {n m : ℕ}
    (p : IntegralParameters a b c n m) (hB : ∀ N, PolynomialBraid N n m) :
    leftWord a b c ![(n : ℂ), (m : ℂ)] = rightWord a b c ![(n : ℂ), (m : ℂ)] := by
  have hi := inverseWords_eq p hB
  apply LinearMap.ext
  intro f
  calc
    leftWord a b c ![(n : ℂ), (m : ℂ)] f =
        rightWord a b c ![(n : ℂ), (m : ℂ)]
          (inverseRightWord a b c n m (leftWord a b c ![(n : ℂ), (m : ℂ)] f)) :=
      (rightWord_inverseRightWord p _).symm
    _ = rightWord a b c ![(n : ℂ), (m : ℂ)] f := by
      rw [← hi, inverseLeftWord_leftWord p f]

theorem polynomial_braid_small (N n m : ℕ)
    (hsmall : (n = 1 ∨ n = 2) ∨ (m = 1 ∨ m = 2)) : PolynomialBraid N n m := by
  have hp0 : 0 + 1 < 3 := by decide
  have hp1 : 1 + 1 < 3 := by decide
  obtain ⟨z, hXY, hYZ, hZX⟩ := exists_relations N (Or.inl ⟨rfl, rfl⟩) hp0 hp1
  have hZY : z * gen N hp1 - gen N hp1 * z = -gen N hp0 := by
    apply LinearMap.ext
    intro w
    have hh := LinearMap.congr_fun hYZ w
    change gen N hp1 (z w) - z (gen N hp1 w) = gen N hp0 w at hh
    change z (gen N hp1 w) - gen N hp1 (z w) = -(gen N hp0 w)
    rw [← hh]
    abel
  have hh := RealDifferentialCharacterBraid.normalized_braid_small
    (X := gen N hp0) (Y := gen N hp1) (Z := z) hXY hZX hZY m n
      (hsmall.elim Or.inr Or.inl)
  simpa only [PolynomialBraid, Nat.add_comm] using hh

theorem integral_braid_small {a b c : RealCharacterData} {n m : ℕ}
    (p : IntegralParameters a b c n m)
    (hsmall : (n = 1 ∨ n = 2) ∨ (m = 1 ∨ m = 2)) :
    leftWord a b c ![(n : ℂ), (m : ℂ)] = rightWord a b c ![(n : ℂ), (m : ℂ)] :=
  integral_braid p (fun N => polynomial_braid_small N n m hsmall)

theorem grid_braid_of_polynomial
    (hB : ∀ N n m, PolynomialBraid N n m) (a b c : RealCharacterData) :
    ∀ z ∈ Set.pi Set.univ
      (RealRationalCompactFamilies.grid (pairParity a b) (pairParity b c)),
      leftWord a b c z = rightWord a b c z := by
  intro z hz
  have h0 : z 0 ∈ RealRationalCompactFamilies.positiveGrid (pairParity a b) :=
    hz 0 (Set.mem_univ _)
  have h1 : z 1 ∈ RealRationalCompactFamilies.positiveGrid (pairParity b c) :=
    hz 1 (Set.mem_univ _)
  obtain ⟨r, hr⟩ := h0
  obtain ⟨s, hs⟩ := h1
  let n : ℕ := (a.parity.val + b.parity.val) % 2 + 2 * (r + 1)
  let m : ℕ := (b.parity.val + c.parity.val) % 2 + 2 * (s + 1)
  have hcast0 : (n : ℂ) = z 0 := by
    rw [← hr]
    simp only [n, pairParity, Int.cast_natCast, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
  have hcast1 : (m : ℂ) = z 1 := by
    rw [← hs]
    simp only [m, pairParity, Int.cast_natCast, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
  have p : IntegralParameters a b c n m := by
    constructor
    · dsimp [n]; omega
    · dsimp [m]; omega
    · rw [Int.even_iff]
      dsimp [n, pairParity]
      omega
    · rw [Int.even_iff]
      dsimp [m, pairParity]
      omega
  have hvec : ![(n : ℂ), (m : ℂ)] = z := by
    funext i
    fin_cases i
    · exact hcast0
    · exact hcast1
  rw [← hvec]
  exact integral_braid p (fun N => hB N n m)

theorem generic_braid_of_polynomial
    (hB : ∀ N n m, PolynomialBraid N n m) (a b c : RealCharacterData)
    (z : RealRationalCompactFamilies.Parameters) (hz0 : 0 < (z 0).re)
    (hz1 : 0 < (z 1).re) :
    leftWord a b c z = rightWord a b c z :=
  braid_of_grid a b c (grid_braid_of_polynomial hB a b c) z hz0 hz1

end Langlands.Archimedean.RealGenericCharacterBraidReduction

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealGenericCompactCharacter
  RealGenericCharacterBraidReduction

/-- Actual small integral generic braids and the explicit remaining full-polynomial premise. -/
def RealGenericCharacterBraidReductionStatement : Prop :=
  (∀ (a b c : RealCharacterData) (n m : ℕ), IntegralParameters a b c n m →
    ((n = 1 ∨ n = 2) ∨ (m = 1 ∨ m = 2)) →
      leftWord a b c ![(n : ℂ), (m : ℂ)] = rightWord a b c ![(n : ℂ), (m : ℂ)]) ∧
  ((∀ N n m, PolynomialBraid N n m) →
    ∀ (a b c : RealCharacterData) (z : RealRationalCompactFamilies.Parameters),
      0 < (z 0).re → 0 < (z 1).re → leftWord a b c z = rightWord a b c z)

theorem realGenericCharacterBraidReduction : RealGenericCharacterBraidReductionStatement :=
  ⟨fun _ _ _ _ _ p hs => integral_braid_small p hs,
    fun hB a b c z hz0 hz1 => generic_braid_of_polynomial hB a b c z hz0 hz1⟩

end Langlands.Archimedean
