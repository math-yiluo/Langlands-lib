import Langlands.Representation.RankinSelberg.MultiplicativityStatement
import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# L-factors of pairs: supercuspidal, square-integrable and tempered representations

JPSS 1983, Section 8 (printed pages 443-452). Proposition (8.1): the L-factor of
an irreducible supercuspidal representation against a representation of
Whittaker type of smaller rank is `1`, and in equal rank it is the product of
the factors `(1 - a q^(-s))^(-1)` over the unramified twists that make the pair
contragredient. Theorem (8.2): the L-factor of a pair of quasi-square-integrable
representations `σ(π_1, …, π_m) × σ(σ_1, …, σ_n)` with `t ≤ r` is
`∏_i L(s, π_1 × σ_i)`. Statement (6) of (8.2): for square-integrable inputs the
L-factor has no pole in `Re(s) > 0`. Proposition (8.4): for representations
induced from square-integrable ones the L-factor is the product over all pairs
of blocks, and has no pole in `Re(s) > 0`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uG uX uF uV uW uV₂ uW₂

section Component

variable {G : Type uG} [Group G] {X : Type uX} {V : Type uV}
  [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

/-- `π` is a component of `ξ` in the sense of JPSS Section 8: an irreducible
subquotient of `ξ`. Some subrepresentation `U` of `ξ` has a surjective
intertwiner onto the irreducible representation `π`. -/
def IsIrreducibleComponent (ξ : Representation ℂ G X) (π : Representation ℂ G V) : Prop :=
  Representation.IsIrreducible π ∧
    ∃ U : Subrepresentation ξ, ∃ f : U.toRepresentation.IntertwiningMap π,
      Function.Surjective f.toLinearMap

end Component

/-- The blocks `π₀ ⊗ α^(m/2 - i)`, `i = 0, …, m`, of the induced representation
of JPSS (8.2)(1), printed page 444. With `M = m + 1` blocks counted from `1`,
JPSS write `π_i = π₀ ⊗ α^((M+1)/2 - i)`; the block `i` here is JPSS's `π_(i+1)`.
Here `α = |det|` is the normalized determinant absolute value. -/
def centeredSegmentBlocks {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {a : ℕ} (m : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π₀ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V) :
    Fin (m + 1) → Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V :=
  fun i => realPowerTwist (F.canonicalTopologicalData.determinantNorm (a + 1))
    ((m : ℝ) / 2 - (i : ℕ)) π₀

/-- JPSS 1983, Proposition (8.1)(i) (printed page 443). Let `π` be an
irreducible supercuspidal representation of `GL_(r+1)(F)` and `σ` a
representation of Whittaker type of `GL_(t+1)(F)` with `t < r`. Then
`L(s, π × σ) = 1`. -/
def SupercuspidalUnequalRankLFactorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
    Representation.IsIrreducible π →
    (letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal π) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ) →
    t < r → IsPadicPairLPolynomial F ψ ν.val π σ 1

/-- JPSS 1983, Proposition (8.1)(ii) (printed page 443), with the contragredient
restored on `σ` (see the Markdown). Let `π` be an irreducible supercuspidal
representation and `σ` an irreducible representation of Whittaker type, both of
`GL_(r+1)(F)`. Let `A` be the set of complex numbers `a = q^(-u)`, `u ∈ ℂ`, with
`π ⊗ α^(-u) ≅ σ̃`, where `α^(-u)(g) = |det g|^(-u)` and `σ̃` is the smooth
contragredient. Then `A` is finite and `L(s, π × σ) = ∏_(a ∈ A) (1 - a q^(-s))^(-1)`. -/
def SupercuspidalEqualRankLFactorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W),
    Representation.IsIrreducible π →
    (letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal π) →
    Representation.IsIrreducible σ →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) σ) →
    ∃ A : Finset ℂ,
      (∀ a : ℂ, a ∈ A ↔ ∃ u : ℂ,
        a = (F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-u) ∧
        ∃ χ : F.Carrierˣ →* ℂˣ,
          (∀ x : F.Carrierˣ,
            (χ x : ℂ) = ((F.canonicalTopologicalData.normalizedAbs (x : F.Carrier) : ℝ) : ℂ) ^ (-u)) ∧
          letI := F.canonicalTopologicalData.topology
          haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)
          Nonempty ((Langlands.twist (χ.comp determinant) π).Equiv (smoothContragredient σ))) ∧
      IsPadicPairLPolynomial F ψ ν.val π σ (∏ a ∈ A, (1 - C a * X))

/-- JPSS 1983, Theorem (8.2) (printed pages 444-445). Let `π₀` and `σ₀` be
irreducible supercuspidal representations of `GL_(a+1)(F)` and `GL_(b+1)(F)`.
Let `π` be an irreducible essentially square-integrable component of the
normalized induction of `(π₀ ⊗ α^(m/2), …, π₀ ⊗ α^(-m/2))` from the standard
upper parabolic of type `(a+1, …, a+1)` of `GL_(r+1)(F)`, `(m+1)(a+1) = r+1`,
and `σ` one of the induction of `(σ₀ ⊗ α^(n/2), …, σ₀ ⊗ α^(-n/2))` to
`GL_(t+1)(F)`, `(n+1)(b+1) = t+1`. If `t ≤ r`, then
`L(s, π × σ) = ∏_j L(s, (π₀ ⊗ α^(m/2)) × (σ₀ ⊗ α^(n/2 - j)))`. -/
def SquareIntegrableLFactorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (a m r b n t : ℕ) (hr : ∑ _i : Fin (m + 1), (a + 1) = r + 1)
    (ht : ∑ _j : Fin (n + 1), (b + 1) = t + 1)
    {V₀ : Type uV} [AddCommGroup V₀] [Module ℂ V₀]
    {W₀ : Type uW} [AddCommGroup W₀] [Module ℂ W₀]
    {V : Type uV₂} [AddCommGroup V] [Module ℂ V]
    {W : Type uW₂} [AddCommGroup W] [Module ℂ W]
    (π₀ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₀)
    (σ₀ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) W₀)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
    Representation.IsIrreducible π₀ →
    (letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal π₀) →
    Representation.IsIrreducible σ₀ →
    (letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal σ₀) →
    F.canonicalTopologicalData.IsEssentiallySquareIntegrable π →
    IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
        (centeredSegmentBlocks F m π₀)) π →
    F.canonicalTopologicalData.IsEssentiallySquareIntegrable σ →
    IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => b) ht)
        (centeredSegmentBlocks F n σ₀)) σ →
    t ≤ r →
    ∃ (P : ℂ[X]) (Q : Fin (n + 1) → ℂ[X]),
      IsPadicPairLPolynomial F ψ ν.val π σ P ∧
      (∀ j, IsPadicSymmetricLPolynomial F ψ ν.val
        (centeredSegmentBlocks F m π₀ 0) (centeredSegmentBlocks F n σ₀ j) (Q j)) ∧
      P = ∏ j, Q j

/-- JPSS 1983, statement (6) in the proof of Theorem (8.2) (printed page 445).
Let `π` and `σ` be irreducible square-integrable representations of
`GL_(r+1)(F)` and `GL_(t+1)(F)`, of any ranks. Then `L(s, π × σ)` has no pole
in `Re(s) > 0`: its L-polynomial `P` has no zero `z` with `‖z‖ < 1`, the image
of that half-plane under `s ↦ q^(-s)`. -/
def SquareIntegrablePoleFreeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
    Representation.IsIrreducible π → F.canonicalTopologicalData.IsSquareIntegrable π →
    Representation.IsIrreducible σ → F.canonicalTopologicalData.IsSquareIntegrable σ →
    ∃ P : ℂ[X], IsPadicSymmetricLPolynomial F ψ ν.val π σ P ∧
      ∀ z : ℂ, ‖z‖ < 1 → P.eval z ≠ 0

/-- JPSS 1983, Proposition (8.4) (printed pages 451-452). Let `π_1, …, π_k` and
`σ_1, …, σ_l` be irreducible square-integrable representations of
`GL_(m_i+1)(F)` and `GL_(n_j+1)(F)`, and let `π` and `σ` be their normalized
inductions from the standard upper block parabolics of `GL_(r+1)(F)` and
`GL_(t+1)(F)`. Then `L(s, π × σ) = ∏_(i,j) L(s, π_i × σ_j)`, and
`L(s, π × σ)` has no pole in `Re(s) > 0`. -/
def TemperedLFactorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t k l : ℕ) (m : Fin k → ℕ) (n : Fin l → ℕ)
    (hm : ∑ i, (m i + 1) = r + 1) (hn : ∑ j, (n j + 1) = t + 1)
    {V : Fin k → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {W : Fin l → Type uW} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (π : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (V i))
    (σ : ∀ j, Representation ℂ (Langlands.GeneralLinear (n j + 1) F.Carrier) (W j)),
    (∀ i, Representation.IsIrreducible (π i)) →
    (∀ i, F.canonicalTopologicalData.IsSquareIntegrable (π i)) →
    (∀ j, Representation.IsIrreducible (σ j)) →
    (∀ j, F.canonicalTopologicalData.IsSquareIntegrable (σ j)) →
    ∃ (P : ℂ[X]) (Q : Fin k → Fin l → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val
        (F.canonicalNormalizedProductInduced (succBlockShape m hm) π)
        (F.canonicalNormalizedProductInduced (succBlockShape n hn) σ) P ∧
      (∀ i j, IsPadicSymmetricLPolynomial F ψ ν.val (π i) (σ j) (Q i j)) ∧
      P = ∏ i, ∏ j, Q i j ∧
      ∀ z : ℂ, ‖z‖ < 1 → P.eval z ≠ 0

/-- The L-factor formulas of JPSS 1983, Section 8: Proposition (8.1)(i) and (ii),
Theorem (8.2), its statement (6), and Proposition (8.4). -/
def TemperedLFactorFormulasStatement : Prop :=
  SupercuspidalUnequalRankLFactorStatement.{uF, uV, uW} ∧
    SupercuspidalEqualRankLFactorStatement.{uF, uV, uW} ∧
    SquareIntegrableLFactorStatement.{uF, uV, uW, uV₂, uW₂} ∧
    SquareIntegrablePoleFreeStatement.{uF, uV, uW} ∧
    TemperedLFactorStatement.{uF, uV, uW}

end Langlands.RankinSelberg
