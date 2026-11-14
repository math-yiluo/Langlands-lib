import Langlands.Representation.Archimedean.RealGenericParameterReduction
import Langlands.Representation.Unitary.Basic
import Langlands.LocalFactor.ArchimedeanPairFactor

/-!
# Archimedean pair `L`-factors of unitary generic modules on `Re(s) ≥ 1`

The Archimedean half of Getz–Hahn 2024, Theorem 11.5.2: for irreducible admissible generic
unitary representations `π` of `GL_n(F)` and `π'` of `GL_m(F)`, `F = ℝ` or `ℂ`, the pair
`L`-function `L(s, π × π')` is holomorphic and nonzero for `Re(s) ≥ 1`. Here `L(s, π × π')`
is the Library's pair `L`-factor `realPairLFactor ds ds'` (resp. `complexPairLFactor ds ds'`)
of the standard parameters `ds`, `ds'` of `π`, `π'`, a reciprocal `1 / P(s)` of an entire
function `P`; the statement says `P(s) ≠ 0` on `Re(s) ≥ 1`.

The file defines unitarizability of `(𝔤, K)`-modules (Knapp–Vogan 1995, (0.5): a positive
definite Hermitian form invariant under `K` and skew under the real Lie algebra `𝔤₀`) and
states:

* the exponent bound `|Re t| < 1/2` for every block of the standard parameter of an
  irreducible admissible generic unitarizable module (from Badulescu–Renard 2010,
  Theorem 8.2, the classification of generic unitary representations of `GL_n(ℝ)`);
* the regularity of a pair `L`-factor at every `s` with `Re(s + t + t') > 0` for all pairs
  of block exponents `t`, `t'` (an elementary fact about the poles of `Γ`);
* the Archimedean case of Getz–Hahn, Theorem 11.5.2, and its reduction to the two previous
  statements.

These are statements, not proofs.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

universe uV uW

/-! ## Unitarizable `(𝔤, K)`-modules -/

section Unitarizable

variable (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A `(𝔤𝔩_n(ℝ), O(n))`-module `(ρ, π)` is unitarizable (infinitesimally unitary,
Knapp–Vogan 1995, (0.5)) when it admits a positive definite Hermitian form `⟨·, ·⟩` that is
invariant under `ρ(k)` for every `k ∈ O(n)` and skew under every real matrix
`X ∈ 𝔤𝔩_n(ℝ)`: `⟨π(1 ⊗ X) v, w⟩ + ⟨v, π(1 ⊗ X) w⟩ = 0`. -/
def IsRealUnitarizableGKModule (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  ∃ b : Langlands.InvariantPositiveForm ρ, ∀ (X : Matrix (Fin n) (Fin n) ℝ) (v w : V),
    b.inner (π (1 ⊗ₜ X) v) w + b.inner v (π (1 ⊗ₜ X) w) = 0

/-- A `(𝔤𝔩_n(ℂ), U(n))`-module `(ρ, π)` is unitarizable (infinitesimally unitary,
Knapp–Vogan 1995, (0.5)) when it admits a positive definite Hermitian form `⟨·, ·⟩` that is
invariant under `ρ(k)` for every `k ∈ U(n)` and skew under every matrix `X ∈ 𝔤𝔩_n(ℂ)`,
regarded as an element of the real Lie algebra: `⟨π(1 ⊗ X) v, w⟩ + ⟨v, π(1 ⊗ X) w⟩ = 0`. -/
def IsComplexUnitarizableGKModule (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  ∃ b : Langlands.InvariantPositiveForm ρ, ∀ (X : Matrix (Fin n) (Fin n) ℂ) (v w : V),
    b.inner (π (1 ⊗ₜ X) v) w + b.inner v (π (1 ⊗ₜ X) w) = 0

end Unitarizable

/-! ## Exponent bounds for unitary generic modules -/

/-- Every block of a standard parameter of an irreducible admissible generic unitarizable
`(𝔤𝔩_n(ℝ), O(n))`-module has exponent of real part in `(-1/2, 1/2)`. This is the bound
read off from the classification of generic irreducible unitary representations of
`GL_n(ℝ)` (Badulescu–Renard 2010, Theorem 8.2); see the Markdown. -/
def RealUnitaryGenericExponentBoundStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V) (ds : List RealBlock),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      IsRealGenericGKModule n π → IsRealUnitarizableGKModule n ρ π →
        HasRealStandardParameter n ρ π ds → ∀ x ∈ ds, |realBlockExponent x| < 1 / 2

/-- Every character of a standard parameter of an irreducible admissible generic
unitarizable `(𝔤𝔩_n(ℂ), U(n))`-module has exponent of real part in `(-1/2, 1/2)`, for the
Library's normalization `(z/|z|)^m |z|^(2t)` of characters of `ℂˣ`. This is the
`GL_n(ℂ)` analogue of Badulescu–Renard 2010, Theorem 8.2; see the Markdown. -/
def ComplexUnitaryGenericExponentBoundStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ds : List ComplexCharacterData),
    IsComplexGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      IsComplexGenericGKModule n π → IsComplexUnitarizableGKModule n ρ π →
        HasComplexStandardParameter n ρ π ds → ∀ x ∈ ds, |x.exponent.re| < 1 / 2

/-! ## Regularity of pair `L`-factors to the right of the exponents -/

/-- The real pair `L`-factor `L(s, ds × ds')` has no pole at `s` when
`Re(s) + Re(t) + Re(t') > 0` for every block exponent `t` of `ds` and `t'` of `ds'`; that is,
its entire denominator does not vanish at `s`. -/
def RealPairLFactorRightHalfPlaneRegularityStatement : Prop :=
  ∀ (ds ds' : List RealBlock) (s : ℂ),
    (∀ x ∈ ds, ∀ y ∈ ds', 0 < s.re + realBlockExponent x + realBlockExponent y) →
      (realPairLFactor ds ds').denominator s ≠ 0

/-- The complex pair `L`-factor `L(s, ds × ds')` has no pole at `s` when
`Re(s) + Re(t) + Re(t') > 0` for every exponent `t` of `ds` and `t'` of `ds'`; that is, its
entire denominator does not vanish at `s`. -/
def ComplexPairLFactorRightHalfPlaneRegularityStatement : Prop :=
  ∀ (ds ds' : List ComplexCharacterData) (s : ℂ),
    (∀ x ∈ ds, ∀ y ∈ ds', 0 < s.re + x.exponent.re + y.exponent.re) →
      (complexPairLFactor ds ds').denominator s ≠ 0

/-! ## Getz–Hahn, Theorem 11.5.2, Archimedean case -/

/-- Getz–Hahn 2024, Theorem 11.5.2, case `F = ℝ` (printed page 305): if `(ρ, π)` and
`(ρ', π')` are irreducible admissible generic unitarizable `(𝔤𝔩_n(ℝ), O(n))`- and
`(𝔤𝔩_m(ℝ), O(m))`-modules with standard parameters `ds` and `ds'`, then the pair `L`-factor
`L(s, π × π') = 1 / P(s)`, `P = (realPairLFactor ds ds').denominator`, is holomorphic and
nonzero for `Re(s) ≥ 1`: `P(s) ≠ 0` there. -/
def RealUnitaryGenericPairRegularityStatement : Prop :=
  ∀ (n m : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ρ' : Representation ℂ (Matrix.unitaryGroup (Fin m) ℝ) W)
    (π' : (ℂ ⊗[ℝ] Matrix (Fin m) (Fin m) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ W)
    (ds ds' : List RealBlock),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      IsRealGenericGKModule n π → IsRealUnitarizableGKModule n ρ π →
        HasRealStandardParameter n ρ π ds →
    IsRealGKModule m ρ' π' → IsIrreducibleGKModule ρ' π' → IsAdmissibleGKModule ρ' →
      IsRealGenericGKModule m π' → IsRealUnitarizableGKModule m ρ' π' →
        HasRealStandardParameter m ρ' π' ds' →
    ∀ s : ℂ, 1 ≤ s.re → (realPairLFactor ds ds').denominator s ≠ 0

/-- Getz–Hahn 2024, Theorem 11.5.2, case `F = ℂ` (printed page 305): if `(ρ, π)` and
`(ρ', π')` are irreducible admissible generic unitarizable `(𝔤𝔩_n(ℂ), U(n))`- and
`(𝔤𝔩_m(ℂ), U(m))`-modules with standard parameters `ds` and `ds'`, then the pair `L`-factor
`L(s, π × π') = 1 / P(s)`, `P = (complexPairLFactor ds ds').denominator`, is holomorphic and
nonzero for `Re(s) ≥ 1`: `P(s) ≠ 0` there. -/
def ComplexUnitaryGenericPairRegularityStatement : Prop :=
  ∀ (n m : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ρ' : Representation ℂ (Matrix.unitaryGroup (Fin m) ℂ) W)
    (π' : (ℂ ⊗[ℝ] Matrix (Fin m) (Fin m) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ W)
    (ds ds' : List ComplexCharacterData),
    IsComplexGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      IsComplexGenericGKModule n π → IsComplexUnitarizableGKModule n ρ π →
        HasComplexStandardParameter n ρ π ds →
    IsComplexGKModule m ρ' π' → IsIrreducibleGKModule ρ' π' → IsAdmissibleGKModule ρ' →
      IsComplexGenericGKModule m π' → IsComplexUnitarizableGKModule m ρ' π' →
        HasComplexStandardParameter m ρ' π' ds' →
    ∀ s : ℂ, 1 ≤ s.re → (complexPairLFactor ds ds').denominator s ≠ 0

/-! ## Reductions -/

/-- The real case of Getz–Hahn, Theorem 11.5.2 follows from the exponent bound at both
carrier universes and the right half-plane regularity of real pair `L`-factors. -/
def RealUnitaryGenericPairRegularityReductionStatement : Prop :=
  RealUnitaryGenericExponentBoundStatement.{uV} →
    RealUnitaryGenericExponentBoundStatement.{uW} →
      RealPairLFactorRightHalfPlaneRegularityStatement →
        RealUnitaryGenericPairRegularityStatement.{uV, uW}

/-- The complex case of Getz–Hahn, Theorem 11.5.2 follows from the exponent bound at both
carrier universes and the right half-plane regularity of complex pair `L`-factors. -/
def ComplexUnitaryGenericPairRegularityReductionStatement : Prop :=
  ComplexUnitaryGenericExponentBoundStatement.{uV} →
    ComplexUnitaryGenericExponentBoundStatement.{uW} →
      ComplexPairLFactorRightHalfPlaneRegularityStatement →
        ComplexUnitaryGenericPairRegularityStatement.{uV, uW}

end Langlands.Archimedean
