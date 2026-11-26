import Langlands.Representation.Whittaker.Spherical
import Langlands.Representation.Shahidi.TwoBlocks
import Langlands.Representation.Shahidi.Geometry
import Langlands.Group.GL.NormalizedCharacter
import Langlands.HarmonicAnalysis.Conductor

/-! # The unramified value of the two-block open-cell sum

Over a `p`-adic field `K` with residue cardinality `q` and an additive character `ψ` of
conductor `𝒪`, let `f` be a function on `GL_((r+1)+(t+1))(K)` with the transformation law of
the normalized spherical section of the representation induced from the upper two-block
parabolic, the unramified spherical Whittaker functions with parameters `a` on `GL_(r+1)` and
`c` on `GL_(t+1)`, and the twist `δ_P^(s/(r+t+2))`. The sum over
`Y ∈ M_((t+1)×(r+1))(K) / M_((t+1)×(r+1))(𝒪)` of `f(w u'(Y)) conj(ψ(Y_(t,0)))` is
`∏_(i,j) (1 − a_i c_j⁻¹ q^(−1−s))` on a right half-plane that depends only on bounds for the
parameters. This is the two-block case of Casselman–Shalika (1980), Theorem 5.4, as used in
Shahidi (1981), p. 352. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Shahidi

open Langlands.GeneralLinear

variable {p : ℕ} [Fact p.Prime]

/-- The lattice of matrices of size `a × b` over `K` whose entries lie in the ring of integers
of the canonical valuation. -/
def integralMatrices (K : PadicField.{u} p) (a b : ℕ) :
    AddSubgroup (Matrix (Fin a) (Fin b) K.Carrier) :=
  AddSubgroup.pi Set.univ fun _ =>
    AddSubgroup.pi Set.univ fun _ => K.canonicalTopologicalData.Integers.toAddSubgroup

/-- The modulus character `δ_P(diag(m₁, m₂)) = |det m₁|^n / |det m₂|^m` of the upper
two-block parabolic of `GL_(m+n)(K)`, for the residue-normalized absolute value. -/
def twoBlockModulus (K : PadicField.{u} p) {m n : ℕ} (m₁ : Langlands.GeneralLinear m K.Carrier)
    (m₂ : Langlands.GeneralLinear n K.Carrier) : ℝ :=
  ((K.canonicalTopologicalData.determinantNorm m m₁ : NNReal) : ℝ) ^ n /
    ((K.canonicalTopologicalData.determinantNorm n m₂ : NNReal) : ℝ) ^ m

/-- **The unramified two-block open-cell sum** (Casselman–Shalika 1980, Theorem 5.4, for the
upper two-block parabolic of `GL_((r+1)+(t+1))`; Shahidi 1981, p. 352).

For ranks `r`, `t` and bounds `A`, `B` there is `σ` with the following property. Let `K` be a
`p`-adic field with residue cardinality `q`, `ψ` an additive character of `K` of conductor
`𝒪` (additive conductor `0`), `ϖ` a uniformizer, and `a`, `c` tuples with `‖a_i‖ ≤ q ^ A` and
`‖c_j⁻¹‖ ≤ q ^ B`. Let `σ < Re s` and let `f` satisfy
`f(u(X) · diag(m₁, m₂) · k) = δ_P(m₁, m₂)^(1/2 + s/(r+t+2)) W°(m₁; a) W°(m₂; c)` for every
`X`, `m₁ ∈ GL_(r+1)(K)`, `m₂ ∈ GL_(t+1)(K)` and `k ∈ GL_((r+1)+(t+1))(𝒪)`, where `u(X)` is the
upper radical matrix and `W°` the Library's explicit spherical Whittaker function for the
standard character of `ψ`. Then
`∑_(Y ∈ M(K)/M(𝒪)) f(w u'(Y)) conj(ψ(Y_(t,0))) = ∏_(i,j) (1 − a_i c_j⁻¹ q^(−1−s))`,
the sum being unconditionally convergent, where `w = blockWeyl (r+1) (t+1)` and
`u'(Y) = intertwiningUnipotent (r+1) (t+1) Y`. -/
def UnramifiedOpenCellSumStatement : Prop :=
  ∀ (r t : ℕ) (A B : ℝ), ∃ σ : ℝ,
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{u} p)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
      K.canonicalTopologicalData.topology),
    K.canonicalTopologicalData.additiveConductor ψ = 0 →
  ∀ (ϖ : K.Carrierˣ) (hϖ : Iwasawa.IsUniformizingElement
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ),
  ∀ (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ),
    (∀ i, ‖(a i : ℂ)‖ ≤ (K.canonicalTopologicalData.residueCardinality : ℝ) ^ A) →
    (∀ j, ‖((c j)⁻¹ : ℂ)‖ ≤ (K.canonicalTopologicalData.residueCardinality : ℝ) ^ B) →
  ∀ s : ℂ, σ < s.re →
  ∀ f : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier → ℂ,
    (∀ (X : Matrix (Fin (r + 1)) (Fin (t + 1)) K.Carrier)
        (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
        (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier)
        (k : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier),
        k ∈ Langlands.Conductor.integralSubgroup K.canonicalTopologicalData.Integers
          (r + 1 + t) →
        f (upper (r + 1) (t + 1) K.Carrier X * GeneralLinear.blockSum (m₁, m₂) * k) =
          ((twoBlockModulus K m₁ m₂ : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + s / ((r + t + 2 : ℕ) : ℂ)) *
            GeneralLinear.Spherical.sphericalWhittaker (n := r) hϖ
              (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
              K.canonicalTopologicalData.residueCardinality a m₁ *
            GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
              (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
              K.canonicalTopologicalData.residueCardinality c m₂) →
    HasSum
      (fun Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸ integralMatrices K (t + 1) (r + 1) =>
        f (blockWeyl (r + 1) (t + 1) K.Carrier *
            intertwiningUnipotent (r + 1) (t + 1) K.Carrier (Quotient.out Y)) *
          starRingEnd ℂ (ψ (Quotient.out Y (Fin.last t) 0) : ℂ))
      (∏ i, ∏ j, (1 - (a i : ℂ) * ((c j : ℂ))⁻¹ *
        (K.canonicalTopologicalData.residueCardinality : ℂ) ^ (-(1 + s))))

end Langlands.Shahidi
