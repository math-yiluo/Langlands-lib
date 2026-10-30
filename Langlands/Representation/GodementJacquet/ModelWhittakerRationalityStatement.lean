import Langlands.Representation.GodementJacquet.Zeta

/-!
# Convergence and rationality of each Whittaker matrix integral on the model

JPSS (1983), Section (5.2), printed 420–421: for `σ` of Whittaker type acting on
its Whittaker model, every full-matrix integral
`Z(Φ, s, W) = ∫ Φ(g) W(g) |det g|^s dg` converges for `Re s` large and defines a
rational function of `q^(-s)`. The common g.c.d. asserted there is not part of
this proposition. This module only defines the proposition.
-/

noncomputable section

namespace Langlands.GodementJacquet

open HarmonicAnalysis Whittaker RankinSelberg

universe uF uV

/-- Every shifted full-matrix Whittaker integral on the actual coefficient model
converges on some right half-plane and has a rational continuation in
`q^(-s)`. For a representation `σ` of `GL_(n+1)` of Whittaker type for the
standard character, possibly reducible, a nonzero standard Whittaker functional
`ℓ`, any Schwartz–Bruhat function `Φ` on all square matrices and any function
`W` of the coefficient image of `ℓ`, the integral
`∫ Φ(g) W(g) |det g|^(s + n/2) dg` for the normalized Haar measure converges
absolutely for `Re s > a` for some real `a`, and agrees there with a rational
function of `q^(-s)`. Each half-plane may depend on `Φ` and `W`. -/
def ModelWhittakerRationalityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V),
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType n (standardCharacter ψ n) σ) →
    ∀ ℓ : (letI := F.canonicalTopologicalData.topology; glFunctionals ψ n σ),
      ℓ.val ≠ 0 →
      letI := F.canonicalTopologicalData.topology
      ∀ (Φ : MatrixTestFunction n F.Carrier) (w : (glCoefficientModel ψ n σ ℓ).toSubmodule),
        (∃ a : ℝ, ∀ s : ℂ, a < s.re →
          Padic.MatrixConverges F Φ (s + jpssShift n) (glModelFunction ψ n σ ℓ w)) ∧
        ∃ R : RationalFunctions,
          HasRationalContinuation F.canonicalTopologicalData.residueCardinality
            (fun s => Padic.matrixIntegral F Φ (s + jpssShift n)
              (glModelFunction ψ n σ ℓ w)) R

end Langlands.GodementJacquet
