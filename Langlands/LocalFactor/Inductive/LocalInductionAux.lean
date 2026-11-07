import Langlands.Weil.Local.ExtensionWeilRange
import Langlands.Weil.Representation.InductionAlongCoinduction
import Langlands.Weil.Representation.CoinductionDegreeCoordinates
import Langlands.LocalFactor.Euler.Definitions
import Mathlib.Algebra.Polynomial.Expand

noncomputable section

namespace Langlands.Weil.Local

universe u v

variable {p : ℕ} [Fact p.Prime]

open FiniteRepresentation

/-- The inertia invariants of the actual induced local Weil representation are
`f` copies of the source inertia invariants, using arbitrary degree-one elements. -/
def localInductionCoordinates (E : PadicField.{u} p) (E' : PadicField.{v} p)
    (g : E.Carrier →ₐ[Padic p] E'.Carrier)
    (A : FiniteRepresentation.{0, v, v} ℂ (localWeilGroup E'))
    (Φ : localWeilGroup E) (Φ' : localWeilGroup E')
    (hΦ : localDegreeInt E Φ = 1) (hΦ' : localDegreeInt E' Φ' = 1) :
    invariants (localInertia E)
        (induceAlong (extensionWeilMap E E' g).toMonoidHom
          (extensionWeilMap_injective E E' g) A) ≃ₗ[ℂ]
      (Fin (extensionResidueDegree E E' g) → invariants (localInertia E') A) :=
  (InductionAlong.invariantCoinductionEquiv
      (extensionWeilMap E E' g).toMonoidHom (extensionWeilMap_injective E E' g)
      (localInertia E) A).trans
    (InductionDegree.coordinates (localDegree E).toMonoidHom (localDegree E').toMonoidHom
      (extensionWeilMap E E' g).toMonoidHom A.representation
      (extensionResidueDegree E E' g) (extensionResidueDegree_pos E E' g)
      (localDegreeInt_extensionWeilMap E E' g) Φ hΦ Φ' hΦ')

/-- The coordinate indexed by `i` is evaluation at `Φ^(-i)`. -/
@[simp]
theorem localInductionCoordinates_apply (E : PadicField.{u} p) (E' : PadicField.{v} p)
    (g : E.Carrier →ₐ[Padic p] E'.Carrier)
    (A : FiniteRepresentation.{0, v, v} ℂ (localWeilGroup E'))
    (Φ : localWeilGroup E) (Φ' : localWeilGroup E')
    (hΦ : localDegreeInt E Φ = 1) (hΦ' : localDegreeInt E' Φ' = 1)
    (x : invariants (localInertia E)
      (induceAlong (extensionWeilMap E E' g).toMonoidHom
        (extensionWeilMap_injective E E' g) A))
    (i : Fin (extensionResidueDegree E E' g)) :
    (localInductionCoordinates E E' g A Φ Φ' hΦ hΦ' x i).val =
      x.val.val (Φ ^ (-(i : ℤ))) := rfl

/-- Every ambient Weil element acts by right translation before evaluation. -/
theorem localInductionCoordinates_action_apply
    (E : PadicField.{u} p) (E' : PadicField.{v} p)
    (g : E.Carrier →ₐ[Padic p] E'.Carrier)
    (A : FiniteRepresentation.{0, v, v} ℂ (localWeilGroup E'))
    (Φ : localWeilGroup E) (Φ' : localWeilGroup E')
    (hΦ : localDegreeInt E Φ = 1) (hΦ' : localDegreeInt E' Φ' = 1)
    (w : localWeilGroup E)
    (x : invariants (localInertia E)
      (induceAlong (extensionWeilMap E E' g).toMonoidHom
        (extensionWeilMap_injective E E' g) A))
    (i : Fin (extensionResidueDegree E E' g)) :
    (localInductionCoordinates E E' g A Φ Φ' hΦ hΦ'
      ((invariants (localInertia E)
        (induceAlong (extensionWeilMap E E' g).toMonoidHom
          (extensionWeilMap_injective E E' g) A)).representation w x) i).val =
      x.val.val (Φ ^ (-(i : ℤ)) * w) := rfl

/-- The logarithm of the residue cardinality scales by the relative residue degree. -/
theorem extensionResidueCardinality_log (E : PadicField.{u} p) (E' : PadicField.{v} p)
    (g : E.Carrier →ₐ[Padic p] E'.Carrier) :
    (Real.log (E'.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) =
      (extensionResidueDegree E E' g : ℂ) *
        (Real.log (E.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) := by
  rw [extensionResidueCardinality E E' g, Nat.cast_pow, Real.log_pow,
    Complex.ofReal_mul, Complex.ofReal_natCast]

/-- The spectral variable of the extension is the residue-degree power of the
spectral variable of the base, for every complex argument. -/
theorem extensionSpectralParameter_pow (E : PadicField.{u} p) (E' : PadicField.{v} p)
    (g : E.Carrier →ₐ[Padic p] E'.Carrier) (s : ℂ) :
    Complex.exp (-s * (Real.log (E.canonicalTopologicalData.residueCardinality : ℝ) : ℂ)) ^
        extensionResidueDegree E E' g =
      Complex.exp (-s * (Real.log (E'.canonicalTopologicalData.residueCardinality : ℝ) : ℂ)) := by
  rw [extensionResidueCardinality_log E E' g, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- Polynomial expansion gives the equality of the two local spectral evaluations. -/
theorem extensionExpandedPolynomial_eval (E : PadicField.{u} p) (E' : PadicField.{v} p)
    (g : E.Carrier →ₐ[Padic p] E'.Carrier) (P : Polynomial ℂ) (s : ℂ) :
    (Polynomial.expand ℂ (extensionResidueDegree E E' g) P).eval
        (Complex.exp (-s * (Real.log (E.canonicalTopologicalData.residueCardinality : ℝ) : ℂ))) =
      P.eval (Complex.exp
        (-s * (Real.log (E'.canonicalTopologicalData.residueCardinality : ℝ) : ℂ))) := by
  rw [Polynomial.expand_eval, extensionSpectralParameter_pow E E' g s]

end Langlands.Weil.Local
