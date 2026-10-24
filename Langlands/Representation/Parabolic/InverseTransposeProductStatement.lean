import Langlands.Group.GL.ReverseBlocks
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Classification.SupercuspidalTwist

/-!
# Inverse transpose and normalized upper block products

Internal transport statements for the actual normalized induction constructors.
These proposition definitions do not assert smooth contragredient duality.
-/

namespace Langlands.Parabolic

universe uF uV uL

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- Pulling back a normalized upper product by inverse transpose reverses the
block order and pulls back each block by its own inverse transpose. -/
def NormalizedProductInverseTransposeClause : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n → ∀ B : GeneralLinear.BlockShape n,
    letI := T.generalLinearTopologicalGroup n
    ∀ (V : Fin B.length → Type uV) [hadd : ∀ i, AddCommGroup (V i)]
      [hmod : ∀ i, Module ℂ (V i)]
      (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)),
      (∀ i, IsSmooth (σ i)) →
      letI : ∀ i : Fin B.reverse.length, AddCommGroup (V i.rev) := fun i => hadd i.rev
      letI : ∀ i : Fin B.reverse.length, Module ℂ (V i.rev) := fun i => hmod i.rev
      Nonempty (Representation.Equiv
        ((T.normalizedProductInduced B σ).comp
          (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom)
        (T.normalizedProductInduced B.reverse (V := fun i => V i.rev)
          (fun i => (σ i.rev).comp
            (GeneralLinear.inverseTranspose (B.size i.rev) F.Carrier).toMonoidHom)))

/-- On the same carrier, determinant-power twisting and inverse-transpose
pullback commute after negating the real exponent. -/
def InverseTransposeDeterminantTwistClause : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear n F.Carrier) V) (u : ℝ),
    (twist (T.determinantPowerCharacter n u) σ).comp
        (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom =
      twist (T.determinantPowerCharacter n (-u))
        (σ.comp (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom)

/-- Reversing a strictly decreasing finite real sequence and negating all
its entries gives a strictly decreasing sequence. -/
def ReverseNegateStrictAntiClause : Prop :=
  ∀ (r : ℕ) (u : Fin r → ℝ), StrictAnti u → StrictAnti (fun i : Fin r => -u i.rev)

/-- Internal inverse-transpose transport and the determinant-twist/order
compatibilities used for standard modules, over arbitrary p-adic fields. -/
def InverseTransposeProductStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    NormalizedProductInverseTransposeClause.{uF, uV} F T ∧
    InverseTransposeDeterminantTwistClause.{uF, uV} F T) ∧
  ReverseNegateStrictAntiClause

/-- The same statement in the carrier universe that accommodates an independent
lift; this is a universe specialization, not an extra transport hypothesis. -/
abbrev InverseTransposeProductLiftStatement : Prop :=
  InverseTransposeProductStatement.{uF, max uV uL}

end Langlands.Parabolic
