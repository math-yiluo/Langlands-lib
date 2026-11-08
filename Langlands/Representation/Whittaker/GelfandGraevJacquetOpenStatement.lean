import Langlands.Representation.Whittaker.GelfandGraev
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Geometric.ClosedSubgroupDefinitions
import Langlands.Group.GL.ReverseBlocks

/-!
# The open orbit piece of the Jacquet module of a Gelfand–Graev representation (statement)

For a representation of a standard block parabolic, `parabolicNormalizedJacquet` is the
normalized Levi action on its coinvariants under the unipotent radical. On the restriction of a
representation of `GL_n` it is literally `normalizedJacquet`.

`GelfandGraevOpenPieceStatement` asserts that this normalized Jacquet module of the open orbit
piece `c-Ind_H^P (ψ ∘ Ad(w)⁻¹)` of the Gelfand–Graev representation, with `w` the block-reversal
matrix and `H = P ∩ w N w⁻¹`, is the Gelfand–Graev representation of the Levi.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis

universe uF uV

section

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (B : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The normalized Jacquet module of a representation of the block parabolic: the Levi acts on
the unipotent-radical coinvariants through its section, scaled by `δ_P^(-1/2)`. -/
def parabolicNormalizedJacquet (ρ : Representation ℂ (B.parabolic F.Carrier) V) :
    Representation ℂ (B.Levi F.Carrier)
      (Jacquet.Coinvariants ρ (B.unipotentRadical F.Carrier)) :=
  (Jacquet.normalizedActionOfModulus ρ (B.unipotentRadical F.Carrier) ⊤
    B.top_le_normalizer_unipotentRadical (B.topModulus (T.leviModulus B))).comp B.leviToTop

/-- On the restriction of a representation of `GL_n`, this is the normalized Jacquet module. -/
theorem normalizedJacquet_eq_parabolicNormalizedJacquet
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    T.normalizedJacquet B ρ =
      parabolicNormalizedJacquet T B (ρ.comp (B.parabolic F.Carrier).subtype) := rfl

end

/-- The open orbit piece of the Gelfand–Graev representation `c-Ind_N^G ψ` restricted to the
block parabolic `P`, for the block-reversal representative `w`: compact induction from
`H = P ∩ w N w⁻¹` to `P` of the character `h ↦ ψ_N(w⁻¹ h w)`. Its normalized Jacquet module is
the Gelfand–Graev representation of the Levi. -/
def GelfandGraevOpenPieceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (n : ℕ) (B : BlockShape (n + 1)),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    Nonempty ((parabolicNormalizedJacquet F.canonicalTopologicalData B
      (Induction.compactInduced
        (Geometric.orbitStabilizer (upperUnipotent (n + 1) F.Carrier) (B.parabolic F.Carrier)
          (B.reverseMatrix F.Carrier))
        ((gelfandGraevCharacterRepresentation ψ n).comp
          (Geometric.stabilizerToInducing (upperUnipotent (n + 1) F.Carrier)
            (B.parabolic F.Carrier) (B.reverseMatrix F.Carrier))))).Equiv
      (leviGelfandGraev B ψ.complex))

end Langlands.Whittaker
