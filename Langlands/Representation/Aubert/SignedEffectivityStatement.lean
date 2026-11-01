import Langlands.Representation.Aubert.AlternatingOperator
import Langlands.Representation.Smooth.IrreducibleCompositionFactors
import Langlands.Representation.CuspidalSupport.LeviDefinitions

/-!
# Signed effectivity on constituents of quasicuspidal induction

This proposition isolates the nonnegativity consequence of the corrected
duality-complex argument. It supplies no proof of that consequence.
-/

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- For every irreducible constituent of an actual induction from irreducible
quasicuspidal Levi data, the common support sign makes the Aubert class
coordinatewise effective in the lattice of actual irreducible classes. -/
def SignedEffectivityStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : GeneralLinear.BlockShape n)
    (σ : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)),
    Representation.IsIrreducible σ.representation →
    CuspidalSupport.IsLeviQuasicuspidal B σ.representation →
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hπ : Representation.IsIrreducible π.representation),
      SmoothRep.IsSubquotient π
        ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj σ) →
      SmoothRep.IrreducibleGrothendieckProof.factorMap
        (((-1 : ℤ) ^ (n - B.length)) •
          alternatingOperator.{uF, uV} F T n
            (GeneralLinear.finiteLengthClass n F.Carrier π
              (SmoothRep.hasFiniteLength_of_isIrreducible hπ))) ∈
        VirtualRepresentation.effective

end Langlands.Aubert
