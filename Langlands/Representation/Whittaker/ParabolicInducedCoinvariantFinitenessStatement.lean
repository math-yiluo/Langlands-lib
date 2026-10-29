import Langlands.Group.GL.BlockModulus
import Langlands.Group.GL.UpperUnipotent
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Jacquet.Localization
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Preservation of finite character coinvariants by parabolic induction

An internal conditional statement extracted from the finite-orbit argument of
Bernstein--Zelevinsky (1976), section 7.12(1)--(5). The coefficient-finiteness
premise replaces the source's use of irreducible cuspidal inducing data.
This module defines a proposition and supplies no proof of it.
-/

namespace Langlands.Whittaker

universe uF uV

/-- Normalized induction from an actual upper block parabolic preserves
finiteness of all locally constant upper-unipotent character quotients.
The coefficient representation is an arbitrary actual smooth Levi object;
the field and coefficient-carrier universes are independent. -/
def ParabolicInducedCoinvariantFinitenessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (_hn : 0 < n) (B : GeneralLinear.BlockShape n),
      letI := T.generalLinearTopologicalGroup n
      ∀ σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
        (∀ η : (Subgroup.pi Set.univ
            (fun i : Fin B.length =>
              GeneralLinear.upperUnipotent (B.size i) F.Carrier)) →* ℂˣ,
          IsLocallyConstant (fun u => (η u : ℂ)) →
          FiniteDimensional ℂ
            (Jacquet.Localization.Coinvariants σ.representation
              (Subgroup.pi Set.univ
                (fun i : Fin B.length =>
                  GeneralLinear.upperUnipotent (B.size i) F.Carrier)) η)) →
        ∀ θ : GeneralLinear.upperUnipotent n F.Carrier →* ℂˣ,
          IsLocallyConstant (fun u => (θ u : ℂ)) →
          FiniteDimensional ℂ
            (Jacquet.Localization.Coinvariants
              (Induction.smoothInduced (B.parabolic F.Carrier)
                (twist (T.parabolicHalfModulus B)
                  (σ.representation.comp (B.leviProjection F.Carrier))))
              (GeneralLinear.upperUnipotent n F.Carrier) θ)

end Langlands.Whittaker
