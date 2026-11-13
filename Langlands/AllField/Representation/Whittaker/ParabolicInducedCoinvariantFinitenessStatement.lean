import Langlands.Representation.Whittaker.ParabolicInducedCoinvariantFinitenessStatement
import Langlands.AllField.Group.GL.BlockModulus
/-!
# Preservation of finite character coinvariants by parabolic induction

An internal conditional statement extracted from the finite-orbit argument of
Bernstein--Zelevinsky (1976), section 7.12(1)--(5). The coefficient-finiteness
premise replaces the source's use of irreducible cuspidal inducing data.
This module defines a proposition and supplies no proof of it.
-/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding ParabolicInducedCoinvariantFinitenessStatement
open Langlands.AllField.Whittaker

universe uF uV

/-- Normalized induction from an actual upper block parabolic preserves
finiteness of all locally constant upper-unipotent character quotients.
The coefficient representation is an arbitrary actual smooth Levi object;
the field and coefficient-carrier universes are independent. -/
def ParabolicInducedCoinvariantFinitenessStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    letI := T.topology
    ∀ (n : ℕ) (_hn : 0 < n) (B : GeneralLinear.BlockShape n),
      letI := T.generalLinearTopologicalGroup n
      ∀ σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F),
        (∀ η : (Subgroup.pi Set.univ
            (fun i : Fin B.length =>
              GeneralLinear.upperUnipotent (B.size i) F)) →* ℂˣ,
          IsLocallyConstant (fun u => (η u : ℂ)) →
          FiniteDimensional ℂ
            (Jacquet.Localization.Coinvariants σ.representation
              (Subgroup.pi Set.univ
                (fun i : Fin B.length =>
                  GeneralLinear.upperUnipotent (B.size i) F)) η)) →
        ∀ θ : GeneralLinear.upperUnipotent n F →* ℂˣ,
          IsLocallyConstant (fun u => (θ u : ℂ)) →
          FiniteDimensional ℂ
            (Jacquet.Localization.Coinvariants
              (Induction.smoothInduced (B.parabolic F)
                (twist (T.parabolicHalfModulus B)
                  (σ.representation.comp (B.leviProjection F))))
              (GeneralLinear.upperUnipotent n F) θ)

end Langlands.AllField.Whittaker
