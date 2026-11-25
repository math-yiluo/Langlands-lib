/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFiniteDiagonal

/-! # Every uniformizer reduction of diagonal coefficient diagrams

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: def-sfb-diagonal-coefficient-quotients).

## Main definitions

- `QuotientCompatibility`, `FiniteReductions`: every positive quotient identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Identification of a uniformizer reduction with the actual torsion Cartier
class and unit/Chern trace. The positive ell power is merely a presentation of
the quotient's annihilator; the quotient itself is the specified pi power.
The class uses the recorded canonical Cartier arrow. The trace uses the inverse
of the recorded canonical positive unit/Chern splitting, followed by its constant
summand projection. Source: blueprint clause 1 and proof step 1
(blueprint: def-sfb-diagonal-coefficient-quotients). -/
def QuotientCompatibility (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) [IsNoetherian Y]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n)) : Prop :=
  ∃ (hfinite : Finite (ULift.{u + 1} (completedResidue l E π n))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0)
    (hY : IsUnit ((l ^ (r + 1) : ℕ) : Γ(Y, ⊤)))
    (hW : IsUnit ((l ^ (r + 1) : ℕ) : Γ(diagonalSurface Y, ⊤)))
    (eY : FiniteRealization (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) Y)
    (eP : FiniteRealization (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) (ProjectiveLine Y))
    (eW : FiniteRealization (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) (diagonalSurface Y))
    (lineP : QuotientLineRealization l E π n r hA (ProjectiveLine Y) eP)
    (lineW : QuotientLineRealization l E π n r hA (diagonalSurface Y) eW),
    FiniteDiagonalComparison
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) (hfinite := hfinite)
      (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA Y hY hW
      (quotientLine l E π n) d eY eP eW (lineP.iso l) (lineW.iso l)

/-- Every positive uniformizer quotient is identified with its torsion class and
trace, with both integration identities retained under derived reduction.
Source: blueprint clause 1 (blueprint: def-sfb-diagonal-coefficient-quotients). -/
def FiniteReductions (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) [IsNoetherian Y]
    (family : Family l Y) : Prop :=
  ∀ (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (_hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ),
    ∃ d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n),
      Nonempty (ScalarCompatibility (quotientMap l E π n) Y
        (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
        (quotientLineMap l E π n) (family.integral E) d) ∧
      QuotientCompatibility l Y E π n d

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
