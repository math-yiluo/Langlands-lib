import Langlands.GroupScheme.Rational.QuasiSplitCocycleTorusReduction
import Langlands.GroupScheme.SimplyConnected.CoverExistenceProof
import Langlands.GroupScheme.Rational.InfiniteFieldStronglyRegularPoint
import Langlands.GroupScheme.Rational.QuasiSplitRegularConjugateReduction
import Langlands.GroupScheme.Rational.RegularConjugateFiniteGaloisProof
import Langlands.GroupScheme.Rational.QuasiSplitRegularClassRationalReduction
import Langlands.GroupScheme.Rational.QuasiSplitSteinbergQuotient

/-! # Torus reduction for cocycles of quasi-split semisimple groups: the remaining input -/

universe u

namespace Langlands.GroupScheme

/-- With simply connected covers and strongly regular points supplied by their proofs, Steinberg's
torus reduction needs only the rational conjugacy transfer for quasi-split simply connected
groups. -/
theorem quasiSplitCocycleTorusReduction_of_regularConjugate
    (hconj : QuasiSplitSimplyConnectedRegularConjugateStatement.{u}) :
    QuasiSplitCocycleTorusReductionStatement.{u} :=
  quasiSplitCocycleTorusReduction_of_prerequisites simplyConnectedCoverExistence
    infiniteFieldStronglyRegularPoint hconj

/-- Steinberg's torus reduction from rational points of Galois-stable strongly regular classes
(Borel–Springer 8.6), through the published conjugacy-transfer reduction and the published
finite-Galois conjugacy proof. -/
theorem quasiSplitCocycleTorusReduction_of_classRational
    (hclass : QuasiSplitRegularClassRationalStatement.{u}) :
    QuasiSplitCocycleTorusReductionStatement.{u} :=
  quasiSplitCocycleTorusReduction_of_regularConjugate
    (quasiSplitSimplyConnectedRegularConjugate_of_classRational hclass
      regularConjugateFiniteGalois)

/-- Steinberg's torus reduction from Steinberg's class quotient of simply connected quasi-split
groups, through the published reduction of Borel–Springer 8.6 to that quotient. -/
theorem quasiSplitCocycleTorusReduction_of_steinbergQuotient
    (hquot : QuasiSplitSteinbergQuotientStatement.{u}) :
    QuasiSplitCocycleTorusReductionStatement.{u} :=
  quasiSplitCocycleTorusReduction_of_classRational
    (quasiSplitRegularClassRationalReduction hquot)

/-- **Steinberg's torus reduction for quasi-split semisimple groups** (Steinberg 1965, §§10–11,
over arbitrary fields as in Borel–Springer 1968, 8.6): every natural cocycle of a semisimple
quasi-split group on a finite Galois cover reduces, after a finite Galois refinement, to a
closed torus. -/
theorem quasiSplitCocycleTorusReduction : QuasiSplitCocycleTorusReductionStatement.{u} :=
  quasiSplitCocycleTorusReduction_of_steinbergQuotient quasiSplitSteinbergQuotient

end Langlands.GroupScheme
