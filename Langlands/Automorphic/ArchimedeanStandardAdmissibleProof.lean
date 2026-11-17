import Langlands.Automorphic.CuspidalArchimedeanComponentStatement
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible
import Langlands.Representation.Archimedean.PrincipalSeriesAdmissible

/-!
# Admissibility of the real and complex archimedean standard modules

This module proves `Langlands.Automorphic.ArchimedeanStandardAdmissibleStatement`: the
`O(n)`-finite functions of every real standard module and the `U(n)`-finite functions of every
complex standard module are admissible. The real conjunct is
`Langlands.Archimedean.realStandardAdmissible`. The complex standard module of `ds` is the
complex principal series of the position character of `ds`, and its `U(n)`-finite functions
carry `principalSeriesRep ℂ n (complexPositionCharacter ds)`, which is admissible by
`Langlands.Archimedean.PrincipalSeries.isAdmissibleGKModule_principalSeriesRep`.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

/-- The `U(n)`-intertwiners from a matrix representation of degree `d` of `U(n)` into the
`U(n)`-finite functions of a complex standard module form a space of dimension at most `d`. -/
theorem finrank_gkIntertwiners_complexStandardRep_le (n : ℕ) (ds : List ComplexCharacterData)
    (d : ℕ) (τ : Matrix.unitaryGroup (Fin n) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    Module.finrank ℂ (gkIntertwiners (complexStandardRep n ds) d τ) ≤ d :=
  PrincipalSeries.finrank_gkIntertwiners_principalSeriesRep_le ℂ n
    (complexPositionCharacter ds) d τ

/-- Complex standard modules are admissible. -/
theorem complexStandardAdmissible (n : ℕ) (ds : List ComplexCharacterData) :
    IsAdmissibleGKModule (complexStandardRep n ds) :=
  PrincipalSeries.isAdmissibleGKModule_principalSeriesRep ℂ n (complexPositionCharacter ds)

end Langlands.Archimedean

namespace Langlands.Automorphic

/-- **Admissibility of the archimedean standard modules.** Every real and every complex
standard module is an admissible `(𝔤, K)`-module. -/
theorem archimedeanStandardAdmissible : ArchimedeanStandardAdmissibleStatement :=
  ⟨Archimedean.realStandardAdmissible, Archimedean.complexStandardAdmissible⟩

end Langlands.Automorphic
