import Langlands.Global.Factors.CuspidalPairFunctionalEquationTCStatement
import Langlands.Automorphic.ArchimedeanParameterReduction
import Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction
import Langlands.Automorphic.PlaceComponentExistence
import Langlands.Automorphic.CuspidalWhittaker.PlaceWhittaker
import Langlands.Representation.Archimedean.ComplexGenericStandardParameterProof

/-! # Archimedean parameters of cuspidal realizations over totally complex fields

`cuspidalArchimedeanParameterExistenceTC` proves
`CuspidalArchimedeanParameterExistenceTCStatement`: over a totally complex number field,
every actual cuspidal realization of `GL_(r+1)` has a complex standard-module parameter at
every complex place. The real-place clause is vacuous because a totally complex field has no
real place. At a complex place, the proved generic-component statement
(`cuspidalArchimedeanGenericComponentBridge` applied to
`cuspidalArchimedeanIrreducibleAdmissibleComponent` and
`cuspidalArchimedeanWhittakerFunctional`) gives an irreducible admissible generic
`(𝔤𝔩_(r+1)(ℂ), U(r+1))`-module inside the realization, and the proved `GL_n(ℂ)` theorem
`Archimedean.complexGenericStandardParameter` gives it a standard-module parameter, which
`OperatorRealization.hasComplexPlaceParameter_of_component` transports to the realization.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Global

open NumberField Langlands.Automorphic

/-- **Archimedean standard-module parameters over totally complex fields.** Every actual
cuspidal realization of `GL_(r+1)` over a totally complex number field `F` has a complex
standard-module parameter at every complex place of `F`; the real-place clause holds
vacuously. -/
theorem cuspidalArchimedeanParameterExistenceTC :
    CuspidalArchimedeanParameterExistenceTCStatement.{u} := by
  intro F _ _ _ _ r T
  have hG := cuspidalArchimedeanGenericComponentBridge
    cuspidalArchimedeanIrreducibleAdmissibleComponent cuspidalArchimedeanWhittakerFunctional
    F r T
  refine ⟨fun v => absurd v.2
    (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v.1)), fun v => ?_⟩
  obtain ⟨V, _, _, ρ, π, ι, hι, hρ, hπ, hgk, hirr, hadm, hgen⟩ := hG.2 v
  obtain ⟨ds, hds⟩ :=
    Archimedean.complexGenericStandardParameter (r + 1) V ρ π hgk hirr hadm hgen
  exact ⟨ds, OperatorRealization.hasComplexPlaceParameter_of_component hι hρ hπ hds⟩

end Langlands.Global
