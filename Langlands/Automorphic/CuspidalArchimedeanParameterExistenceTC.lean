import Langlands.Automorphic.ArchimedeanParameterReduction
import Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction
import Langlands.Automorphic.PlaceComponentExistence
import Langlands.Automorphic.CuspidalWhittaker.PlaceWhittaker
import Langlands.Representation.Archimedean.ComplexGenericStandardParameterProof
import Langlands.Global.Factors.CuspidalPairFunctionalEquationTCStatement

/-!
# Archimedean parameters of cuspidal realizations over totally complex fields

`cuspidalArchimedeanParameterExistenceTC` proves
`Langlands.Global.CuspidalArchimedeanParameterExistenceTCStatement`. Over a totally complex
number field the real-place clause is vacuous. At a complex place, the proof composes the
irreducible admissible generic component given by the published bridge
`cuspidalArchimedeanGenericComponentBridge` with a standard-module parameter of that component
(`Archimedean.complexGenericStandardParameter`).
-/

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Archimedean parameters over totally complex fields.** For every actual cuspidal
realization `T` of `GL_{r+1}` over a totally complex number field with compact adele quotient,
every complex place has a list of complex characters whose standard module's `U(r+1)`-finite
part embeds into the space of `T`, intertwining the compact and Lie actions at that place.
There are no real places, so the real-place clause holds trivially. -/
theorem cuspidalArchimedeanParameterExistenceTC :
    CuspidalArchimedeanParameterExistenceTCStatement.{u} := by
  intro F _ _ _ _ r T
  refine ⟨fun v => absurd v.2 (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
    (NumberField.IsTotallyComplex.isComplex v.1)), fun v => ?_⟩
  obtain ⟨V, _, _, ρ, π, ι, hι, hρ, hπ, hgk, hirr, hadm, hgen⟩ :=
    (cuspidalArchimedeanGenericComponentBridge cuspidalArchimedeanIrreducibleAdmissibleComponent
      cuspidalArchimedeanWhittakerFunctional F r T).2 v
  obtain ⟨ds, hds⟩ :=
    Archimedean.complexGenericStandardParameter (r + 1) V ρ π hgk hirr hadm hgen
  exact ⟨ds, OperatorRealization.hasComplexPlaceParameter_of_component hι hρ hπ hds⟩

end Langlands.Automorphic
