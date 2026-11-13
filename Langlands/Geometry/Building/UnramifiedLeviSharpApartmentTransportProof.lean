import Langlands.Geometry.Building.UnramifiedLeviSharpApartmentTransportStatement
import Langlands.Geometry.Building.LeviSharpTransport
import Langlands.Geometry.Building.UnramifiedFiltrationSharpFixer
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.LocalField.ValuativeInfinite

/-! # Proof of Levi sharp transport from membership in an unramified apartment -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- **Levi sharp transport from chart membership.** Over the maximal unramified extension
`K`, the general infinite-field transport `KPApartmentData.exists_leviSharp_transport`
applies to the split torus `S_K`, the maximal split torus `T_K` and the base-changed
factorization `S_K → T_K → G_K`. -/
theorem unramifiedLeviSharpApartmentTransport :
    UnramifiedLeviSharpApartmentTransportStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : Mono iS.hom.hom.left := mono_of_isMaximalSplitTorus hiS
  intro hiT
  let : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C _ n x hx
  obtain ⟨y, hy⟩ := hx
  have hGK : IsConnectedReductive
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj G) :=
    hG.baseChange_of_algebraicExtension (K := inertiaFixedField F)
  have : Infinite F := LocalField.infinite_of_isNonarchimedeanLocalField F
  have : Infinite (inertiaFixedField F) :=
    Infinite.of_injective (algebraMap F (inertiaFixedField F))
      (algebraMap F (inertiaFixedField F)).injective
  have hSK : IsSplitTorus ((CommGroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).obj S).toGrp :=
    hiS.1.1.baseChange _
  exact D.exists_leviSharp_transport hGK hiT hSK _
    (baseChange_groupHom_comp_of_factorization f hf) n.2 x y hy

end Langlands.Geometry.Building
