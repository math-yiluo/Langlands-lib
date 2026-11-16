import Langlands.GroupScheme.RelativeLevi.ParabolicEtaleLocalModels
import Langlands.GroupScheme.RelativeLevi.ParabolicSheaf
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationZariski

/-! # Zariski gluing of smooth proper parabolic models -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {hG : IsReductive G}

namespace SmoothProperModel

/-- Supplied smooth proper models on an arbitrary open base cover give
an actual smooth proper model over the entire base. -/
theorem nonempty_of_openCover (𝒰 : Scheme.OpenCover.{u} S)
    (d : ∀ i, SmoothProperModel ((GroupScheme.baseChange (𝒰.f i)).obj G)
      (hG.baseChange (𝒰.f i))) :
    Nonempty (SmoothProperModel G hG) := by
  let H : ∀ i, Over (𝒰.X i) := fun i => (d i).scheme
  let e : ∀ i, (schemeYoneda (𝒰.X i)).obj (H i) ≅
      (Over.map (𝒰.f i)).op ⋙ parabolicPresheaf G hG :=
    fun i => (Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ _)
      (restrictedRepresentation (𝒰.f i) (d i))
  obtain ⟨V, ⟨eV⟩⟩ := LocalRepresentation.exists_representation_zariski
    ((isSheaf_iff_isSheaf_of_type _ _).mpr (parabolic_isSheaf G hG)) 𝒰 H e
  exact ⟨⟨V,
    (Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ _).symm eV,
    LocalRepresentation.property_of_local_representations (@Smooth)
      V eV 𝒰 H e (fun i => (d i).smooth),
    LocalRepresentation.property_of_local_representations (@IsProper)
      V eV 𝒰 H e (fun i => (d i).proper)⟩⟩

/-- Choose a global model obtained from supplied models on an open cover. -/
def zariskiGlue (𝒰 : Scheme.OpenCover.{u} S)
    (d : ∀ i, SmoothProperModel ((GroupScheme.baseChange (𝒰.f i)).obj G)
      (hG.baseChange (𝒰.f i))) : SmoothProperModel G hG :=
  Classical.choice (nonempty_of_openCover 𝒰 d)

end SmoothProperModel

end Langlands.GroupScheme.ParabolicSubgroupModuli
