import Langlands.Sheaf.AdicSystem
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Functor.EpiMono

noncomputable section

namespace Langlands.Sheaf.AdicSystem

open CategoryTheory Opposite

universe u v uC vC

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
variable {R : Type u} [CommRing R] (I : Ideal R)
variable [HasSheafify J (ModuleCat.{v} R)]

/-- The sheaf quotient unit is an epimorphism, even when it is not sectionwise surjective. -/
instance quotientMap_app_epi (n : ℕ) (F : CategoryTheory.Sheaf J (ModuleCat.{v} R)) :
    Epi ((quotientMap J I n).app F) := by
  let q := Functor.whiskerLeft F.obj (Langlands.Coefficients.AdicSystem.quotientMap I n)
  haveI : ∀ U, Epi (q.app U) := fun U =>
    (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
  haveI : Epi q := NatTrans.epi_of_epi_app q
  change Epi ((inv (sheafificationAdjunction J (ModuleCat.{v} R)).counit).app F ≫
    (presheafToSheaf J (ModuleCat.{v} R)).map q)
  infer_instance

end Langlands.Sheaf.AdicSystem
