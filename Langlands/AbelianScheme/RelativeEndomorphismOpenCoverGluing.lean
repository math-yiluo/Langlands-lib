import Langlands.GroupScheme.Cartier.BaseChange
import Langlands.GroupScheme.Cartier.RelativeHomSheaf
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationZariski

/-! # Relative endomorphisms glued over an open base cover -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AbelianScheme

open Langlands.GroupScheme.Cartier
open Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (B : AbelianScheme S)

private abbrev endFunctor {S : Scheme.{u}} (B : AbelianScheme S) : (Over S)ᵒᵖ ⥤ Type u :=
  relativeHomFunctor B.toCommGroupScheme B.toCommGroupScheme ⋙ forget AddCommGrpCat.{u}

/-- A separated locally finite type scheme representing the actual relative
endomorphism functor on the full slice over the base. -/
structure GlobalRelativeEndomorphismRepresentation where
  scheme : Over S
  locallyOfFiniteType : LocallyOfFiniteType scheme.hom
  separated : IsSeparated scheme.hom
  comparison : endFunctor B ≅ yoneda.obj scheme

private theorem isSheaf_liftedEndFunctor :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S) (endFunctor B ⋙ uliftFunctor.{u + 1}) := by
  let J := Scheme.zariskiTopology.over S
  have h := isSheaf_relativeHomFunctor B.toCommGroupScheme B.toCommGroupScheme J
  have h₀ : Presheaf.IsSheaf J (endFunctor B) :=
    Presheaf.isSheaf_comp_of_isSheaf J _ (forget AddCommGrpCat.{u}) h
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr (Presieve.isSheaf_comp_uliftFunctor _
    ((isSheaf_iff_isSheaf_of_type _ _).mp h₀))

variable (𝒰 : Scheme.OpenCover.{u} S) (H : ∀ i, Over (𝒰.X i))
    (comparison : ∀ i, endFunctor ((baseChange (𝒰.f i)).obj B) ≅ yoneda.obj (H i))

private def localLiftedComparison (i : 𝒰.I₀) :
    (schemeYoneda (𝒰.X i)).obj (H i) ≅ (Over.map (𝒰.f i)).op ⋙
      (endFunctor B ⋙ uliftFunctor.{u + 1}) := by
  let b := 𝒰.f i
  let e := relativeHomBaseChangeIso B.toCommGroupScheme B.toCommGroupScheme b
  let e₀ : (Over.map b).op ⋙ endFunctor B ≅ endFunctor ((baseChange b).obj B) :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e (forget AddCommGrpCat.{u})
  exact ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (e₀ ≪≫ comparison i) uliftFunctor.{u + 1}).symm

/-- Relative endomorphism representatives on a base open cover glue to a
representative of the same actual Hom functor over the whole base. -/
def globalRelativeEndomorphismRepresentation
    (hFiniteType : ∀ i, LocallyOfFiniteType (H i).hom)
    (hSeparated : ∀ i, IsSeparated (H i).hom) :
    GlobalRelativeEndomorphismRepresentation B := by
  let e := localLiftedComparison B 𝒰 H comparison
  let hex := LocalRepresentation.exists_representation_zariski
    (isSheaf_liftedEndFunctor B) 𝒰 H e
  let X := hex.choose
  let ex := hex.choose_spec.some
  exact
    { scheme := X
      locallyOfFiniteType := LocalRepresentation.property_of_local_representations
        (@LocallyOfFiniteType) X ex 𝒰 H e hFiniteType
      separated := LocalRepresentation.property_of_local_representations
        (@IsSeparated) X ex 𝒰 H e hSeparated
      comparison := (fullyFaithfulULiftFunctor.whiskeringRight (Over S)ᵒᵖ).preimageIso ex.symm }

end Langlands.AbelianScheme
