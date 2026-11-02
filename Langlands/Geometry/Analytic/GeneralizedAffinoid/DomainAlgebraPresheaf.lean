import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain

/-! # The retained algebra presheaves of full affinoid domains -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory Opposite

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K)

/-- Keep each full domain's actual presentation and its bounded restrictions. -/
def boundedPresheaf : (Domain K A)ᵒᵖ ⥤ PresentedAffinoidAlgebra K where
  obj U := U.unop.algebra
  map f := f.unop.restriction
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Keep the complete normed rings underlying the full domain presentations. -/
def banachPresheaf : (Domain K A)ᵒᵖ ⥤ BanachRing :=
  boundedPresheaf K A ⋙ PresentedAffinoidAlgebra.toBanachRing K

/-- The actual stored domain algebras with their bounded restriction maps,
forgetting only the norm and presentation. -/
def algebraPresheaf : (Domain K A)ᵒᵖ ⥤ CommAlgCat K where
  obj U := CommAlgCat.of K U.unop.algebra
  map f := CommAlgCat.ofHom f.unop.restriction.toAlgHom
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem algebraPresheaf_obj (U : Domain K A) :
    (algebraPresheaf K A).obj (op U) = CommAlgCat.of K U.algebra := rfl

@[simp]
theorem algebraPresheaf_map_apply {U V : Domain K A} (f : U ⟶ V)
    (a : V.algebra) :
    (algebraPresheaf K A).map f.op a = f.restriction a := rfl

/-- The full-domain bridge retains the rational bounded presheaf literally. -/
theorem rational_boundedPresheaf :
    (RationalChart.toDomainFunctor K A).op ⋙ boundedPresheaf K A =
      RationalChart.boundedPresheaf K A := rfl

/-- The full-domain bridge retains the rational Banach presheaf literally. -/
theorem rational_banachPresheaf :
    (RationalChart.toDomainFunctor K A).op ⋙ banachPresheaf K A =
      RationalChart.banachPresheaf K A := rfl

/-- In particular, restriction gives the original rational quotient-algebra
presheaf with exactly its original maps. -/
theorem rational_algebraPresheaf :
    (RationalChart.toDomainFunctor K A).op ⋙ algebraPresheaf K A =
      RationalChart.algebraPresheaf K A := rfl

/-- The actual bounded structural maps form a natural transformation from
the constant base presentation. -/
def baseMapNat : (Functor.const (Domain K A)ᵒᵖ).obj A ⟶ boundedPresheaf K A where
  app U := U.unop.baseMap
  naturality U V f := by
    change V.unop.baseMap = f.unop.restriction.comp U.unop.baseMap
    exact f.unop.comp_baseMap.symm

/-- Forgetting the norm retains the same structural algebra maps. -/
def algebraBaseMapNat :
    (Functor.const (Domain K A)ᵒᵖ).obj (CommAlgCat.of K A) ⟶ algebraPresheaf K A where
  app U := CommAlgCat.ofHom U.unop.baseMap.toAlgHom
  naturality U V f := by
    ext a
    exact congrArg (fun g : BoundedAlgHom K A V.unop.algebra => g a)
      f.unop.comp_baseMap.symm

@[simp]
theorem algebraBaseMapNat_app_apply (U : Domain K A) (a : A) :
    (algebraBaseMapNat K A).app (op U) a = U.baseMap a := rfl

/-- On the actual whole domain the presheaf has the original algebra. -/
theorem algebraPresheaf_whole :
    (algebraPresheaf K A).obj (op (whole K A)) = CommAlgCat.of K A := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
