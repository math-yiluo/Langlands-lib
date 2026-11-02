import Langlands.Sheaf.Renard.BasisStalkRepresentativesStatement
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Representatives and common-refinement equality for actual basis stalks

The forgetful functor preserves the actual lifted filtered colimit. Its
representatives and equality criterion descend to original section values.
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Langlands.Sheaf.Renard

private instance forgetPreservesNeighborhoodColimits :
    PreservesFilteredColimitsOfSize.{u,u} (forget AddCommGrpCat.{max u v}) :=
  preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{max u v})

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- Every element of the existing raw stalk is the germ of an original section. -/
theorem rawStalk_representative (F : RawPresheaf.{u,v} B) (x : X) :
    RawStalkRepresentativeStatement F x := by
  intro a
  obtain ⟨N, ⟨s⟩, hs⟩ := Concrete.colimit_exists_rep (stalkDiagram F x) a
  exact ⟨N.obj.unop, N.property, s, hs⟩

/-- Equality in the actual raw stalk is equality after an actual basis refinement. -/
theorem rawGerm_eq_iff (F : RawPresheaf.{u,v} B) (x : X) :
    RawGermEqualityStatement F x := by
  intro U V hxU hxV s t
  change colimit.ι (stalkDiagram F x) (⟨op U, hxU⟩ : BasisNeighborhood B x)
      (ULift.up s) =
    colimit.ι (stalkDiagram F x) (⟨op V, hxV⟩ : BasisNeighborhood B x)
      (ULift.up t) ↔ _
  refine (Concrete.colimit_rep_eq_iff_exists (stalkDiagram F x)
    (i := ⟨op U, hxU⟩) (j := ⟨op V, hxV⟩) (ULift.up s) (ULift.up t)).trans ?_
  constructor
  · rintro ⟨W, f, g, hfg⟩
    refine ⟨W.obj.unop, W.property, f.hom.unop.hom.le, g.hom.unop.hom.le, ?_⟩
    exact congrArg ULift.down
      ((stalkDiagram_map_apply F f s).symm.trans
        (hfg.trans (stalkDiagram_map_apply F g t)))
  · rintro ⟨W, hxW, hWU, hWV, hst⟩
    let f : (⟨op U, hxU⟩ : BasisNeighborhood B x) ⟶ ⟨op W, hxW⟩ :=
      neighborhoodHom hWU
    let g : (⟨op V, hxV⟩ : BasisNeighborhood B x) ⟶ ⟨op W, hxW⟩ :=
      neighborhoodHom hWV
    refine ⟨⟨op W, hxW⟩, f, g, ?_⟩
    exact (stalkDiagram_map_apply F f s).trans
      ((congrArg ULift.up hst).trans
        (stalkDiagram_map_apply F g t).symm)

/-- The representative assertion for the normalized presheaf's underlying functor. -/
theorem stalk_representative (F : Presheaf.{u,v} B) (x : X) :
    StalkRepresentativeStatement F x :=
  rawStalk_representative F.obj x

/-- The refinement criterion for the normalized presheaf's underlying functor. -/
theorem germ_eq_iff (F : Presheaf.{u,v} B) (x : X) :
    GermEqualityStatement F x :=
  rawGerm_eq_iff F.obj x

/-- Renard's complete raw and normalized basis-stalk representative description. -/
theorem basisStalkRepresentatives :
    BasisStalkRepresentativesStatement.{u,v} := by
  intro X _ B
  exact ⟨fun F x => ⟨rawStalk_representative F x, rawGerm_eq_iff F x⟩,
    fun F x => ⟨stalk_representative F x, germ_eq_iff F x⟩⟩

end Langlands.Sheaf.Renard
