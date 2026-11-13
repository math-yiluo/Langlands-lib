import Langlands.BruhatTits.SpecialCompact.CongruenceBasis.ModelCongruence
import Langlands.GroupScheme.IntegralModel.BuildingComparisonAssembly
import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Geometry.Building.SpecialCompact
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # The full model at a special vertex and its cocharacters -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.SpecialCompact.CongruenceGL

open Langlands.GroupScheme Langlands.GroupScheme.IntegralModel Langlands.Geometry.Building
  Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A split integral torus of a relative-component model gives, for every cocharacter of the
generic torus, a cocharacter of the full model whose generic cocharacter is the given
cocharacter followed by the generic torus inclusion. -/
theorem exists_fullModelCocharacter {D : RelativeComponentModelData ↥𝒪[F] F G}
    {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData D S i) (hT : IsSplitTorus T.torus.toGrp)
    (y : cocharacterLattice S) :
    ∃ χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ D.full.group,
      D.full.genericCocharacter χ = CommGroupScheme.groupHom y ≫ i := by
  obtain ⟨ν, hν, -⟩ := hT.existsUnique_baseChangeCocharacter (Spec.algebraMap ↥𝒪[F] F) T.torus
    (CommGroupScheme.groupHom y ≫ T.genericIso.inv)
  refine ⟨CommGroupScheme.groupHom ν ≫ T.inclusion ≫ D.inclusion.hom, ?_⟩
  have hD := D.inclusion.generic_comm
  have hT' := T.generic_comm
  unfold IntegralModel.genericCocharacter Dynamic.baseChangeCocharacter at *
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, Category.assoc, hD,
    Category.comp_id, hT', ← Category.assoc, hν, Category.assoc, Iso.inv_hom_id_assoc]

variable [IsAffineHom G.X.hom]

/-- **The full model at a special vertex.** For a KP assignment available for `G`, and a special
vertex `x` of its apartment, the full model at the singleton facet of `x` has integral points
exactly the special compact subgroup at `x`, and every cocharacter of the maximal split torus is
the generic cocharacter of a cocharacter of this model. -/
theorem exists_specialVertexModel (𝔅 : KPBuildingAssignment.{u})
    (hG : IsConnectedReductive G) (h𝔅 : 𝔅.IsAvailableFor F G hG)
    (x : (𝔅.datum F G hG).base.Apartment)
    (hx : (𝔅.datum F G hG).base.apartment.IsSpecialApartmentVertex x) :
    ∃ M : IntegralModel ↥𝒪[F] F G,
      M.integralPoints = (𝔅.datum F G hG).base.apartment.specialCompactSubgroup x ∧
      ∀ y : cocharacterLattice (𝔅.datum F G hG).base.S,
        ∃ χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group,
          M.genericCocharacter χ =
            CommGroupScheme.groupHom y ≫ (𝔅.datum F G hG).base.i := by
  have hax := h𝔅.bruhatTitsGroupSchemes
  let B := (𝔅.datum F G hG).base.toValuationBuildingData
  have hz : B.IsVertex (B.apartmentMap x) := ⟨1, x, one_smul _ _, hx.2⟩
  have hΩ : (B.vertexModelIndex (B.apartmentMap x) hz).val =
      B.translatedApartmentMap 1 '' {x} := by
    rw [ValuationBuildingData.coe_vertexModelIndex, Set.image_singleton,
      ValuationBuildingData.translatedApartmentMap_one]
  refine ⟨((𝔅.datum F G hG).models.model (B.vertexModelIndex (B.apartmentMap x) hz)).full,
    B.integralPoints_vertexModelIndex _ hax.full_points _ hz, fun y => ?_⟩
  obtain ⟨χ, hχ⟩ := exists_fullModelCocharacter
    ((𝔅.datum F G hG).models.torus _ 1 {x} hΩ) (hax.torus_clause _ 1 {x} hΩ).1.1 y
  refine ⟨χ, hχ.trans ?_⟩
  rw [innerIso_one_hom, Category.comp_id]

end Langlands.BruhatTits.SpecialCompact.CongruenceGL
