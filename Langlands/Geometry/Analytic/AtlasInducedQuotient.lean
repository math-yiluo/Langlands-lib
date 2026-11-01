import Langlands.Geometry.Analytic.AtlasInducedUniversal

/-! # Full bounded maps between induced balanced-quotient atlases -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AtlasInducedAction

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (hH : IsOpen (H : Set G))
  {X Y Z : Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) H}
  [ContinuousSMul H (LocalSpace H X)] [ContinuousSMul H (LocalSpace H Y)]
  [ContinuousSMul H (LocalSpace H Z)]

/-- Transport the original complete equivariant arrow to the actual balanced quotients. -/
def quotientMap (f : X ⟶ Y) : presentation H X hH ⟶ presentation H Y hH :=
  (copiesIso H X hH).inv ≫ copiesMap H f ≫ (copiesIso H Y hH).hom

/-- The transport square commutes as an equality of complete bounded arrows. -/
theorem copiesIso_quotientMap (f : X ⟶ Y) :
    (copiesIso H X hH).hom ≫ quotientMap H hH f =
      copiesMap H f ≫ (copiesIso H Y hH).hom := by
  simp only [quotientMap, Iso.hom_inv_id_assoc]

/-- Quotient transport preserves full equivariance, including the chosen chart data. -/
theorem quotientMap_equivariant (f : X ⟶ Y) (g : G) :
    actionMap H X hH g ≫ quotientMap H hH f =
      quotientMap H hH f ≫ actionMap H Y hH g :=
  ((equivariantCopiesIso H X hH).inv ≫ copiesEquivariantMap H f ≫
    (equivariantCopiesIso H Y hH).hom).comm g

/-- The actual quotient map bundled as a full-group-equivariant bounded arrow. -/
def quotientEquivariantMap (f : X ⟶ Y) : action H X hH ⟶ action H Y hH where
  hom := quotientMap H hH f
  comm := quotientMap_equivariant H hH f

@[simp]
theorem quotientMap_id :
    quotientMap H hH (𝟙 X) = 𝟙 (presentation H X hH) := by
  simp only [quotientMap, copiesMap_id, Category.id_comp, Iso.inv_hom_id]

/-- The quotient maps compose with all bounded pullbacks retained. -/
theorem quotientMap_comp (f : X ⟶ Y) (k : Y ⟶ Z) :
    quotientMap H hH (f ≫ k) = quotientMap H hH f ≫ quotientMap H hH k := by
  simp only [quotientMap, copiesMap_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- Normalized units are natural for the transported whole arrows. -/
theorem quotientUnitMap_naturality (f : X ⟶ Y) :
    localMap H f ≫ quotientUnitMap H Y hH =
      quotientUnitMap H X hH ≫ quotientMap H hH f := by
  simp only [quotientUnitMap, quotientMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, unitMap_naturality, Category.assoc]

/-- Quotient transport retains the original chosen chart, with its coset tag. -/
@[simp]
theorem quotientMap_indexMap (f : X ⟶ Y) (c : G ⧸ H)
    (i : X.V.nonemptyPresentation.atlas.Index) :
    (quotientMap H hH f).indexMap ⟨c, i⟩ =
      ⟨c, (localMap H f).indexMap i⟩ := rfl

/-- The identity pullbacks of transport cancel, leaving exactly the input bounded map. -/
@[simp]
theorem quotientMap_pullback (f : X ⟶ Y) (c : G ⧸ H)
    (i : X.V.nonemptyPresentation.atlas.Index) :
    (quotientMap H hH f).pullback ⟨c, i⟩ = f.hom.pullback i.val := by
  change (BoundedAlgHom.id K _).comp
    ((copiesMap H f).pullback ⟨c, i⟩ |>.comp (BoundedAlgHom.id K _)) = _
  rw [BoundedAlgHom.id_comp, BoundedAlgHom.comp_id, copiesMap_pullback]

/-- Evaluation at the distinguished copy uses the same original source point map. -/
@[simp]
theorem quotientMap_unit (f : X ⟶ Y) (x : LocalSpace H X) :
    (quotientMap H hH f).baseMap (TopologicalInduction.unit H x) =
      TopologicalInduction.unit H (show LocalSpace H Y from f.hom.baseMap x) := by
  have he := congrArg (fun q : X.V.nonemptyPresentation ⟶ presentation H Y hH =>
    q.baseMap x) (quotientUnitMap_naturality H hH f)
  change (quotientUnitMap H Y hH).baseMap (f.hom.baseMap x) =
    (quotientMap H hH f).baseMap ((quotientUnitMap H X hH).baseMap x) at he
  rw [quotientUnitMap_baseMap H X hH x] at he
  exact he.symm.trans (quotientUnitMap_baseMap H Y hH
    (show LocalSpace H Y from f.hom.baseMap x))

/-- On every representative the actual bounded map is exactly [g,x] to [g,f(x)]. -/
@[simp]
theorem quotientMap_mk (f : X ⟶ Y) (g : G) (x : LocalSpace H X) :
    (quotientMap H hH f).baseMap (TopologicalInduction.mk H g x) =
      TopologicalInduction.mk H g (show LocalSpace H Y from f.hom.baseMap x) := by
  have he := congrArg
    (fun q : presentation H X hH ⟶ presentation H Y hH =>
      q.baseMap (TopologicalInduction.unit H x))
    (quotientMap_equivariant H hH f g)
  change (quotientMap H hH f).baseMap
      ((actionMap H X hH g).baseMap (TopologicalInduction.unit H x)) =
    (actionMap H Y hH g).baseMap
      ((quotientMap H hH f).baseMap (TopologicalInduction.unit H x)) at he
  have hs := congrArg (fun p : Space H X => (quotientMap H hH f).baseMap p)
    ((actionMap_baseMap H X hH g (TopologicalInduction.unit H x)).trans
      (TopologicalInduction.smul_unit g x)).symm
  have hm := congrArg (fun p : Space H Y => (actionMap H Y hH g).baseMap p)
    (quotientMap_unit H hH f x)
  have ht := (actionMap_baseMap H Y hH g (TopologicalInduction.unit H
    (show LocalSpace H Y from f.hom.baseMap x))).trans
      (TopologicalInduction.smul_unit g (show LocalSpace H Y from f.hom.baseMap x))
  exact hs.trans (he.trans (hm.trans ht))

end Langlands.Analytic.AtlasInducedAction
