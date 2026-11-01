import Langlands.Geometry.Analytic.AtlasInducedQuotient

/-! # Relative universal property of arbitrary-atlas quotient induction -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AtlasInducedAction

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (hH : IsOpen (H : Set G))
  {X X' : Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) H}
  [ContinuousSMul H (LocalSpace H X)] [ContinuousSMul H (LocalSpace H X')]
  {Y Z : Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) G}

/-- Transport the constructed bounded extension to the actual balanced quotient. -/
def quotientExtendMap (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y) :
    presentation H X hH ⟶ Y.V :=
  (copiesIso H X hH).inv ≫ extendMap H f

/-- The quotient extension into every supplied target is a full equivariant arrow. -/
def quotientExtendToAction (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y) :
    action H X hH ⟶ Y :=
  (equivariantCopiesIso H X hH).inv ≫ extendToAction H f

/-- Equivariance holds for all chosen indices and bounded algebra maps. -/
theorem quotientExtendMap_equivariant (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y)
    (g : G) :
    actionMap H X hH g ≫ quotientExtendMap H hH f =
      quotientExtendMap H hH f ≫ Y.ρ g :=
  (quotientExtendToAction H hH f).comm g

/-- The full normalized-unit triangle survives transport to the quotient. -/
theorem quotientUnitMap_quotientExtendMap (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y) :
    quotientUnitMap H X hH ≫ quotientExtendMap H hH f = f.hom := by
  simp only [quotientUnitMap, quotientExtendMap, Category.assoc,
    Iso.hom_inv_id_assoc, unitMap_extendMap]
  rfl

/-- Restrict through the constructed equivariant copies isomorphism and normalized unit. -/
def quotientRestrictFromAction (p : action H X hH ⟶ Y) :
    normalizedAction H X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y :=
  restrictFromAction H ((equivariantCopiesIso H X hH).hom ≫ p)

/-- Restriction is exactly composition with the actual quotient unit. -/
theorem quotientRestrictFromAction_hom (p : action H X hH ⟶ Y) :
    (quotientRestrictFromAction H hH p).hom = quotientUnitMap H X hH ≫ p.hom :=
  (Category.assoc (unitMap H X) (copiesIso H X hH).hom p.hom).symm

@[simp]
theorem quotientRestrictFromAction_quotientExtendToAction (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y) :
    quotientRestrictFromAction H hH (quotientExtendToAction H hH f) = f := by
  unfold quotientRestrictFromAction quotientExtendToAction
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    restrictFromAction_extendToAction]

@[simp]
theorem quotientExtendToAction_quotientRestrictFromAction (p : action H X hH ⟶ Y) :
    quotientExtendToAction H hH (quotientRestrictFromAction H hH p) = p := by
  unfold quotientRestrictFromAction quotientExtendToAction
  rw [extendToAction_restrictFromAction, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- The relative induction correspondence for the actual balanced-quotient atlas. -/
def quotientActionExtensionEquiv :
    (action H X hH ⟶ Y) ≃
      (normalizedAction H X ⟶
        (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y) where
  toFun := quotientRestrictFromAction H hH
  invFun := quotientExtendToAction H hH
  left_inv := quotientExtendToAction_quotientRestrictFromAction H hH
  right_inv := quotientRestrictFromAction_quotientExtendToAction H hH

/-- Agreement after the entire normalized unit determines the entire extension. -/
theorem quotientExtendToAction_unique (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y)
    (p : action H X hH ⟶ Y) (hp : quotientUnitMap H X hH ≫ p.hom = f.hom) :
    p = quotientExtendToAction H hH f := by
  apply (quotientActionExtensionEquiv H hH).injective
  change quotientRestrictFromAction H hH p =
    quotientRestrictFromAction H hH (quotientExtendToAction H hH f)
  rw [quotientRestrictFromAction_quotientExtendToAction]
  apply Action.Hom.ext
  exact (quotientRestrictFromAction_hom H hH p).trans hp

/-- Source naturality retains the original complete equivariant arrow. -/
theorem quotientActionExtensionEquiv_naturality_left
    (a : X' ⟶ X) (p : action H X hH ⟶ Y) :
    quotientActionExtensionEquiv H hH (quotientEquivariantMap H hH a ≫ p) =
      (AffinoidAtlasPresentation.nonemptyActionFunctor H).map a ≫
        quotientActionExtensionEquiv H hH p := by
  apply Action.Hom.ext
  let p₀ : presentation H X hH ⟶ Y.V := p.hom
  change unitMap H X' ≫ ((copiesIso H X' hH).hom ≫
      ((quotientMap H hH a) ≫ p₀)) =
    localMap H a ≫ (unitMap H X ≫ ((copiesIso H X hH).hom ≫ p₀))
  change (unitMap H X' ≫ ((copiesIso H X' hH).hom ≫ quotientMap H hH a)) ≫ p₀ =
    (localMap H a ≫ (unitMap H X ≫ (copiesIso H X hH).hom)) ≫ p₀
  exact congrArg (fun q => q ≫ p₀) (quotientUnitMap_naturality H hH a).symm

/-- Target naturality holds for every full equivariant arrow, without target continuity. -/
theorem quotientActionExtensionEquiv_naturality_right
    (p : action H X hH ⟶ Y) (q : Y ⟶ Z) :
    quotientActionExtensionEquiv H hH (p ≫ q) =
      quotientActionExtensionEquiv H hH p ≫
        (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).map q := by
  apply Action.Hom.ext
  simp only [quotientActionExtensionEquiv, Equiv.coe_fn_mk,
    quotientRestrictFromAction_hom, Action.comp_hom, Action.res_map_hom]
  exact (Category.assoc (quotientUnitMap H X hH) p.hom q.hom).symm

/-- The constructed extension commutes with every original equivariant source map. -/
theorem quotientExtendToAction_naturality_left (a : X' ⟶ X)
    (f : normalizedAction H X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y) :
    quotientExtendToAction H hH
        ((AffinoidAtlasPresentation.nonemptyActionFunctor H).map a ≫ f) =
      quotientEquivariantMap H hH a ≫ quotientExtendToAction H hH f := by
  apply (quotientActionExtensionEquiv H hH).injective
  rw [quotientActionExtensionEquiv_naturality_left]
  change quotientRestrictFromAction H hH (quotientExtendToAction H hH _) =
    (AffinoidAtlasPresentation.nonemptyActionFunctor H).map a ≫
      quotientRestrictFromAction H hH (quotientExtendToAction H hH f)
  rw [quotientRestrictFromAction_quotientExtendToAction,
    quotientRestrictFromAction_quotientExtendToAction]

/-- The constructed quotient extension commutes with every full target map. -/
theorem quotientExtendToAction_naturality_right (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y)
    (q : Y ⟶ Z) :
    quotientExtendToAction H hH
        (f ≫ (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).map q) =
      quotientExtendToAction H hH f ≫ q := by
  apply (quotientActionExtensionEquiv H hH).injective
  rw [quotientActionExtensionEquiv_naturality_right]
  change quotientRestrictFromAction H hH (quotientExtendToAction H hH _) =
    quotientRestrictFromAction H hH (quotientExtendToAction H hH f) ≫
      (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).map q
  rw [quotientRestrictFromAction_quotientExtendToAction,
    quotientRestrictFromAction_quotientExtendToAction]

/-- The transported extension retains the actual chosen chart composite. -/
@[simp]
theorem quotientExtendMap_indexMap (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y)
    (c : G ⧸ H) (i : X.V.nonemptyPresentation.atlas.Index) :
    (quotientExtendMap H hH f).indexMap ⟨c, i⟩ =
      (Y.ρ c.out).indexMap (f.hom.indexMap i) := rfl

/-- Its bounded pullback is the original contravariant composite. -/
@[simp]
theorem quotientExtendMap_pullback (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y)
    (c : G ⧸ H) (i : X.V.nonemptyPresentation.atlas.Index) :
    (quotientExtendMap H hH f).pullback ⟨c, i⟩ =
      (f.hom.pullback i).comp ((Y.ρ c.out).pullback (f.hom.indexMap i)) := by
  change (BoundedAlgHom.id K _).comp ((extendMap H f).pullback ⟨c, i⟩) = _
  rw [BoundedAlgHom.id_comp, extendMap_pullback]

/-- Every representative evaluates as [g,x] to the actual target action g • f(x). -/
theorem quotientExtendMap_mk (f : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y)
    (g : G) (x : LocalSpace H X) :
    (quotientExtendMap H hH f).baseMap (TopologicalInduction.mk H g x) =
      (Y.ρ g).baseMap (f.hom.baseMap x) := by
  have hu := congrArg (fun p : X.V.nonemptyPresentation ⟶ Y.V => p.baseMap x)
    (quotientUnitMap_quotientExtendMap H hH f)
  change (quotientExtendMap H hH f).baseMap ((quotientUnitMap H X hH).baseMap x) =
    f.hom.baseMap x at hu
  rw [quotientUnitMap_baseMap H X hH x] at hu
  have he := congrArg (fun p : presentation H X hH ⟶ Y.V =>
    p.baseMap (TopologicalInduction.unit H x)) (quotientExtendMap_equivariant H hH f g)
  change (quotientExtendMap H hH f).baseMap
      ((actionMap H X hH g).baseMap (TopologicalInduction.unit H x)) =
    (Y.ρ g).baseMap ((quotientExtendMap H hH f).baseMap
      (TopologicalInduction.unit H x)) at he
  have hs := congrArg (fun p : Space H X => (quotientExtendMap H hH f).baseMap p)
    ((actionMap_baseMap H X hH g (TopologicalInduction.unit H x)).trans
      (TopologicalInduction.smul_unit g x)).symm
  exact hs.trans (he.trans (congrArg (fun p : Y.V.space => (Y.ρ g).baseMap p) hu))

end Langlands.Analytic.AtlasInducedAction
