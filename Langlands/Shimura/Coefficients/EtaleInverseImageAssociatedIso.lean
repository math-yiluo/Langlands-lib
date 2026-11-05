import Langlands.Shimura.Coefficients.EtaleInverseImageAssociated
import Langlands.Shimura.Coefficients.EtaleAssociatedPullback
import Langlands.Geometry.EtaleRestrictionSectionComparison
import Langlands.Geometry.EtaleSectionPullbackCoherence
import Langlands.Shimura.Coefficients.TorsorSectionSplittingProof

/-! # Invertibility of the arbitrary-morphism product-sheaf base-change map -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtaleDirectImage Langlands.Geometry.EtaleInverseImage
open Langlands.Geometry.EtaleDerivedGlobalPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Etale

variable {X Z : Scheme.{u}} (f : Z ⟶ X) [Etale f] (R : Type u) [CommRing R]

/-- The counit of the composition/base-change adjunction of small etale objects is the first
fiber projection. -/
theorem siteMapPullbackAdjunction_counit_app (U : X.Etale) :
    (EtalePullback.siteMapPullbackAdjunction f).counit.app U = etalePullbackProjection f U := by
  apply MorphismProperty.Over.Hom.ext
  rfl

/-- The unit of the restriction/direct-image adjunction restricts sections along the first
fiber projection. -/
theorem restrictionGeometricAdjunction_unit_app_hom_app
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (U : X.Etaleᵒᵖ) :
    ((restrictionGeometricAdjunction f (ModuleCat.{u} R)).unit.app F).hom.app U =
      F.obj.map (etalePullbackProjection f U.unop).op := by
  rw [← siteMapPullbackAdjunction_counit_app]
  simp [restrictionGeometricAdjunction]

/-- Base change of the product with the first fiber projection agrees with the etale product
comparison followed by the first fiber projection on the second factor. -/
theorem etaleProductPullbackHom_projection (V U : X.Etale) :
    etaleProductPullbackHom f V ((etaleObjectPullback f).obj U) ≫
        prod.map (𝟙 V) (etalePullbackProjection f U) =
      (EtalePullback.siteMap f).map (inv (prodComparison (etaleObjectPullback f) V U)) ≫
        etalePullbackProjection f (V ⨯ U) := by
  apply prod.hom_ext
  · rw [Category.assoc, prod.map_fst, Category.comp_id, Category.assoc,
      ← etalePullbackProjection_natural, ← Category.assoc, ← Functor.map_comp,
      inv_prodComparison_map_fst]
    exact prod.lift_fst _ _
  · rw [Category.assoc, prod.map_snd, Category.assoc, ← etalePullbackProjection_natural,
      ← Functor.map_comp_assoc, inv_prodComparison_map_snd, ← Category.assoc]
    exact congrArg (· ≫ etalePullbackProjection f U) (prod.lift_snd _ _)

/-- The etale product-sheaf comparison is the mate of the direct-image comparison: under the
restriction/direct-image adjunction both have the same adjoint. -/
@[reassoc] theorem restrictionGeometricUnit_etaleProductSheafPullback (V : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (restrictionGeometricAdjunction f (ModuleCat.{u} R)).unit.app
        ((productSheaf X.smallEtaleTopology V).obj F) ≫
      (directImage f (ModuleCat.{u} R)).map ((etaleProductSheafPullback f R V).hom.app F) =
    (productSheaf X.smallEtaleTopology V).map
        ((restrictionGeometricAdjunction f (ModuleCat.{u} R)).unit.app F) ≫
      (directImageProductSheafIso f R V).hom.app
        ((EtalePullback.restriction f (ModuleCat.{u} R)).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map (prod.map (𝟙 V) (etalePullbackProjection f U.unop)).op ≫
      F.obj.map (etaleProductPullbackHom f V ((etaleObjectPullback f).obj U.unop)).op =
    F.obj.map (etalePullbackProjection f (V ⨯ U.unop)).op ≫
      F.obj.map ((EtalePullback.siteMap f).map
        (inv (prodComparison (etaleObjectPullback f) V U.unop))).op
  rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp,
    etaleProductPullbackHom_projection]

/-- Along an etale morphism, the product-sheaf base-change map is the published etale
product-sheaf comparison, through the identification of inverse image with restriction. -/
theorem inverseImageProductSheafMap_etale (V : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    inverseImageProductSheafMap f R V F =
      (inverseImageIsoRestriction f R).hom.app ((productSheaf X.smallEtaleTopology V).obj F) ≫
        (etaleProductSheafPullback f R V).hom.app F ≫
          (productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj V)).map
            ((inverseImageIsoRestriction f R).inv.app F) := by
  apply ((inverseImageAdjunction f R).homEquiv _ _).injective
  have hη : (inverseImageAdjunction f R).unit.app F =
      (restrictionGeometricAdjunction f (ModuleCat.{u} R)).unit.app F ≫
        (directImage f (ModuleCat.{u} R)).map ((inverseImageIsoRestriction f R).inv.app F) := by
    rw [← inverseImageIsoRestriction_unit, Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  have hn := (directImageProductSheafIso f R V).hom.naturality
    ((inverseImageIsoRestriction f R).inv.app F)
  simp only [Functor.comp_map] at hn
  rw [homEquiv_inverseImageProductSheafMap, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, inverseImageIsoRestriction_unit, Functor.map_comp, ← Category.assoc,
    restrictionGeometricUnit_etaleProductSheafPullback, hη, Functor.map_comp, Category.assoc, hn,
    Category.assoc]

/-- Along an etale morphism, the product-sheaf base-change map is an isomorphism. -/
instance isIso_inverseImageProductSheafMap_etale (V : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    IsIso (inverseImageProductSheafMap f R V F) := by
  rw [inverseImageProductSheafMap_etale]
  infer_instance

end Etale

section Composition

variable {X Z W : Scheme.{u}} (f : Z ⟶ X) (g : W ⟶ Z) (R : Type u) [CommRing R]

/-- Scheme-level coherence of the product comparisons for a composite geometric base change. -/
theorem inv_prodComparison_etaleObjectPullbackComp (V U : X.Etale) :
    prod.map (𝟙 _) ((etaleObjectPullbackComp f g).hom.app U) ≫
        prod.map ((etaleObjectPullbackComp f g).hom.app V) (𝟙 _) ≫
        inv (prodComparison (etaleObjectPullback g) ((etaleObjectPullback f).obj V)
          ((etaleObjectPullback f).obj U)) ≫
        (etaleObjectPullback g).map (inv (prodComparison (etaleObjectPullback f) V U)) =
      inv (prodComparison (etaleObjectPullback (g ≫ f)) V U) ≫
        (etaleObjectPullbackComp f g).hom.app (V ⨯ U) := by
  rw [← cancel_mono (prodComparison (etaleObjectPullback f ⋙ etaleObjectPullback g) V U)]
  apply prod.hom_ext
  · have e := (etaleObjectPullbackComp f g).hom.naturality (prod.fst : V ⨯ U ⟶ V)
    simp only [Functor.comp_map] at e
    simp only [Category.assoc, prodComparison_fst, Functor.comp_map, ← Functor.map_comp,
      inv_prodComparison_map_fst, ← e, inv_prodComparison_map_fst_assoc]
    erw [prod.map_fst, prod.map_fst_assoc, Category.id_comp]
  · have e := (etaleObjectPullbackComp f g).hom.naturality (prod.snd : V ⨯ U ⟶ U)
    simp only [Functor.comp_map] at e
    simp only [Category.assoc, prodComparison_snd, Functor.comp_map, ← Functor.map_comp,
      inv_prodComparison_map_snd, ← e, inv_prodComparison_map_snd_assoc]
    erw [prod.map_snd, prod.map_snd_assoc, Category.comp_id]

/-- The direct-image product comparisons for `f`, `g` and `g ≫ f` are compatible with the
composition comparison of direct images and the base-change comparison of the cover. -/
theorem directImageProductSheafIso_comp (V : X.Etale)
    (H : Sheaf W.smallEtaleTopology (ModuleCat.{u} R)) :
    (directImageProductSheafIso f R V).hom.app ((directImage g (ModuleCat.{u} R)).obj H) ≫
        (directImage f (ModuleCat.{u} R)).map
          ((directImageProductSheafIso g R ((etaleObjectPullback f).obj V)).hom.app H) ≫
        (directImage f (ModuleCat.{u} R)).map ((directImage g (ModuleCat.{u} R)).map
          (coverPullback W.smallEtaleTopology ((etaleObjectPullbackComp f g).hom.app V) H)) ≫
        (directImageComp (ModuleCat.{u} R) f g).hom.app
          ((productSheaf W.smallEtaleTopology ((etaleObjectPullback (g ≫ f)).obj V)).obj H) =
      (productSheaf X.smallEtaleTopology V).map
          ((directImageComp (ModuleCat.{u} R) f g).hom.app H) ≫
        (directImageProductSheafIso (g ≫ f) R V).hom.app H := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change H.obj.map ((etaleObjectPullback g).map
        (inv (prodComparison (etaleObjectPullback f) V U.unop))).op ≫
      H.obj.map (inv (prodComparison (etaleObjectPullback g) ((etaleObjectPullback f).obj V)
        ((etaleObjectPullback f).obj U.unop))).op ≫
      H.obj.map (prod.map ((etaleObjectPullbackComp f g).hom.app V) (𝟙 _)).op ≫
      H.obj.map (prod.map (𝟙 _) ((etaleObjectPullbackComp f g).hom.app U.unop)).op =
    H.obj.map ((etaleObjectPullbackComp f g).hom.app (V ⨯ U.unop)).op ≫
      H.obj.map (inv (prodComparison (etaleObjectPullback (g ≫ f)) V U.unop)).op
  rw [← H.obj.map_comp, ← H.obj.map_comp, ← H.obj.map_comp, ← H.obj.map_comp,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp]
  congr 2
  simp only [Category.assoc]
  exact inv_prodComparison_etaleObjectPullbackComp f g V U.unop

/-- The base-change map for a composite: the composition comparison of inverse images followed by
the map for `g ≫ f` is inverse image along `g` of the map for `f`, followed by the map for `g`,
restriction along the base-change comparison of the cover, and the composition comparison of the
coefficients. -/
theorem inverseImageProductSheafMap_comp (V : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (inverseImageComp R f g).hom.app ((productSheaf X.smallEtaleTopology V).obj F) ≫
        inverseImageProductSheafMap (g ≫ f) R V F =
      (inverseImage g R).map (inverseImageProductSheafMap f R V F) ≫
        inverseImageProductSheafMap g R ((etaleObjectPullback f).obj V) ((inverseImage f R).obj F) ≫
          coverPullback W.smallEtaleTopology ((etaleObjectPullbackComp f g).hom.app V)
            ((inverseImage g R).obj ((inverseImage f R).obj F)) ≫
            (productSheaf W.smallEtaleTopology ((etaleObjectPullback (g ≫ f)).obj V)).map
              ((inverseImageComp R f g).hom.app F) := by
  let adj := (inverseImageAdjunction f R).comp (inverseImageAdjunction g R)
  apply (adj.homEquiv _ _).injective
  rw [← cancel_mono ((directImageComp (ModuleCat.{u} R) f g).hom.app
    ((productSheaf W.smallEtaleTopology ((etaleObjectPullback (g ≫ f)).obj V)).obj
      ((inverseImage (g ≫ f) R).obj F)))]
  simp only [adj, Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Functor.comp_map,
    Category.assoc]
  -- the common value: the defining adjoint of the map for `g ≫ f`
  have hl := (directImageComp (ModuleCat.{u} R) f g).hom.naturality
    (inverseImageProductSheafMap (g ≫ f) R V F)
  simp only [Functor.comp_map] at hl
  have hL : (inverseImageAdjunction f R).unit.app ((productSheaf X.smallEtaleTopology V).obj F) ≫
      (directImage f (ModuleCat.{u} R)).map ((inverseImageAdjunction g R).unit.app
        ((inverseImage f R).obj ((productSheaf X.smallEtaleTopology V).obj F))) ≫
      (directImage f (ModuleCat.{u} R)).map ((directImage g (ModuleCat.{u} R)).map
        ((inverseImageComp R f g).hom.app ((productSheaf X.smallEtaleTopology V).obj F) ≫
          inverseImageProductSheafMap (g ≫ f) R V F)) ≫
      (directImageComp (ModuleCat.{u} R) f g).hom.app
        ((productSheaf W.smallEtaleTopology ((etaleObjectPullback (g ≫ f)).obj V)).obj
          ((inverseImage (g ≫ f) R).obj F)) =
      (productSheaf X.smallEtaleTopology V).map ((inverseImageAdjunction (g ≫ f) R).unit.app F) ≫
        (directImageProductSheafIso (g ≫ f) R V).hom.app ((inverseImage (g ≫ f) R).obj F) := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hl]
    erw [inverseImageComposition_unit_assoc R f g]
    rw [← Adjunction.homEquiv_unit]
    exact homEquiv_inverseImageProductSheafMap (g ≫ f) R V F
  rw [hL]
  have h1 := (inverseImageAdjunction g R).unit.naturality (inverseImageProductSheafMap f R V F)
  simp only [Functor.id_map, Functor.comp_map] at h1
  have h2 : (inverseImageAdjunction f R).unit.app ((productSheaf X.smallEtaleTopology V).obj F) ≫
      (directImage f (ModuleCat.{u} R)).map (inverseImageProductSheafMap f R V F) =
      (productSheaf X.smallEtaleTopology V).map ((inverseImageAdjunction f R).unit.app F) ≫
        (directImageProductSheafIso f R V).hom.app ((inverseImage f R).obj F) := by
    have := homEquiv_inverseImageProductSheafMap f R V F
    rw [Adjunction.homEquiv_unit] at this
    exact this
  have h3 : (inverseImageAdjunction g R).unit.app
        ((productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj V)).obj
          ((inverseImage f R).obj F)) ≫
      (directImage g (ModuleCat.{u} R)).map (inverseImageProductSheafMap g R
        ((etaleObjectPullback f).obj V) ((inverseImage f R).obj F)) =
      (productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj V)).map
          ((inverseImageAdjunction g R).unit.app ((inverseImage f R).obj F)) ≫
        (directImageProductSheafIso g R ((etaleObjectPullback f).obj V)).hom.app
          ((inverseImage g R).obj ((inverseImage f R).obj F)) := by
    have := homEquiv_inverseImageProductSheafMap g R ((etaleObjectPullback f).obj V)
      ((inverseImage f R).obj F)
    rw [Adjunction.homEquiv_unit] at this
    exact this
  have h4 := coverPullback_natural W.smallEtaleTopology
    ((etaleObjectPullbackComp f g).hom.app V) ((inverseImageComp R f g).hom.app F)
  have h5 := (directImageProductSheafIso g R ((etaleObjectPullback f).obj V)).hom.naturality
    ((inverseImageComp R f g).hom.app F)
  simp only [Functor.comp_map] at h5
  have h6 := (directImageProductSheafIso f R V).hom.naturality
    ((inverseImageAdjunction g R).unit.app ((inverseImage f R).obj F) ≫
      (directImage g (ModuleCat.{u} R)).map ((inverseImageComp R f g).hom.app F))
  simp only [Functor.comp_map] at h6
  have h7 := directImageProductSheafIso_comp f g R V ((inverseImage (g ≫ f) R).obj F)
  have hu := inverseImageComposition_unit R f g F
  -- unit naturality for `g`
  rw [← Functor.map_comp_assoc, Functor.map_comp (directImage g (ModuleCat.{u} R)),
    ← Category.assoc ((inverseImageAdjunction g R).unit.app _), ← h1, Category.assoc,
    Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% h2]
  -- the map for `g`, the cover comparison and the coefficient comparison
  rw [Functor.map_comp (directImage g (ModuleCat.{u} R)) (inverseImageProductSheafMap g R _ _),
    ← Category.assoc ((inverseImageAdjunction g R).unit.app _), h3, Category.assoc]
  erw [h4]
  rw [Functor.map_comp (directImage g (ModuleCat.{u} R))]
  erw [← reassoc_of% h5]
  rw [← Functor.map_comp_assoc (productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj V)),
    Functor.map_comp (directImage f (ModuleCat.{u} R))]
  simp only [Category.assoc]
  erw [← reassoc_of% h6]
  rw [Functor.map_comp (directImage f (ModuleCat.{u} R))]
  erw [h7]
  rw [← hu]
  simp only [Functor.map_comp, Category.assoc]

end Composition

section Split

variable {S W : Scheme.{u}} (f : W ⟶ S) (R : Type u) [CommRing R]

/-- A terminal cover object `t` identifies `t × U` with `U`. -/
def terminalProdIso {t : S.Etale} (ht : IsTerminal t) (U : S.Etale) : t ⨯ U ≅ U where
  hom := prod.snd
  inv := prod.lift (ht.from U) (𝟙 U)
  hom_inv_id := prod.hom_ext (ht.hom_ext _ _) (by simp)
  inv_hom_id := prod.lift_snd _ _

/-- The product sheaf of a terminal cover object is the original sheaf. -/
def productSheafTerminalIso {t : S.Etale} (ht : IsTerminal t) :
    productSheaf S.smallEtaleTopology t ≅ 𝟭 (Sheaf S.smallEtaleTopology (ModuleCat.{u} R)) :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _
      (NatIso.ofComponents (fun U => F.obj.mapIso (terminalProdIso ht U.unop).symm.op)
        (fun {U U'} b => by
          change F.obj.map (prod.map (𝟙 t) b.unop).op ≫ F.obj.map (prod.lift (ht.from U'.unop)
              (𝟙 U'.unop)).op =
            F.obj.map (prod.lift (ht.from U.unop) (𝟙 U.unop)).op ≫ F.obj.map b
          rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp]
          congr 1
          change _ = (b.unop ≫ prod.lift (ht.from U.unop) (𝟙 U.unop)).op
          congr 1
          exact prod.hom_ext (ht.hom_ext _ _) (by simp))))
    (fun {F F'} a => by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      exact (a.hom.naturality _).symm)

/-- Base change of the identification of `U` with `t × U`. -/
theorem lift_inv_prodComparison {t : S.Etale} (ht : IsTerminal t)
    (ht' : IsTerminal ((etaleObjectPullback f).obj t)) (U : S.Etale) :
    prod.lift (ht'.from ((etaleObjectPullback f).obj U)) (𝟙 _) ≫
        inv (prodComparison (etaleObjectPullback f) t U) =
      (etaleObjectPullback f).map (prod.lift (ht.from U) (𝟙 U)) := by
  rw [← cancel_mono (prodComparison (etaleObjectPullback f) t U), Category.assoc,
    IsIso.inv_hom_id, Category.comp_id]
  apply prod.hom_ext
  · rw [prod.lift_fst, Category.assoc, prodComparison_fst]
    exact ht'.hom_ext _ _
  · rw [prod.lift_snd, Category.assoc, prodComparison_snd, ← Functor.map_comp, prod.lift_snd,
      CategoryTheory.Functor.map_id]

/-- The direct-image product comparison for a terminal cover object is compatible with the
identifications of the product sheaves of terminal objects. -/
theorem directImageProductSheafIso_terminal {t : S.Etale} (ht : IsTerminal t)
    (ht' : IsTerminal ((etaleObjectPullback f).obj t))
    (H : Sheaf W.smallEtaleTopology (ModuleCat.{u} R)) :
    (directImageProductSheafIso f R t).hom.app H ≫
        (directImage f (ModuleCat.{u} R)).map ((productSheafTerminalIso R ht').hom.app H) =
      (productSheafTerminalIso R ht).hom.app ((directImage f (ModuleCat.{u} R)).obj H) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change H.obj.map (inv (prodComparison (etaleObjectPullback f) t U.unop)).op ≫
      H.obj.map (prod.lift (ht'.from ((etaleObjectPullback f).obj U.unop)) (𝟙 _)).op =
    H.obj.map ((etaleObjectPullback f).map (prod.lift (ht.from U.unop) (𝟙 U.unop))).op
  rw [← H.obj.map_comp, ← op_comp, lift_inv_prodComparison f ht ht']

/-- For a terminal cover object, the base-change map is the inverse image of the identification
of the product sheaf with the original sheaf. -/
theorem inverseImageProductSheafMap_terminal {t : S.Etale} (ht : IsTerminal t)
    (ht' : IsTerminal ((etaleObjectPullback f).obj t))
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} R)) :
    inverseImageProductSheafMap f R t F ≫
        (productSheafTerminalIso R ht').hom.app ((inverseImage f R).obj F) =
      (inverseImage f R).map ((productSheafTerminalIso R ht).hom.app F) := by
  apply ((inverseImageAdjunction f R).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, homEquiv_inverseImageProductSheafMap, Category.assoc,
    directImageProductSheafIso_terminal f R ht ht', Adjunction.homEquiv_unit]
  have hn := (productSheafTerminalIso R ht).hom.naturality ((inverseImageAdjunction f R).unit.app F)
  have hu := (inverseImageAdjunction f R).unit.naturality ((productSheafTerminalIso R ht).hom.app F)
  simp only [Functor.id_map, Functor.comp_map] at hn hu
  exact hn.trans hu

variable {G : Type u} [Group G]

/-- For a cover object with a section `σ` from a terminal object, restriction along the graph of
`σ` translated by `g`, as a map from the product sheaf to the original sheaf. -/
def splittingProjection (T : Action S.Etale G) {t : S.Etale} (ht : IsTerminal t) (σ : t ⟶ T.V)
    (g : G) (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} R)) :
    (productSheaf S.smallEtaleTopology T.V).obj F ⟶ F :=
  coverPullback S.smallEtaleTopology (σ ≫ T.ρ g) F ≫ (productSheafTerminalIso R ht).hom.app F

/-- On sections over `U`, the graph projection restricts along the graph of `σ ≫ T.ρ g`. -/
theorem splittingProjection_hom_app (T : Action S.Etale G) {t : S.Etale} (ht : IsTerminal t)
    (σ : t ⟶ T.V) (g : G) (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} R))
    (U : S.Etaleᵒᵖ) :
    (splittingProjection R T ht σ g F).hom.app U =
      F.obj.map (prod.lift (ht.from U.unop ≫ σ ≫ T.ρ g) (𝟙 U.unop)).op := by
  change F.obj.map (prod.map (σ ≫ T.ρ g) (𝟙 U.unop)).op ≫
      F.obj.map (prod.lift (ht.from U.unop) (𝟙 U.unop)).op = _
  rw [← F.obj.map_comp, ← op_comp, prod.lift_map, Category.comp_id]

/-- Under the torsor splitting property, the graph projections exhibit the product sheaf of a cover
with a section as the product of copies of the original sheaf indexed by the group. -/
def isLimitSplittingFan (T : Action S.Etale G) {t : S.Etale} (ht : IsTerminal t) (σ : t ⟶ T.V)
    (hT : TorsorSectionSplitting (R := R) S.smallEtaleTopology T)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} R)) :
    IsLimit (Fan.mk ((productSheaf S.smallEtaleTopology T.V).obj F)
      (fun g : G => splittingProjection R T ht σ g F)) := by
  apply isLimitOfReflects (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} R))
  apply evaluationJointlyReflectsLimits
  intro U
  apply isLimitOfReflects (forget (ModuleCat.{u} R))
  refine Classical.choice ((Types.isLimit_iff_bijective_sectionOfCone _).2 ?_)
  have hb := hT F (Over.mk (ht.from U.unop ≫ σ))
  constructor
  · intro x y hxy
    apply hb.1
    funext g
    have h := congrArg (fun s => s.1 ⟨g⟩) hxy
    simp only [Types.sectionOfCone] at h
    change (splittingProjection R T ht σ g F).hom.app U x =
      (splittingProjection R T ht σ g F).hom.app U y at h
    rw [splittingProjection_hom_app] at h
    exact h
  · intro s
    obtain ⟨x, hx⟩ := hb.2 (fun g => s.1 ⟨g⟩)
    refine ⟨x, Subtype.ext (funext fun j => ?_)⟩
    obtain ⟨g⟩ := j
    have h := congrFun hx g
    change (splittingProjection R T ht σ g F).hom.app U x = s.1 ⟨g⟩
    rw [splittingProjection_hom_app]
    exact h

/-- For a finite group and a cover with a section from a terminal object, both satisfying the
torsor splitting property before and after base change, the product-sheaf base-change map is an
isomorphism: it is a map of limit fans of graph projections. -/
theorem isIso_inverseImageProductSheafMap_of_section [Finite G] (T : Action S.Etale G)
    {t : S.Etale} (ht : IsTerminal t) (ht' : IsTerminal ((etaleObjectPullback f).obj t))
    (σ : t ⟶ T.V) (hT : TorsorSectionSplitting (R := R) S.smallEtaleTopology T)
    (hT' : TorsorSectionSplitting (R := R) W.smallEtaleTopology
      ((etaleTorsorPullbackFunctor f G).obj T))
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} R)) :
    IsIso (inverseImageProductSheafMap f R T.V F) := by
  have : Fintype G := Fintype.ofFinite G
  have h1 := isLimitFanMkObjOfIsLimit (inverseImage f R) (fun _ : G => F)
    (fun g => splittingProjection R T ht σ g F) (isLimitSplittingFan R T ht σ hT F)
  have h2 := isLimitSplittingFan R ((etaleTorsorPullbackFunctor f G).obj T) ht'
    ((etaleObjectPullback f).map σ) hT' ((inverseImage f R).obj F)
  have hw : ∀ j : Discrete G, inverseImageProductSheafMap f R T.V F ≫
      (Fan.mk ((productSheaf W.smallEtaleTopology ((etaleObjectPullback f).obj T.V)).obj
          ((inverseImage f R).obj F))
        (fun g => splittingProjection R ((etaleTorsorPullbackFunctor f G).obj T) ht'
          ((etaleObjectPullback f).map σ) g ((inverseImage f R).obj F))).π.app j =
      (Fan.mk ((inverseImage f R).obj ((productSheaf S.smallEtaleTopology T.V).obj F))
        (fun g => (inverseImage f R).map (splittingProjection R T ht σ g F))).π.app j := by
    rintro ⟨g⟩
    change inverseImageProductSheafMap f R T.V F ≫
        (coverPullback W.smallEtaleTopology ((etaleObjectPullback f).map σ ≫
            (etaleObjectPullback f).map (T.ρ g)) ((inverseImage f R).obj F) ≫
          (productSheafTerminalIso R ht').hom.app ((inverseImage f R).obj F)) =
      (inverseImage f R).map (coverPullback S.smallEtaleTopology (σ ≫ T.ρ g) F ≫
        (productSheafTerminalIso R ht).hom.app F)
    rw [← Functor.map_comp, ← inverseImageProductSheafMap_coverPullback_assoc,
      inverseImageProductSheafMap_terminal f R ht ht', CategoryTheory.Functor.map_comp]
  let φ : Fan.mk ((inverseImage f R).obj ((productSheaf S.smallEtaleTopology T.V).obj F))
        (fun g => (inverseImage f R).map (splittingProjection R T ht σ g F)) ⟶
      Fan.mk ((productSheaf W.smallEtaleTopology ((etaleObjectPullback f).obj T.V)).obj
          ((inverseImage f R).obj F))
        (fun g => splittingProjection R ((etaleTorsorPullbackFunctor f G).obj T) ht'
          ((etaleObjectPullback f).map σ) g ((inverseImage f R).obj F)) :=
    { hom := inverseImageProductSheafMap f R T.V F, w := hw }
  have hφ : IsIso φ := IsLimit.hom_isIso h1 h2 φ
  exact (Cone.forget _).map_isIso φ

end Split

section Torsor

/-- Restriction along an isomorphism of cover objects is an isomorphism. -/
instance isIso_coverPullback {S : Scheme.{u}} (R : Type u) [CommRing R] {V V' : S.Etale}
    (a : V' ⟶ V) [IsIso a] (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} R)) :
    IsIso (coverPullback S.smallEtaleTopology a F) :=
  ⟨⟨coverPullback S.smallEtaleTopology (inv a) F, by
      rw [← coverPullback_comp, IsIso.inv_hom_id, coverPullback_id], by
      rw [← coverPullback_comp, IsIso.hom_inv_id, coverPullback_id]⟩⟩

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (R : Type u) [CommRing R]

/-- The base-change map along a composite is an isomorphism if and only if the inverse image along
the second morphism of the base-change map for the first one is, provided the base-change map for
the second morphism is an isomorphism. -/
theorem isIso_inverseImageProductSheafMap_comp_iff {W : Scheme.{u}} (g : W ⟶ Z) (V : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    [IsIso (inverseImageProductSheafMap g R ((etaleObjectPullback f).obj V)
      ((inverseImage f R).obj F))] :
    IsIso (inverseImageProductSheafMap (g ≫ f) R V F) ↔
      IsIso ((inverseImage g R).map (inverseImageProductSheafMap f R V F)) := by
  have h := inverseImageProductSheafMap_comp f g R V F
  constructor
  · intro hc
    have : IsIso ((inverseImageComp R f g).hom.app ((productSheaf X.smallEtaleTopology V).obj F) ≫
        inverseImageProductSheafMap (g ≫ f) R V F) := inferInstance
    rw [h] at this
    exact IsIso.of_isIso_comp_right _
      (inverseImageProductSheafMap g R ((etaleObjectPullback f).obj V) ((inverseImage f R).obj F) ≫
        coverPullback W.smallEtaleTopology ((etaleObjectPullbackComp f g).hom.app V)
          ((inverseImage g R).obj ((inverseImage f R).obj F)) ≫
        (productSheaf W.smallEtaleTopology ((etaleObjectPullback (g ≫ f)).obj V)).map
          ((inverseImageComp R f g).hom.app F))
  · intro hc
    have : IsIso ((inverseImageComp R f g).hom.app ((productSheaf X.smallEtaleTopology V).obj F) ≫
        inverseImageProductSheafMap (g ≫ f) R V F) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((inverseImageComp R f g).hom.app ((productSheaf X.smallEtaleTopology V).obj F)) _

/-- For a finite geometric torsor `Y`, the product-sheaf base-change map along an arbitrary
morphism `f` is an isomorphism. The proof restricts to the cover `Y ×_X Z` of `Z`, compares
with base change along the cover `Y → X`, where the torsor acquires the diagonal section, and
applies the split case. -/
theorem isIso_inverseImageProductSheafMap_of_torsor {G : Type u} [Group G]
    (Y : Action X.Etale G) (hY : IsFiniteGeometricTorsor X Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    IsIso (inverseImageProductSheafMap f R Y.V F) := by
  have : Finite G := hY.1
  let W' : Z.Etale := (etaleObjectPullback f).obj Y.V
  let f' : W'.left ⟶ Y.V.left := pullback.fst Y.V.hom f
  have : Etale W'.hom := W'.prop
  have : Etale Y.V.hom := Y.V.prop
  have hjf : W'.hom ≫ f = f' ≫ Y.V.hom := pullback.condition.symm
  apply EtaleRestrictionCover.isIso_of_restrictionFamily (fun _ : Unit => W')
    (EtaleRestrictionCover.coversTop_of_jointlySurjective _ (fun z => ?_))
  · intro _
    have hR := (inverseImageIsoRestriction W'.hom R).hom.naturality
      (inverseImageProductSheafMap f R Y.V F)
    suffices hI : IsIso ((inverseImage W'.hom R).map (inverseImageProductSheafMap f R Y.V F)) by
      have hc : IsIso ((inverseImage W'.hom R).map (inverseImageProductSheafMap f R Y.V F) ≫
          (inverseImageIsoRestriction W'.hom R).hom.app _) := inferInstance
      rw [hR] at hc
      exact IsIso.of_isIso_comp_left ((inverseImageIsoRestriction W'.hom R).hom.app
        ((inverseImage f R).obj ((productSheaf X.smallEtaleTopology Y.V).obj F))) _
    rw [← isIso_inverseImageProductSheafMap_comp_iff f R W'.hom Y.V F, hjf]
    -- the torsor base-changed to its own cover has the diagonal section
    let T := (etaleTorsorPullbackFunctor Y.V.hom G).obj Y
    let t : Y.V.left.Etale := MorphismProperty.Over.mk ⊤ (𝟙 Y.V.left) inferInstance
    have ht : IsTerminal t := MorphismProperty.Over.mkIdTerminal (@Etale) Y.V.left
    have ht' : IsTerminal ((etaleObjectPullback f').obj t) :=
      ht.isTerminalObj (etaleObjectPullback f') t
    let σ : t ⟶ T.V := MorphismProperty.Over.homMk
      (pullback.lift (𝟙 Y.V.left) (𝟙 Y.V.left) rfl) (pullback.lift_snd _ _ _)
    have hT := etaleTorsorSectionSplitting Y.V.left G T (hY.pullback Y.V.hom Y) R
    have hT' := etaleTorsorSectionSplitting W'.left G ((etaleTorsorPullbackFunctor f' G).obj T)
      ((hY.pullback Y.V.hom Y).pullback f' T) R
    have : IsIso (inverseImageProductSheafMap f' R ((etaleObjectPullback Y.V.hom).obj Y.V)
        ((inverseImage Y.V.hom R).obj F)) :=
      isIso_inverseImageProductSheafMap_of_section f' R T ht ht' σ hT hT'
        ((inverseImage Y.V.hom R).obj F)
    rw [isIso_inverseImageProductSheafMap_comp_iff Y.V.hom R f' Y.V F]
    infer_instance
  · obtain ⟨y, hy⟩ := (hY.pullback f Y).2.2.1 z
    exact ⟨(), y, hy⟩

/-- For a finite geometric torsor, the product-sheaf base-change map as an isomorphism. -/
def inverseImageProductSheafIso {G : Type u} [Group G] (Y : Action X.Etale G)
    (hY : IsFiniteGeometricTorsor X Y) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (inverseImage f R).obj ((productSheaf X.smallEtaleTopology Y.V).obj F) ≅
      (productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj Y.V)).obj
        ((inverseImage f R).obj F) :=
  have := isIso_inverseImageProductSheafMap_of_torsor f R Y hY F
  asIso (inverseImageProductSheafMap f R Y.V F)

@[simp] theorem inverseImageProductSheafIso_hom {G : Type u} [Group G] (Y : Action X.Etale G)
    (hY : IsFiniteGeometricTorsor X Y) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (inverseImageProductSheafIso f R Y hY F).hom = inverseImageProductSheafMap f R Y.V F := rfl

/-- For a finite geometric torsor, the comparison of associated sheaves along an arbitrary
morphism is an isomorphism at every coefficient action. -/
theorem isIso_inverseImageAssociatedMap_app_of_torsor {G : Type u} [Group G]
    (Y : Action X.Etale G) (hY : IsFiniteGeometricTorsor X Y)
    (F : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G) :
    IsIso ((inverseImageAssociatedMap f R Y).app F) := by
  have : Finite G := hY.1
  have := isIso_inverseImageProductSheafMap_of_torsor f R Y hY F.V
  exact isIso_inverseImageAssociatedMap_app f R Y F

/-- For a finite geometric torsor `Y`, inverse image along an arbitrary morphism of the associated
sheaf is the associated sheaf of the base-changed torsor with the inverse-image coefficients,
naturally in the coefficient action. -/
def inverseImageAssociatedIso {G : Type u} [Group G] (Y : Action X.Etale G)
    (hY : IsFiniteGeometricTorsor X Y) :
    associatedFunctor X.smallEtaleTopology Y ⋙ inverseImage f R ≅
      (inverseImage f R).mapAction G ⋙
        associatedFunctor Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y) :=
  NatIso.ofComponents
    (fun F => have := isIso_inverseImageAssociatedMap_app_of_torsor f R Y hY F
      asIso ((inverseImageAssociatedMap f R Y).app F))
    (fun a => (inverseImageAssociatedMap f R Y).naturality a)

@[simp] theorem inverseImageAssociatedIso_hom_app {G : Type u} [Group G] (Y : Action X.Etale G)
    (hY : IsFiniteGeometricTorsor X Y)
    (F : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G) :
    (inverseImageAssociatedIso f R Y hY).hom.app F = (inverseImageAssociatedMap f R Y).app F :=
  rfl

/-- The comparison isomorphism on invariant sections. -/
@[reassoc] theorem inverseImageAssociatedIso_hom_inclusion {G : Type u} [Group G]
    (Y : Action X.Etale G) (hY : IsFiniteGeometricTorsor X Y)
    (F : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G) :
    (inverseImageAssociatedIso f R Y hY).hom.app F ≫
        inclusion Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)
          (((inverseImage f R).mapAction G).obj F) =
      (inverseImage f R).map (inclusion X.smallEtaleTopology Y F) ≫
        (inverseImageProductSheafIso f R Y hY F.V).hom :=
  inverseImageAssociatedMap_inclusion f R Y F

/-- The inverse comparison recovers the inverse image of the original invariant inclusion. -/
@[reassoc] theorem inverseImageAssociatedIso_inv_inclusion {G : Type u} [Group G]
    (Y : Action X.Etale G) (hY : IsFiniteGeometricTorsor X Y)
    (F : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G) :
    (inverseImageAssociatedIso f R Y hY).inv.app F ≫
        (inverseImage f R).map (inclusion X.smallEtaleTopology Y F) =
      inclusion Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)
          (((inverseImage f R).mapAction G).obj F) ≫
        (inverseImageProductSheafIso f R Y hY F.V).inv := by
  rw [← cancel_mono (inverseImageProductSheafIso f R Y hY F.V).hom, Category.assoc,
    ← inverseImageAssociatedIso_hom_inclusion, Iso.inv_hom_id_app_assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end Torsor

end Langlands.Shimura.Coefficients
