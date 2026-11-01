import Langlands.Geometry.Analytic.GeneralizedAffinoid.InducedFamilyExtension

/-! # Bounded quotient-atlas realization of affinoid-family extension -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {G : Type v} [Group G] [TopologicalSpace G] (H : Subgroup G)

/-- The constructed family extension is natural in the original input. -/
theorem extendFamily_naturality_left {X X' : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (a : X' ⟶ X)
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y) :
    extendFamily H ((localFunctor H).map a ≫ f) =
      (functor H).map a ≫ extendFamily H f := by
  apply (familyExtensionEquiv H).injective
  rw [familyExtensionEquiv_naturality_left]
  change restrictFamily H (extendFamily H _) =
    (localFunctor H).map a ≫ restrictFamily H (extendFamily H f)
  rw [restrictFamily_extendFamily, restrictFamily_extendFamily]

/-- The constructed family extension commutes with actual target arrows. -/
theorem extendFamily_naturality_right {X : NormContinuousSpace K H}
    {Y Z : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y)
    (q : Y ⟶ Z) :
    extendFamily H (f ≫ (Action.res (AffinoidFamily.{u, v} K) H.subtype).map q) =
      extendFamily H f ≫ q := by
  apply (familyExtensionEquiv H).injective
  rw [familyExtensionEquiv_naturality_right]
  change restrictFamily H (extendFamily H _) =
    restrictFamily H (extendFamily H f) ≫
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).map q
  rw [restrictFamily_extendFamily, restrictFamily_extendFamily]

variable [IsTopologicalGroup G] [CompleteSpace K] (hH : IsOpen (H : Set G))

/-- The inverse comparison intertwines entire bounded atlas action maps. -/
theorem atlasComparisonInv_equivariant (X : NormContinuousSpace K H) (g : G) :
    atlasActionMap H hH X g ≫ atlasComparisonInv H hH X =
      atlasComparisonInv H hH X ≫ (actionMap H X.unop g).atlasMap :=
  (equivariantAtlasComparisonIso H hH X).inv.comm g

/-- The inverse comparison is natural as a complete bounded atlas map. -/
theorem atlasComparisonInv_naturality {X X' : NormContinuousSpace K H}
    (a : X' ⟶ X) :
    atlasMap H hH a ≫ atlasComparisonInv H hH X =
      atlasComparisonInv H hH X' ≫ (familyMap H a).atlasMap :=
  congrArg Action.Hom.hom ((equivariantAtlasComparison H hH).inv.naturality a)

/-- Realize the actual bounded extension on the original balanced quotient atlas. -/
def extendAtlasMap {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y) :
    atlasPresentation H hH X ⟶ Y.V.atlasPresentation :=
  atlasComparisonInv H hH X ≫ (extendFamilyMap H f).atlasMap

/-- Equivariance retains the base map, chart choices and bounded pullbacks. -/
theorem extendAtlasMap_equivariant {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y)
    (g : G) :
    atlasActionMap H hH X g ≫ extendAtlasMap H hH f =
      extendAtlasMap H hH f ≫ (Y.ρ g).atlasMap := by
  unfold extendAtlasMap
  rw [← Category.assoc, atlasComparisonInv_equivariant, Category.assoc,
    ← AffinoidFamily.Hom.atlasMap_comp, extendFamilyMap_equivariant,
    AffinoidFamily.Hom.atlasMap_comp, ← Category.assoc]

/-- The constructed full-group equivariant bounded quotient-atlas extension. -/
def extendAtlas {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y) :
    (equivariantAtlasFunctor H hH).obj X ⟶
      ((AffinoidFamily.atlasFunctor (K := K)).mapAction G).obj Y :=
  ⟨extendAtlasMap H hH f, extendAtlasMap_equivariant H hH f⟩

/-- The normalized unit triangle commutes as an equation of complete atlas maps. -/
theorem unitAtlasMap_extendAtlasMap {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y) :
    unitAtlasMap H hH X ≫ extendAtlasMap H hH f = f.hom.atlasMap := by
  unfold unitAtlasMap extendAtlasMap
  rw [Category.assoc, ← Category.assoc (atlasComparisonHom H hH X),
    atlasComparisonHom_inv, Category.id_comp,
    ← AffinoidFamily.Hom.atlasMap_comp, unitFamilyMap_extendFamilyMap]
  rfl

/-- Naturality in every original equivariant bounded input morphism. -/
theorem extendAtlasMap_naturality_left {X X' : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (a : X' ⟶ X)
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y) :
    extendAtlasMap H hH ((localFunctor H).map a ≫ f) =
      atlasMap H hH a ≫ extendAtlasMap H hH f := by
  have he : extendFamilyMap H ((localFunctor H).map a ≫ f) =
      familyMap H a ≫ extendFamilyMap H f :=
    congrArg Action.Hom.hom (extendFamily_naturality_left H a f)
  unfold extendAtlasMap
  rw [he, AffinoidFamily.Hom.atlasMap_comp, ← Category.assoc,
    ← atlasComparisonInv_naturality, Category.assoc]

/-- Naturality in every equivariant bounded target-family morphism. -/
theorem extendAtlasMap_naturality_right {X : NormContinuousSpace K H}
    {Y Z : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y)
    (q : Y ⟶ Z) :
    extendAtlasMap H hH
        (f ≫ (Action.res (AffinoidFamily.{u, v} K) H.subtype).map q) =
      extendAtlasMap H hH f ≫ q.hom.atlasMap := by
  have he : extendFamilyMap H
        (f ≫ (Action.res (AffinoidFamily.{u, v} K) H.subtype).map q) =
      extendFamilyMap H f ≫ q.hom :=
    congrArg Action.Hom.hom (extendFamily_naturality_right H f q)
  unfold extendAtlasMap
  rw [he, AffinoidFamily.Hom.atlasMap_comp, Category.assoc]

@[simp]
theorem extendAtlasMap_indexMap {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y)
    (c : (atlas H X.unop hH).Index) :
    ((extendAtlasMap H hH f).indexMap c).val =
      (Y.ρ c.val.out).indexMap (f.hom.indexMap PUnit.unit) := rfl

/-- The atlas pullback is precisely the constructed bounded copywise composite. -/
@[simp]
theorem extendAtlasMap_pullback {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y)
    (c : (atlas H X.unop hH).Index) :
    (extendAtlasMap H hH f).pullback c =
      (f.hom.pullback PUnit.unit).comp
        ((Y.ρ c.val.out).pullback (f.hom.indexMap PUnit.unit)) :=
  BoundedAlgHom.ext fun _ => rfl

/-- On every coset copy the continuous map applies the chosen target operator. -/
theorem extendAtlasMap_baseMap_copy {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y)
    (c : G ⧸ H) (x : LocalSpectrum H X.unop) :
    (extendAtlasMap H hH f).baseMap (spectrumHomeomorph H X.unop hH ⟨c, x⟩) =
      (Y.ρ c.out).spectrumMap (f.hom.spectrumMap ⟨PUnit.unit, x⟩) := by
  change (extendFamilyMap H f).spectrumMap
      ((spectrumHomeomorph H X.unop hH).symm
        (spectrumHomeomorph H X.unop hH ⟨c, x⟩)) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- The formula uses any representative, independently of the chosen out values. -/
theorem extendAtlasMap_baseMap_mk {X : NormContinuousSpace K H}
    {Y : Action (AffinoidFamily.{u, v} K) G}
    (f : (localFunctor H).obj X ⟶
      (Action.res (AffinoidFamily.{u, v} K) H.subtype).obj Y)
    (g : G) (x : LocalSpectrum H X.unop) :
    (extendAtlasMap H hH f).baseMap (TopologicalInduction.mk H g x) =
      (Y.ρ g).spectrumMap (f.hom.spectrumMap ⟨PUnit.unit, x⟩) := by
  have hu := congrArg
    (fun p : (localFamily H X).atlasPresentation ⟶ Y.V.atlasPresentation =>
      p.baseMap ⟨PUnit.unit, x⟩) (unitAtlasMap_extendAtlasMap H hH f)
  change (extendAtlasMap H hH f).baseMap
    ((unitAtlasMap H hH X).baseMap ⟨PUnit.unit, x⟩) =
      f.hom.spectrumMap ⟨PUnit.unit, x⟩ at hu
  rw [unitAtlasMap_baseMap_apply] at hu
  have he := congrArg
    (fun p : atlasPresentation H hH X ⟶ Y.V.atlasPresentation =>
      p.baseMap (TopologicalInduction.unit H x)) (extendAtlasMap_equivariant H hH f g)
  change (extendAtlasMap H hH f).baseMap (g • TopologicalInduction.unit H x) =
    (Y.ρ g).spectrumMap
      ((extendAtlasMap H hH f).baseMap (TopologicalInduction.unit H x)) at he
  simpa only [TopologicalInduction.smul_unit, hu] using he

end Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction
