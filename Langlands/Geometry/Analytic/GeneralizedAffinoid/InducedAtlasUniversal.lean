import Langlands.Geometry.Analytic.GeneralizedAffinoid.InducedAtlasCopies
import Langlands.Geometry.Analytic.GeneralizedAffinoid.InducedAtlasExtension

/-! # Relative induction into arbitrary actual atlas-action targets -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (hH : IsOpen (H : Set G))

/-- The original bounded copy inclusion transported to the balanced quotient. -/
def quotientCopyMap (X : NormContinuousSpace K H) (c : G ⧸ H) :
    (localFamily H X).atlasPresentation ⟶ atlasPresentation H hH X :=
  (copyMap H X c).atlasMap ≫ atlasComparisonHom H hH X

/-- The representative correction is an equation of entire bounded atlas maps. -/
theorem quotientCopyMap_action (X : NormContinuousSpace K H)
    (g : G) (c : G ⧸ H) :
    quotientCopyMap H hH X c ≫ atlasActionMap H hH X g =
      (localActionMap H X (correction H g c)).atlasMap ≫
        quotientCopyMap H hH X (g • c) := by
  unfold quotientCopyMap
  rw [Category.assoc, ← atlasComparisonHom_equivariant, ← Category.assoc,
    ← AffinoidFamily.Hom.atlasMap_comp, copyMap_action,
    AffinoidFamily.Hom.atlasMap_comp, Category.assoc]

/-- Complete arrows from the quotient atlas are determined on its actual copies. -/
theorem quotientAtlasHom_ext {X : NormContinuousSpace K H}
    {Y : AffinoidAtlasPresentation.{u, max u v, v} K}
    {f k : atlasPresentation H hH X ⟶ Y}
    (h : ∀ c, quotientCopyMap H hH X c ≫ f = quotientCopyMap H hH X c ≫ k) :
    f = k := by
  have he : atlasComparisonHom H hH X ≫ f = atlasComparisonHom H hH X ≫ k := by
    apply familyAtlasHom_ext H
    intro c
    simpa only [quotientCopyMap, Category.assoc] using h c
  calc
    f = atlasComparisonInv H hH X ≫ (atlasComparisonHom H hH X ≫ f) := by
      rw [← Category.assoc, atlasComparisonInv_hom, Category.id_comp]
    _ = atlasComparisonInv H hH X ≫ (atlasComparisonHom H hH X ≫ k) := by rw [he]
    _ = k := by rw [← Category.assoc, atlasComparisonInv_hom, Category.id_comp]

/-- The unit corrects the chosen representative before entering its coset copy. -/
theorem unitAtlasMap_eq_quotientCopyMap (X : NormContinuousSpace K H) :
    unitAtlasMap H hH X =
      (localActionMap H X (identityRepresentative H)⁻¹).atlasMap ≫
        quotientCopyMap H hH X (identityCoset H) := by
  unfold unitAtlasMap quotientCopyMap
  rw [unitFamilyMap_eq, AffinoidFamily.Hom.atlasMap_comp, Category.assoc]

/-- Translating the normalized unit recovers the entire bounded copy inclusion. -/
theorem unitAtlasMap_action (X : NormContinuousSpace K H) (c : G ⧸ H) :
    unitAtlasMap H hH X ≫ atlasActionMap H hH X c.out =
      quotientCopyMap H hH X c := by
  unfold unitAtlasMap quotientCopyMap
  rw [Category.assoc, ← atlasComparisonHom_equivariant, ← Category.assoc,
    ← AffinoidFamily.Hom.atlasMap_comp, unitFamilyMap_action]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Categorical target action in geometric composition order. -/
theorem atlasTargetAction_comp
    (Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G) (g k : G) :
    Y.ρ k ≫ Y.ρ g = Y.ρ (g * k) :=
  (Y.ρ.map_mul g k).symm

/-- Copywise bounded extension into any existing categorical atlas-action target. -/
def extendToAtlasMap {X : NormContinuousSpace K H}
    {Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (f : (localAtlasFunctor H).obj X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).obj Y) :
    atlasPresentation H hH X ⟶ Y.V :=
  atlasComparisonInv H hH X ≫
    assembleCopyAtlasMap H (fun c => f.hom ≫ Y.ρ c.out)

/-- Copy restriction recovers the entire prescribed target-action composite. -/
@[simp]
theorem quotientCopyMap_extendToAtlasMap {X : NormContinuousSpace K H}
    {Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (f : (localAtlasFunctor H).obj X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).obj Y)
    (c : G ⧸ H) :
    quotientCopyMap H hH X c ≫ extendToAtlasMap H hH f = f.hom ≫ Y.ρ c.out := by
  unfold quotientCopyMap extendToAtlasMap
  rw [Category.assoc, ← Category.assoc (atlasComparisonHom H hH X),
    atlasComparisonHom_inv, Category.id_comp, copyMap_assembleCopyAtlasMap]
  rfl

/-- The constructed extension is equivariant in all bounded chosen atlas data. -/
theorem extendToAtlasMap_equivariant {X : NormContinuousSpace K H}
    {Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (f : (localAtlasFunctor H).obj X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).obj Y)
    (g : G) :
    atlasActionMap H hH X g ≫ extendToAtlasMap H hH f =
      extendToAtlasMap H hH f ≫ Y.ρ g := by
  apply quotientAtlasHom_ext H hH
  intro c
  let f₀ : (localFamily H X).atlasPresentation ⟶ Y.V := f.hom
  have hc (d : G ⧸ H) : quotientCopyMap H hH X d ≫ extendToAtlasMap H hH f =
      f₀ ≫ Y.ρ d.out := quotientCopyMap_extendToAtlasMap H hH f d
  have hf : (localActionMap H X (correction H g c)).atlasMap ≫ f₀ =
      f₀ ≫ Y.ρ (correction H g c : G) := f.comm (correction H g c)
  calc
    quotientCopyMap H hH X c ≫ (atlasActionMap H hH X g ≫ extendToAtlasMap H hH f) =
        (localActionMap H X (correction H g c)).atlasMap ≫
          (quotientCopyMap H hH X (g • c) ≫ extendToAtlasMap H hH f) := by
            rw [← Category.assoc, quotientCopyMap_action, Category.assoc]
    _ = (localActionMap H X (correction H g c)).atlasMap ≫
        (f₀ ≫ Y.ρ (g • c).out) := by rw [hc]
    _ = (f₀ ≫ Y.ρ (correction H g c : G)) ≫ Y.ρ (g • c).out := by
      rw [← Category.assoc, hf]
    _ = f₀ ≫ Y.ρ (g * c.out) := by
      rw [Category.assoc, atlasTargetAction_comp, ← correction_spec]
    _ = quotientCopyMap H hH X c ≫ (extendToAtlasMap H hH f ≫ Y.ρ g) := by
      rw [← Category.assoc, hc, Category.assoc, atlasTargetAction_comp]

/-- The actual full-group-equivariant extension for arbitrary atlas-action targets. -/
def extendToAtlas {X : NormContinuousSpace K H}
    {Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (f : (localAtlasFunctor H).obj X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).obj Y) :
    (equivariantAtlasFunctor H hH).obj X ⟶ Y :=
  ⟨extendToAtlasMap H hH f, extendToAtlasMap_equivariant H hH f⟩

/-- The normalized-unit triangle holds for the entire bounded atlas morphism. -/
theorem unitAtlasMap_extendToAtlasMap {X : NormContinuousSpace K H}
    {Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (f : (localAtlasFunctor H).obj X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).obj Y) :
    unitAtlasMap H hH X ≫ extendToAtlasMap H hH f = f.hom := by
  let f₀ : (localFamily H X).atlasPresentation ⟶ Y.V := f.hom
  have hf : (localActionMap H X (identityRepresentative H)⁻¹).atlasMap ≫ f₀ =
      f₀ ≫ Y.ρ ((identityRepresentative H)⁻¹ : H) :=
    f.comm (identityRepresentative H)⁻¹
  have hc : quotientCopyMap H hH X (identityCoset H) ≫ extendToAtlasMap H hH f =
      f₀ ≫ Y.ρ (identityRepresentative H : G) :=
    quotientCopyMap_extendToAtlasMap H hH f (identityCoset H)
  change unitAtlasMap H hH X ≫ extendToAtlasMap H hH f = f₀
  rw [unitAtlasMap_eq_quotientCopyMap, Category.assoc, hc, ← Category.assoc, hf,
    Category.assoc, atlasTargetAction_comp]
  simp

/-- Restriction uses the already constructed natural subgroup-equivariant unit. -/
def restrictFromAtlas {X : NormContinuousSpace K H}
    {Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (p : (equivariantAtlasFunctor H hH).obj X ⟶ Y) :
    (localAtlasFunctor H).obj X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).obj Y :=
  (equivariantAtlasUnit H hH).app X ≫
    (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).map p

@[simp]
theorem restrictFromAtlas_extendToAtlas {X : NormContinuousSpace K H}
    {Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (f : (localAtlasFunctor H).obj X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).obj Y) :
    restrictFromAtlas H hH (extendToAtlas H hH f) = f :=
  Action.Hom.ext (unitAtlasMap_extendToAtlasMap H hH f)

@[simp]
theorem extendToAtlas_restrictFromAtlas {X : NormContinuousSpace K H}
    {Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (p : (equivariantAtlasFunctor H hH).obj X ⟶ Y) :
    extendToAtlas H hH (restrictFromAtlas H hH p) = p := by
  apply Action.Hom.ext
  let p₀ : atlasPresentation H hH X ⟶ Y.V := p.hom
  change extendToAtlasMap H hH (restrictFromAtlas H hH p) = p₀
  apply quotientAtlasHom_ext H hH
  intro c
  rw [quotientCopyMap_extendToAtlasMap]
  change (unitAtlasMap H hH X ≫ p₀) ≫ Y.ρ c.out =
    quotientCopyMap H hH X c ≫ p₀
  have hp : atlasActionMap H hH X c.out ≫ p₀ = p₀ ≫ Y.ρ c.out :=
    p.comm c.out
  rw [Category.assoc, ← hp, ← Category.assoc, unitAtlasMap_action]

/-- Relative induction correspondence for complete chosen bounded atlas morphisms. -/
def atlasExtensionEquiv {X : NormContinuousSpace K H}
    {Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G} :
    ((equivariantAtlasFunctor H hH).obj X ⟶ Y) ≃
      ((localAtlasFunctor H).obj X ⟶
        (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).obj Y) where
  toFun := restrictFromAtlas H hH
  invFun := extendToAtlas H hH
  left_inv := extendToAtlas_restrictFromAtlas H hH
  right_inv := restrictFromAtlas_extendToAtlas H hH

/-- Uniqueness retains chart choices and bounded maps of the original algebras. -/
theorem extendToAtlas_unique {X : NormContinuousSpace K H}
    {Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (f : (localAtlasFunctor H).obj X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).obj Y)
    (p : (equivariantAtlasFunctor H hH).obj X ⟶ Y)
    (hp : unitAtlasMap H hH X ≫ p.hom = f.hom) :
    p = extendToAtlas H hH f := by
  apply (atlasExtensionEquiv H hH).injective
  change restrictFromAtlas H hH p = restrictFromAtlas H hH (extendToAtlas H hH f)
  rw [restrictFromAtlas_extendToAtlas]
  exact Action.Hom.ext hp

/-- The relative Hom correspondence is natural in the original affinoid input. -/
theorem atlasExtensionEquiv_naturality_left {X X' : NormContinuousSpace K H}
    {Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (a : X' ⟶ X) (p : (equivariantAtlasFunctor H hH).obj X ⟶ Y) :
    atlasExtensionEquiv H hH ((equivariantAtlasFunctor H hH).map a ≫ p) =
      (localAtlasFunctor H).map a ≫ atlasExtensionEquiv H hH p := by
  apply Action.Hom.ext
  let p₀ : atlasPresentation H hH X ⟶ Y.V := p.hom
  change unitAtlasMap H hH X' ≫ (atlasMap H hH a ≫ p₀) =
    (localFamilyMap H a).atlasMap ≫ (unitAtlasMap H hH X ≫ p₀)
  rw [← Category.assoc, ← unitAtlasMap_naturality, Category.assoc]

/-- Naturality holds for every bounded equivariant arrow of atlas-action targets. -/
theorem atlasExtensionEquiv_naturality_right {X : NormContinuousSpace K H}
    {Y Z : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (p : (equivariantAtlasFunctor H hH).obj X ⟶ Y) (q : Y ⟶ Z) :
    atlasExtensionEquiv H hH (p ≫ q) =
      atlasExtensionEquiv H hH p ≫
        (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).map q := by
  apply Action.Hom.ext
  exact (Category.assoc (unitAtlasMap H hH X) p.hom q.hom).symm

/-- The constructed extension is natural in the original affinoid input. -/
theorem extendToAtlas_naturality_left {X X' : NormContinuousSpace K H}
    {Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (a : X' ⟶ X)
    (f : (localAtlasFunctor H).obj X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).obj Y) :
    extendToAtlas H hH ((localAtlasFunctor H).map a ≫ f) =
      (equivariantAtlasFunctor H hH).map a ≫ extendToAtlas H hH f := by
  apply (atlasExtensionEquiv H hH).injective
  rw [atlasExtensionEquiv_naturality_left]
  change restrictFromAtlas H hH (extendToAtlas H hH _) =
    (localAtlasFunctor H).map a ≫ restrictFromAtlas H hH (extendToAtlas H hH f)
  rw [restrictFromAtlas_extendToAtlas, restrictFromAtlas_extendToAtlas]

/-- Extension commutes with every complete equivariant atlas-target arrow. -/
theorem extendToAtlas_naturality_right {X : NormContinuousSpace K H}
    {Y Z : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (f : (localAtlasFunctor H).obj X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).obj Y)
    (q : Y ⟶ Z) :
    extendToAtlas H hH
        (f ≫ (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).map q) =
      extendToAtlas H hH f ≫ q := by
  apply (atlasExtensionEquiv H hH).injective
  rw [atlasExtensionEquiv_naturality_right]
  change restrictFromAtlas H hH (extendToAtlas H hH _) =
    restrictFromAtlas H hH (extendToAtlas H hH f) ≫
      (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).map q
  rw [restrictFromAtlas_extendToAtlas, restrictFromAtlas_extendToAtlas]

/-- The chosen chart is exactly the chosen input chart followed by the target action. -/
@[simp]
theorem extendToAtlasMap_indexMap {X : NormContinuousSpace K H}
    {Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (f : (localAtlasFunctor H).obj X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).obj Y)
    (c : (atlas H X.unop hH).Index) :
    (extendToAtlasMap H hH f).indexMap c =
      (Y.ρ c.val.out).indexMap (f.hom.indexMap ⟨PUnit.unit, c.property⟩) := rfl

/-- The original bounded algebra pullback is the actual contravariant composite. -/
@[simp]
theorem extendToAtlasMap_pullback {X : NormContinuousSpace K H}
    {Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (f : (localAtlasFunctor H).obj X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).obj Y)
    (c : (atlas H X.unop hH).Index) :
    (extendToAtlasMap H hH f).pullback c =
      (f.hom.pullback ⟨PUnit.unit, c.property⟩).comp
        ((Y.ρ c.val.out).pullback (f.hom.indexMap ⟨PUnit.unit, c.property⟩)) :=
  BoundedAlgHom.ext fun _ => rfl

/-- On every actual copy the map applies the chosen representative's target action. -/
theorem extendToAtlasMap_baseMap_copy {X : NormContinuousSpace K H}
    {Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (f : (localAtlasFunctor H).obj X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).obj Y)
    (c : G ⧸ H) (x : LocalSpectrum H X.unop) :
    (extendToAtlasMap H hH f).baseMap (spectrumHomeomorph H X.unop hH ⟨c, x⟩) =
      (Y.ρ c.out).baseMap (f.hom.baseMap ⟨PUnit.unit, x⟩) := by
  change (assembleCopyAtlasMap H (fun d => f.hom ≫ Y.ρ d.out)).baseMap
      ((spectrumHomeomorph H X.unop hH).symm
        (spectrumHomeomorph H X.unop hH ⟨c, x⟩)) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- The formula holds at every representative of the actual balanced quotient. -/
theorem extendToAtlasMap_baseMap_mk {X : NormContinuousSpace K H}
    {Y : Action (AffinoidAtlasPresentation.{u, max u v, v} K) G}
    (f : (localAtlasFunctor H).obj X ⟶
      (Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype).obj Y)
    (g : G) (x : LocalSpectrum H X.unop) :
    (extendToAtlasMap H hH f).baseMap (TopologicalInduction.mk H g x) =
      (Y.ρ g).baseMap (f.hom.baseMap ⟨PUnit.unit, x⟩) := by
  have hu := congrArg
    (fun p : (localFamily H X).atlasPresentation ⟶ Y.V =>
      p.baseMap ⟨PUnit.unit, x⟩) (unitAtlasMap_extendToAtlasMap H hH f)
  change (extendToAtlasMap H hH f).baseMap
    ((unitAtlasMap H hH X).baseMap ⟨PUnit.unit, x⟩) =
      f.hom.baseMap ⟨PUnit.unit, x⟩ at hu
  rw [unitAtlasMap_baseMap_apply] at hu
  have he := congrArg
    (fun p : atlasPresentation H hH X ⟶ Y.V =>
      p.baseMap (TopologicalInduction.unit H x)) (extendToAtlasMap_equivariant H hH f g)
  change (extendToAtlasMap H hH f).baseMap (g • TopologicalInduction.unit H x) =
    (Y.ρ g).baseMap
      ((extendToAtlasMap H hH f).baseMap (TopologicalInduction.unit H x)) at he
  simpa only [TopologicalInduction.smul_unit, hu] using he

end Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction
