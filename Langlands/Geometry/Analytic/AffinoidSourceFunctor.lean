import Langlands.Geometry.Analytic.AffinoidSpectrumAtlas
import Langlands.Geometry.Analytic.CompatibleStrongOriginalRestriction
import Langlands.Geometry.Analytic.QuotientTopTargetHom

/-! # Actual affinoids embed fully faithfully in the source quotient category -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidSpace

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- With only one target chart, every complete singleton strong map satisfies
the entire coefficient-test compatibility law. -/
theorem singleton_hasCoherentPullbacks {A B : PresentedAffinoidSpace K}
    (f : AffinoidAtlasPresentation.StrongHom A.atlasPresentation B.atlasPresentation) :
    f.HasCoherentPullbacks := by
  intro i j k hj hk T η m hmj hmk α hα
  cases j
  cases k
  exact hα.symm

/-- The actual singleton atlas in the category of compatible strong maps. -/
def compatibleAtlasPresentation (A : PresentedAffinoidSpace K) :
    CompatibleAtlasPresentation.{u, u, 0} K := ⟨A.atlasPresentation⟩

/-- A bounded affinoid map with the proved singleton compatibility law. -/
def compatibleAtlasMap {A B : PresentedAffinoidSpace K} (f : A ⟶ B) :
    A.compatibleAtlasPresentation ⟶ B.compatibleAtlasPresentation where
  toStrongHom := strongAtlasMap f
  compatible := (strongAtlasMap f).hasLocallyCompatiblePullbacks_iff.mpr
    (singleton_hasCoherentPullbacks _)

/-- Complete compatible singleton maps retain precisely the original
contravariant bounded algebra maps. -/
def compatibleAtlasHomEquiv (A B : PresentedAffinoidSpace K) :
    (A ⟶ B) ≃ (A.compatibleAtlasPresentation ⟶ B.compatibleAtlasPresentation) where
  toFun := compatibleAtlasMap
  invFun f := (strongAtlasHomEquiv A B).symm f.toStrongHom
  left_inv := (strongAtlasHomEquiv A B).left_inv
  right_inv f := AffinoidAtlasPresentation.CompatibleStrongHom.ext
    ((strongAtlasHomEquiv A B).apply_symm_apply f.toStrongHom)

@[simp]
theorem compatibleAtlasMap_pullback {A B : PresentedAffinoidSpace K} (f : A ⟶ B)
    (i : A.atlasPresentation.atlas.Index)
    (h : (compatibleAtlasMap f).baseMap '' Set.range (A.atlasPresentation.atlas.chart i) ⊆
      Set.range (B.atlasPresentation.atlas.chart PUnit.unit)) :
    (compatibleAtlasMap f).pullback i PUnit.unit h = f.unop :=
  strongAtlasMap_pullback f i h

/-- The actual bounded-algebra category maps functorially to compatible
singleton atlases. -/
def compatibleAtlasFunctor :
    PresentedAffinoidSpace K ⥤ CompatibleAtlasPresentation.{u, u, 0} K where
  obj := compatibleAtlasPresentation
  map := compatibleAtlasMap
  map_id A := by
    apply AffinoidAtlasPresentation.CompatibleStrongHom.ext_of_pullback
      (ContinuousMap.ext fun x => BanachSpectrum.ext fun _ => rfl)
    intro i
    refine ⟨PUnit.unit, (compatibleAtlasMap (𝟙 A)).image_chart_top
      PUnit.unit A.atlasPresentation_top_contains i, ?_⟩
    exact (compatibleAtlasMap_pullback (𝟙 A) i _).trans (by cases i; rfl)
  map_comp {A B C} f g := by
    apply AffinoidAtlasPresentation.CompatibleStrongHom.ext_of_pullback
      (ContinuousMap.ext fun x => BanachSpectrum.ext fun _ => rfl)
    intro i
    let hf := (compatibleAtlasMap f).image_chart_top PUnit.unit
      B.atlasPresentation_top_contains i
    let hg := (compatibleAtlasMap g).image_chart_top PUnit.unit
      C.atlasPresentation_top_contains PUnit.unit
    let hfg := (compatibleAtlasMap (f ≫ g)).image_chart_top PUnit.unit
      C.atlasPresentation_top_contains i
    refine ⟨PUnit.unit, hfg, ?_⟩
    change (compatibleAtlasMap (f ≫ g)).pullback i PUnit.unit hfg =
      ((compatibleAtlasMap f).comp (compatibleAtlasMap g)).pullback i PUnit.unit _
    rw [AffinoidAtlasPresentation.CompatibleStrongHom.comp_pullback
      (compatibleAtlasMap f) (compatibleAtlasMap g) i PUnit.unit PUnit.unit hf hg]
    exact (compatibleAtlasMap_pullback (f ≫ g) i hfg).trans
      (congrArg₂ (fun (p : BoundedAlgHom K B.unop A.unop)
        (q : BoundedAlgHom K C.unop B.unop) => p.comp q)
        (compatibleAtlasMap_pullback f i hf)
        (compatibleAtlasMap_pullback g PUnit.unit hg)).symm

/-- Explicit full recovery of compatible singleton morphisms. -/
def compatibleAtlasFullyFaithful : (compatibleAtlasFunctor (K := K)).FullyFaithful where
  preimage f := (compatibleAtlasHomEquiv _ _).symm f
  map_preimage f := (compatibleAtlasHomEquiv _ _).apply_symm_apply f
  preimage_map f := (compatibleAtlasHomEquiv _ _).symm_apply_apply f

instance : (compatibleAtlasFunctor (K := K)).Full := compatibleAtlasFullyFaithful.full
instance : (compatibleAtlasFunctor (K := K)).Faithful := compatibleAtlasFullyFaithful.faithful

/-- Compatible singleton realization retains the actual spectrum functor. -/
theorem compatibleAtlasFunctor_spaceFunctor :
    compatibleAtlasFunctor (K := K) ⋙ CompatibleAtlasPresentation.spaceFunctor =
      affinoidSpectrumFunctor K := rfl

/-- Enlarge the singleton atlases by their actual local affinoid domains
and extend every bounded map by the constructed saturation. -/
def saturatedAtlasFunctor :
    PresentedAffinoidSpace K ⥤ SaturatedAtlasPresentation.{u, u, u} K :=
  compatibleAtlasFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor

/-- The constructed saturated singleton presentation. -/
abbrev saturatedAtlasPresentation (A : PresentedAffinoidSpace K) :
    SaturatedAtlasPresentation.{u, u, u} K := saturatedAtlasFunctor.obj A

/-- Every enlarged chart lies in the original whole spectrum chart. -/
theorem saturatedAtlasPresentation_top_contains (A : PresentedAffinoidSpace K)
    (S : A.saturatedAtlasPresentation.presentation.atlas.Index) :
    Set.range (A.saturatedAtlasPresentation.presentation.atlas.chart S) ⊆
      Set.range (A.saturatedAtlasPresentation.presentation.atlas.chart
        (A.atlasPresentation.atlas.originalSaturatedIndex PUnit.unit)) := by
  change Set.range (A.atlasPresentation.atlas.saturatedAtlas.chart S) ⊆
    Set.range (A.atlasPresentation.atlas.saturatedAtlas.chart
      (A.atlasPresentation.atlas.originalSaturatedIndex PUnit.unit))
  intro x _
  exact (A.atlasPresentation.atlas.saturatedAtlas_original_range PUnit.unit).superset
    ⟨x, rfl⟩

/-- Saturation is fully reversible on these complete actual Hom types. -/
def saturatedAtlasHomEquiv (A B : PresentedAffinoidSpace K) :
    (A ⟶ B) ≃ (A.saturatedAtlasPresentation ⟶ B.saturatedAtlasPresentation) :=
  (compatibleAtlasHomEquiv A B).trans
    AffinoidAtlasPresentation.CompatibleStrongHom.saturationExtensionEquiv

@[simp]
theorem saturatedAtlasHomEquiv_apply {A B : PresentedAffinoidSpace K} (f : A ⟶ B) :
    saturatedAtlasHomEquiv A B f = saturatedAtlasFunctor.map f := rfl

/-- The inverse reads the entire original bounded map by transporting the
enlarged original-chart pullback to the literal affinoid algebra types. -/
theorem saturatedAtlasHomEquiv_symm_unop {A B : PresentedAffinoidSpace K}
    (F : A.saturatedAtlasPresentation ⟶ B.saturatedAtlasPresentation) :
    ((saturatedAtlasHomEquiv A B).symm F).unop =
      F.originalPullback PUnit.unit PUnit.unit
        (F.originalRestriction.toStrongHom.image_chart_top PUnit.unit
          B.atlasPresentation_top_contains PUnit.unit) := rfl

/-- Enlarging the singleton atlas preserves its actual spectrum diagram. -/
theorem saturatedAtlasFunctor_spaceFunctor :
    saturatedAtlasFunctor (K := K) ⋙ SaturatedAtlasPresentation.spaceFunctor =
      affinoidSpectrumFunctor K := rfl

/-- Send actual bounded affinoid maps to their source-refinement quotient
classes after constructing the saturated singleton atlases. -/
def sourceFunctor :
    PresentedAffinoidSpace K ⥤ SaturatedAtlasPresentation.SourceCategory.{u, u, u} K :=
  saturatedAtlasFunctor ⋙ SaturatedAtlasPresentation.SourceCategory.strongFunctor

/-- The full source quotient Hom is computed by the actual original
bounded algebra maps, without a point-map faithfulness assumption. -/
def sourceHomEquiv (A B : PresentedAffinoidSpace K) :
    (A ⟶ B) ≃ (sourceFunctor.obj A ⟶ sourceFunctor.obj B) :=
  (saturatedAtlasHomEquiv A B).trans
    (SaturatedAtlasPresentation.SourceCategory.topTargetHomEquiv
      (B.atlasPresentation.atlas.originalSaturatedIndex PUnit.unit)
      B.saturatedAtlasPresentation_top_contains)

@[simp]
theorem sourceHomEquiv_apply {A B : PresentedAffinoidSpace K} (f : A ⟶ B) :
    sourceHomEquiv A B f = sourceFunctor.map f := rfl

/-- Every quotient arrow recovers its complete original bounded map from
the uniquely extended global strong map, including on nonreduced algebras. -/
theorem sourceHomEquiv_symm_unop {A B : PresentedAffinoidSpace K}
    (F : sourceFunctor.obj A ⟶ sourceFunctor.obj B) :
    let G : A.saturatedAtlasPresentation ⟶ B.saturatedAtlasPresentation :=
      (SaturatedAtlasPresentation.SourceCategory.topTargetHomEquiv
      (A := A.saturatedAtlasPresentation) (B := B.saturatedAtlasPresentation)
      (B.atlasPresentation.atlas.originalSaturatedIndex PUnit.unit)
      B.saturatedAtlasPresentation_top_contains).symm F
    ((sourceHomEquiv A B).symm F).unop =
      G.originalPullback PUnit.unit PUnit.unit
        (G.originalRestriction.toStrongHom.image_chart_top PUnit.unit
          B.atlasPresentation_top_contains PUnit.unit) := rfl

/-- The quotient map still induces precisely the actual continuous
contravariant spectrum map. -/
theorem sourceFunctor_map_spaceFunctor {A B : PresentedAffinoidSpace K} (f : A ⟶ B) :
    SaturatedAtlasPresentation.SourceCategory.spaceFunctor.map (sourceFunctor.map f) =
      (affinoidSpectrumFunctor K).map f :=
  SaturatedAtlasPresentation.SourceCategory.spaceFunctor_map_strong
    (saturatedAtlasFunctor.map f)

/-- The full functor to the source quotient preserves the spectrum diagram. -/
theorem sourceFunctor_spaceFunctor :
    sourceFunctor (K := K) ⋙ SaturatedAtlasPresentation.SourceCategory.spaceFunctor =
      affinoidSpectrumFunctor K := by
  change saturatedAtlasFunctor ⋙
    (SaturatedAtlasPresentation.SourceCategory.strongFunctor ⋙
      SaturatedAtlasPresentation.SourceCategory.spaceFunctor) = _
  rw [SaturatedAtlasPresentation.SourceCategory.strongFunctor_spaceFunctor]
  rfl

/-- Recovery of the bounded map preserves the given quotient arrow's
entire continuous map. -/
theorem sourceHomEquiv_symm_spaceMap {A B : PresentedAffinoidSpace K}
    (F : sourceFunctor.obj A ⟶ sourceFunctor.obj B) :
    (affinoidSpectrumFunctor K).map ((sourceHomEquiv A B).symm F) =
      SaturatedAtlasPresentation.SourceCategory.spaceFunctor.map F :=
  (sourceFunctor_map_spaceFunctor _).symm.trans
    (congrArg (fun q : sourceFunctor.obj A ⟶ sourceFunctor.obj B =>
      SaturatedAtlasPresentation.SourceCategory.spaceFunctor.map q)
        ((sourceHomEquiv A B).apply_symm_apply F))

/-- Full inverse recovery sends quotient identities to the original bounded
identity maps. -/
@[simp]
theorem sourceHomEquiv_symm_id (A : PresentedAffinoidSpace K) :
    (sourceHomEquiv A A).symm (𝟙 (sourceFunctor.obj A)) = 𝟙 A := by
  apply (sourceHomEquiv A A).injective
  exact ((sourceHomEquiv A A).apply_symm_apply _).trans
    (sourceFunctor.map_id A).symm

/-- Full inverse recovery computes quotient composition as actual bounded
affinoid composition. -/
theorem sourceHomEquiv_symm_comp {A B C : PresentedAffinoidSpace K}
    (F : sourceFunctor.obj A ⟶ sourceFunctor.obj B)
    (G : sourceFunctor.obj B ⟶ sourceFunctor.obj C) :
    (sourceHomEquiv A C).symm (F ≫ G) =
      (sourceHomEquiv A B).symm F ≫ (sourceHomEquiv B C).symm G := by
  apply (sourceHomEquiv A C).injective
  exact ((sourceHomEquiv A C).apply_symm_apply _).trans
    ((congrArg₂ (fun (p : sourceFunctor.obj A ⟶ sourceFunctor.obj B)
      (q : sourceFunctor.obj B ⟶ sourceFunctor.obj C) => p ≫ q)
      ((sourceHomEquiv A B).apply_symm_apply F).symm
      ((sourceHomEquiv B C).apply_symm_apply G).symm).trans
        (sourceFunctor.map_comp ((sourceHomEquiv A B).symm F)
          ((sourceHomEquiv B C).symm G)).symm)

/-- An explicit inverse on every source-quotient arrow proves fullness and
faithfulness of the actual affinoid realization. -/
def sourceFullyFaithful : (sourceFunctor (K := K)).FullyFaithful where
  preimage f := (sourceHomEquiv _ _).symm f
  map_preimage f := (sourceHomEquiv _ _).apply_symm_apply f
  preimage_map f := (sourceHomEquiv _ _).symm_apply_apply f

instance : (sourceFunctor (K := K)).Full := sourceFullyFaithful.full
instance : (sourceFunctor (K := K)).Faithful := sourceFullyFaithful.faithful

end Langlands.Analytic.PresentedAffinoidSpace
