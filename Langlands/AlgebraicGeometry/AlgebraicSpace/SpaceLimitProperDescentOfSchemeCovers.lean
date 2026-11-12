import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCoverDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.EventualTargetAtlasDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothChartLimitDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitConnectedFibresDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineTargetFamilyUniversallyClosedBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeDiagonalLimitDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChangeMorphismComparison
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionLimits

/-! # Properness descent reduced to the independent proper scheme cover theorem -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Separatedness is invariant under an actual isomorphism of space arrows. -/
theorem IsSeparatedMorphism.of_arrow_iso
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X ≅ X') (eY : Y ≅ Y') (w : eX.hom ≫ f' = f ≫ eY.hom)
    (hf : IsSeparatedMorphism f) : IsSeparatedMorphism f' := by
  let P := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
    (Over.forget S)).relative (schemeYoneda S)
  exact (MorphismProperty.arrow_mk_iso_iff P.diagonal
    (Arrow.isoMk ((forgetToPresheaf S).mapIso eX) ((forgetToPresheaf S).mapIso eY)
      ((forgetToPresheaf S).congr_map w))).mp hf

/-- Properness is invariant under an actual isomorphism of space arrows. -/
theorem IsProperMorphism.of_arrow_iso
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X ≅ X') (eY : Y ≅ Y') (w : eX.hom ≫ f' = f ≫ eY.hom)
    (hf : IsProperMorphism f) : IsProperMorphism f' :=
  ⟨hf.1.of_arrow_iso eX eY w, hf.2.1.of_arrow_iso eX eY w,
    hf.2.2.1.of_arrow_iso eX eY w, hf.2.2.2.of_arrow_iso eX eY w⟩

/-- Structural universal closedness is unchanged by an isomorphism of the space. -/
theorem IsUniversallyClosedMorphism.structural_of_iso
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (hf : IsUniversallyClosedMorphism (structuralMorphism X)) (e : X ≅ Y) :
    IsUniversallyClosedMorphism (structuralMorphism Y) := by
  apply IsUniversallyClosedMorphism.of_arrow_iso e (Iso.refl _) _ hf
  apply (homEquiv _ _).injective
  exact (basePresheafIsTerminal S).hom_ext _ _

/-- Structural universal closedness is preserved by change of scheme base. -/
theorem IsUniversallyClosedMorphism.structural_baseChange
    {S T : Scheme.{u}} {X : AlgebraicSpace S}
    (hf : IsUniversallyClosedMorphism (structuralMorphism X)) (g : T ⟶ S) :
    IsUniversallyClosedMorphism (structuralMorphism (baseChange g X)) := by
  apply IsUniversallyClosedMorphism.of_arrow_iso (Iso.refl _) (restrictedBaseIso g).symm _
    (hf.baseChangeMap (g := g))
  apply (homEquiv _ _).injective
  exact (basePresheafIsTerminal T).hom_ext _ _

/-- Structural separatedness is preserved by change of scheme base. -/
theorem IsSeparatedMorphism.structural_baseChange
    {S T : Scheme.{u}} {X : AlgebraicSpace S}
    (hf : IsSeparatedMorphism (structuralMorphism X)) (g : T ⟶ S) :
    IsSeparatedMorphism (structuralMorphism (baseChange g X)) := by
  apply IsSeparatedMorphism.of_arrow_iso (Iso.refl _) (restrictedBaseIso g).symm _
    (hf.baseChangeMap (g := g))
  apply (homEquiv _ _).injective
  exact (basePresheafIsTerminal T).hom_ext _ _

/-- Swap the order of a scheme pullback while retaining the same structural family. -/
def structuralPullbackSymmetrySpaceIso {S A B : Scheme.{u}}
    (a : A ⟶ S) (b : B ⟶ S) (X : AlgebraicSpace A) :
    baseChange (pullbackSymmetry b a).hom (baseChange (pullback.fst a b) X) ≅
      baseChange (pullback.snd b a) X :=
  (baseChangeCompNatIso (pullback.fst a b) (pullbackSymmetry b a).hom
    (pullback.snd b a) (pullbackSymmetry_hom_comp_fst b a)).app X

/-- The two orders of the scheme base pullback test the same structural universal closedness. -/
theorem structuralUniversallyClosed_pullbackSymmetry_iff {S A B : Scheme.{u}}
    (a : A ⟶ S) (b : B ⟶ S) (X : AlgebraicSpace A) :
    IsUniversallyClosedMorphism (structuralMorphism (baseChange (pullback.fst a b) X)) ↔
      IsUniversallyClosedMorphism (structuralMorphism (baseChange (pullback.snd b a) X)) := by
  constructor
  · intro h
    exact (h.structural_baseChange (pullbackSymmetry b a).hom).structural_of_iso
      (structuralPullbackSymmetrySpaceIso a b X)
  · intro h
    let e := (baseChangeCompNatIso (pullback.snd b a) (pullbackSymmetry b a).inv
      (pullback.fst a b) (pullbackSymmetry_inv_comp_snd b a)).app X
    exact (h.structural_baseChange (pullbackSymmetry b a).inv).structural_of_iso e

/-- With separatedness at the original stage, a proper scheme cover of the actual
limit target family gives properness at an incoming stage. -/
theorem exists_proper_baseChange_of_separated_of_schemeCovers
    (hcover : ProperSchemeCoverStatement.{u})
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X Y : AlgebraicSpace (D.obj i)}
    (hXqs : IsQuasiSeparated X)
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hYqs : IsQuasiSeparated Y)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (f : X ⟶ Y) (hsep : IsSeparatedMorphism f)
    (hproper : IsProperMorphism (baseChangeMap (c.π.app i) f)) :
    ∃ (j : I) (r : j ⟶ i), IsProperMorphism (baseChangeMap (D.map r) f) := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  obtain ⟨V, b, hVa, hb, hs, hVl⟩ := exists_affine_finitePresentation_atlas Y hY
  let := hVa
  let := hVl
  let F := AffineTargetFamily.space f b
  have hFqs : IsQuasiSeparated F := AffineTargetFamily.isQuasiSeparated f b hXqs
  have hF : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) F :=
    AffineTargetFamily.hasAtlasProperty_finitePresentation f b hX hY hYqs
  let pf := FibreProduct.snd f (homMk b : (schemeToSpace (D.obj i)).obj V ⟶ Y)
  have hFS : IsSeparatedMorphism (structuralMorphism F) :=
    SchemeTargetRebase.isSeparatedMorphism pf
      (IsSeparatedMorphism.of_isPullback (FibreProduct.isPullback_presheaf f
        (homMk b : (schemeToSpace (D.obj i)).obj V ⟶ Y)) hsep)
  let E := TargetLimit.diagram (SpaceFilteredPoints.overDiagram D i)
    (SpaceFilteredPoints.overStructure D i) V.hom
  let t : E ⟶ (Functor.const (Over i)).obj V.left :=
    TargetLimit.comparison (SpaceFilteredPoints.overDiagram D i)
      (SpaceFilteredPoints.overStructure D i) V.hom
  let p := c.π.app i
  let C := TargetLimit.coneOfPullback (SpaceFilteredPoints.overDiagram D i)
    (SpaceFilteredPoints.overStructure D i) V.hom (c.whisker (Over.forget i)) p
    (SpaceFilteredPoints.overCone_π_comp i c) (IsPullback.of_hasPullback p V.hom)
  have hC : IsLimit C := TargetLimit.isLimitConeOfPullback _ _ _ _ _ _ _
    (SpaceFilteredPoints.overConeIsLimit i c hc)
  have (j : Over i) : IsAffine (E.obj j) := by
    change IsAffine (Limits.pullback (D.map j.hom) V.hom)
    infer_instance
  have hCaff : IsAffine C.pt := Scheme.isAffine_of_isLimit C hC
  have : IsAffine (Limits.pullback p V.hom) := hCaff
  have hlimUC : IsUniversallyClosedMorphism
      (structuralMorphism (baseChange (pullback.snd p V.hom) F)) :=
    (structuralUniversallyClosed_pullbackSymmetry_iff V.hom p F).mp
      ((AffineTargetFamily.isUniversallyClosedMorphism_baseChange_iff f b p hb hs).mp
        hproper.2.2.2)
  have hlimProper : IsProperMorphism
      (structuralMorphism (baseChange (pullback.snd p V.hom) F)) := by
    have : LocallyOfFinitePresentation (Over.mk (𝟙 C.pt)).hom :=
      inferInstanceAs (LocallyOfFinitePresentation (𝟙 C.pt))
    have : QuasiCompact (Over.mk (𝟙 C.pt)).hom := inferInstanceAs (QuasiCompact (𝟙 C.pt))
    have : QuasiSeparated (Over.mk (𝟙 C.pt)).hom := inferInstanceAs (QuasiSeparated (𝟙 C.pt))
    apply (isProperMorphism_iff_separated_universallyClosed
      (hF.baseChange (g := pullback.snd p V.hom))
      (HasAtlasProperty.of_scheme (Over.mk (𝟙 C.pt)) ⟨inferInstance, inferInstance⟩)
      (isQuasiSeparated_schemeToSpace (Over.mk (𝟙 C.pt))) _).mpr
    exact ⟨hFS.structural_baseChange _, hlimUC⟩
  obtain ⟨j, hj⟩ := exists_structuralUniversallyClosed_of_properSchemeCover hcover
    E t C hC (pullback.snd p V.hom)
    (fun j => TargetLimit.coneOfPullback_π_snd _ _ _ _ _ _ _ _) F hFqs hF hlimProper
  have hstageUC : IsUniversallyClosedMorphism (baseChangeMap (D.map j.hom) f) :=
    (AffineTargetFamily.isUniversallyClosedMorphism_baseChange_iff f b (D.map j.hom) hb hs).mpr
      ((structuralUniversallyClosed_pullbackSymmetry_iff V.hom (D.map j.hom) F).mpr hj)
  exact ⟨j.left, j.hom,
    (isProperMorphism_baseChangeMap_iff_separated_universallyClosed
      (D.map j.hom) hX hY hYqs f).mpr ⟨hsep.baseChangeMap, hstageUC⟩⟩

/-- The full properness clause of the host limit theorem, conditional only on
the independent proper finite-presentation scheme-cover existence theorem. -/
theorem spaceLimitProperDescent_of_schemeCovers
    (hcover : ProperSchemeCoverStatement.{u}) :
    SpaceLimitPropertyDescends.{u} (fun f => IsProperMorphism f) := by
  intro I _ _ D _ c hc i X Y hXqs hX hYqs hY f
  constructor
  · intro hf
    obtain ⟨j, r, hj⟩ :=
      (spaceLimitSeparatedDescent I D c hc i X Y hXqs hX hYqs hY f).mp hf.1
    let e := baseChangeCompNatIso (D.map r) (c.π.app j) (c.π.app i) (c.w r)
    have hproper : IsProperMorphism (baseChangeMap (c.π.app j) (baseChangeMap (D.map r) f)) :=
      hf.of_arrow_iso (e.symm.app X) (e.symm.app Y) (e.inv.naturality f).symm
    obtain ⟨k, s, hk⟩ := exists_proper_baseChange_of_separated_of_schemeCovers hcover
      D c hc j (hXqs.baseChange (g := D.map r)) (hX.baseChange (g := D.map r))
      (hYqs.baseChange (g := D.map r)) (hY.baseChange (g := D.map r))
      (baseChangeMap (D.map r) f) hj hproper
    let e' := baseChangeCompNatIso (D.map r) (D.map s) (D.map (s ≫ r)) (D.map_comp s r).symm
    exact ⟨k, s ≫ r, hk.of_arrow_iso (e'.app X) (e'.app Y) (e'.hom.naturality f).symm⟩
  · rintro ⟨j, r, hj⟩
    let e := baseChangeCompNatIso (D.map r) (c.π.app j) (c.π.app i) (c.w r)
    exact (hj.baseChangeMap (g := c.π.app j)).of_arrow_iso
      (e.app X) (e.app Y) (e.hom.naturality f).symm

/-- All eight original clauses follow from the two independently stated foundational
inputs. Neither foundational proposition is proved by this reduction. -/
theorem spaceLimitPropertyDescent_of_foundations
    (heff : RepresentedAtlasEffectivityStatement.{u})
    (hcover : ProperSchemeCoverStatement.{u}) : SpaceLimitPropertyDescentStatement.{u} :=
  ⟨spaceLimitClosedImmersionDescent_of_modelUniqueness spaceLimitModelUniqueness heff.1,
    spaceLimitSeparatedDescent, spaceLimitProperDescent_of_schemeCovers hcover,
    spaceLimitSmoothDescent,
    spaceLimitAffineDescent_of_modelUniqueness spaceLimitModelUniqueness heff.2.1,
    spaceLimitOpenImmersionDescent_of_modelUniqueness spaceLimitModelUniqueness heff.2.2.1,
    spaceLimitFiniteDescent_of_modelUniqueness spaceLimitModelUniqueness heff.2.2.2,
    spaceLimitGeometricallyConnectedFibresDescent⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
