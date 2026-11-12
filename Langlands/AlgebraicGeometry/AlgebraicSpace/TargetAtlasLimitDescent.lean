import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedAtlasEffectivityStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedChartLimitDescent

/-! # Limit descent from an actual scheme pullback over a target atlas -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S T : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- An actual scheme pullback over one surjective étale target atlas.
No representability of the original morphism is included in these data. -/
structure SchemeTargetAtlas (f : X ⟶ Y) where
  source : Over S
  target : Over S
  sourceMap : (schemeYoneda S).obj source ⟶ X.presheaf
  targetMap : (schemeYoneda S).obj target ⟶ Y.presheaf
  schemeMap : source ⟶ target
  targetEtale : IsEtale targetMap
  targetSurjective : IsSurjective targetMap
  square : IsPullback sourceMap ((schemeYoneda S).map schemeMap) (hom f) targetMap

namespace SchemeTargetAtlas

variable {f : X ⟶ Y}

/-- A whole-presheaf representation of the pullback constructs an actual
scheme target-atlas square, including its scheme projection. -/
def of_presheafIso {W : AlgebraicSpace S} {V : Over S}
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf)
    (hb : IsEtale b) (hs : IsSurjective b)
    (p : W.presheaf ⟶ X.presheaf) (q : W.presheaf ⟶ (schemeYoneda S).obj V)
    (h : IsPullback p q (hom f) b)
    (U : Over S) (e : W.presheaf ≅ (schemeYoneda S).obj U) :
    SchemeTargetAtlas f where
  source := U
  target := V
  sourceMap := e.inv ≫ p
  targetMap := b
  schemeMap := (schemeYoneda S).preimage (e.inv ≫ q)
  targetEtale := hb
  targetSurjective := hs
  square := by
    apply h.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simp
    · simp

variable (a : SchemeTargetAtlas f)

/-- Scheme base change preserves the whole target-atlas square. -/
def baseChange (g : T ⟶ S) : SchemeTargetAtlas (baseChangeMap g f) where
  source := (Over.pullback g).obj a.source
  target := (Over.pullback g).obj a.target
  sourceMap := restrictAtlas g a.sourceMap
  targetMap := restrictAtlas g a.targetMap
  schemeMap := (Over.pullback g).map a.schemeMap
  targetEtale := relative_restrictAtlas _ a.targetEtale
  targetSurjective := relative_restrictAtlas _ a.targetSurjective
  square := by
    apply (a.square.map (restrictPresheaf g)).of_iso'
      (schemeYonedaBaseChangeIso g a.source) (Iso.refl _)
      (schemeYonedaBaseChangeIso g a.target) (Iso.refl _)
    · simp [restrictAtlas]
    · exact ((schemeYonedaBaseChangeNatIso g).hom.naturality a.schemeMap).symm
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl
    · simp [restrictAtlas]

/-- Effective descent, supplied explicitly, tests the relative property on
this one scheme pullback without prior representability of the space map. -/
theorem property_iff
    (P : MorphismProperty Scheme.{u}) (heff : EtaleAtlasPropertyEffectivity P) :
    (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S)
        (hom f) ↔ P a.schemeMap.left := by
  constructor
  · intro hf
    exact hf.2 a.targetMap a.sourceMap a.schemeMap a.square
  · exact heff S X Y f a.source a.target a.sourceMap a.targetMap
      a.schemeMap a.targetEtale a.targetSurjective a.square

/-- The same scheme map tests the property after any base change. -/
theorem property_baseChange_iff
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (heff : EtaleAtlasPropertyEffectivity P) (g : T ⟶ S) :
    (MorphismProperty.inverseImage P (Over.forget T)).relative (schemeYoneda T)
        (hom (baseChangeMap g f)) ↔
      P (AffineLimit.baseChangeMap a.source.hom a.target.hom a.schemeMap.left
        (Over.w a.schemeMap) g) := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact ((a.baseChange g).property_iff P heff).trans
    (MorphismProperty.arrow_mk_iso_iff P (overPullbackSchemeArrowIso a.schemeMap g))

/-- A finite-presentation scheme pullback over one target atlas suffices for
limit descent, conditional only on the displayed scheme descent and
effective-descent inputs. -/
theorem property_limit_iff
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (heff : EtaleAtlasPropertyEffectivity P)
    (hP : SchemeStructuralPropertyDescent P)
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X Y : AlgebraicSpace (D.obj i)} {f : X ⟶ Y} (a : SchemeTargetAtlas f)
    [LocallyOfFinitePresentation a.source.hom] [QuasiCompact a.source.hom]
    [QuasiSeparated a.source.hom] [LocallyOfFinitePresentation a.target.hom]
    [QuasiCompact a.target.hom] [QuasiSeparated a.target.hom] :
    (MorphismProperty.inverseImage P (Over.forget c.pt)).relative (schemeYoneda c.pt)
        (hom (baseChangeMap (c.π.app i) f)) ↔
      ∃ (j : I) (r : j ⟶ i),
        (MorphismProperty.inverseImage P (Over.forget (D.obj j))).relative
          (schemeYoneda (D.obj j)) (hom (baseChangeMap (D.map r) f)) := by
  let E := Over.forget i ⋙ D
  let t : E ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app := fun j => D.map j.hom
      naturality := by
        intro j k r
        change D.map r.left ≫ D.map k.hom = D.map j.hom ≫ 𝟙 _
        rw [← D.map_comp, Over.w r, Category.comp_id] }
  have (j : Over i) : IsAffine (E.obj j) := by dsimp [E]; infer_instance
  let c' := c.whisker (Over.forget i)
  have hc' : IsLimit c' :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  have hdesc := hP E t a.source.hom a.target.hom a.schemeMap.left
    (Over.w a.schemeMap) c' hc' (c.π.app i) (fun j => c.w j.hom)
  constructor
  · intro hf
    obtain ⟨j, hj⟩ :=
      hdesc.mp ((a.property_baseChange_iff P heff (c.π.app i)).mp hf)
    exact ⟨j.left, j.hom, (a.property_baseChange_iff P heff (D.map j.hom)).mpr hj⟩
  · rintro ⟨j, r, hj⟩
    have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact relative_baseChangeMap_of_stage D c r f P hj

end SchemeTargetAtlas

end Langlands.AlgebraicGeometry.AlgebraicSpace
