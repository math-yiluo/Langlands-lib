import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceProductPointsSurjective
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartFibreCount
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Finitely presented scheme presentations of quasi-separated algebraic spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace FinitePresentationEtaleAtlas

variable {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S}

/-- An actual affine étale presentation with both scheme objects finitely presented
over the base. -/
structure Presentation (X : AlgebraicSpace S) where
  U : Over S
  R : Over S
  a : (schemeYoneda S).obj U ⟶ X.presheaf
  t : R ⟶ U
  s : R ⟶ U
  affine : IsAffine U.left
  etale : IsEtale a
  surjective : IsSurjective a
  locallyOfFinitePresentation_U : LocallyOfFinitePresentation U.hom
  quasiCompact_U : QuasiCompact U.hom
  quasiSeparated_U : QuasiSeparated U.hom
  locallyOfFinitePresentation_R : LocallyOfFinitePresentation R.hom
  quasiCompact_R : QuasiCompact R.hom
  quasiSeparated_R : QuasiSeparated R.hom
  etale_t : Etale t.left
  etale_s : Etale s.left
  kernelPair : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a

/-- Refining a quasi-compact locally finitely presented atlas by finitely many affine
opens gives an affine atlas whose structure morphism is still locally finitely presented. -/
theorem exists_affine_atlas
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X) :
    ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf),
      IsAffine U.left ∧ IsEtale a ∧ IsSurjective a ∧ LocallyOfFinitePresentation U.hom := by
  obtain ⟨W, a, ha, hs, hW⟩ := hX
  have : QuasiCompact W.hom := hW.2
  have : LocallyOfFinitePresentation W.hom := hW.1
  have : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace W.hom
  let 𝒰 := W.left.affineCover.finiteSubcover
  let J : ∐ 𝒰.X ⟶ W.left := Sigma.desc 𝒰.f
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
  have hJ : Etale J := IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance
  have hJs : Surjective J := by
    constructor
    intro x
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    exact ⟨Sigma.ι 𝒰.X i y, by rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]⟩
  let U : Over S := Over.mk (J ≫ W.hom)
  let j : U ⟶ W := Over.homMk J
  have : ∀ i, IsAffine (𝒰.X i) := fun _ => inferInstance
  have : Etale J := hJ
  refine ⟨U, (schemeYoneda S).map j ≫ a, inferInstanceAs (IsAffine (∐ 𝒰.X)),
    (isEtale_map j hJ).comp ha,
    SpaceProductPoints.IsSurjective.comp (SpaceProductPoints.isSurjective_map j hJs) hs, ?_⟩
  change LocallyOfFinitePresentation (J ≫ W.hom)
  infer_instance

/-- The relation scheme of an affine atlas of a quasi-separated space is finitely
presented over the affine base. -/
theorem exists_presentation
    (hqs : IsQuasiSeparated X)
    (hfp : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X) :
    ∃ (U R : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf) (t s : R ⟶ U),
      IsAffine U.left ∧ IsEtale a ∧ IsSurjective a ∧
      LocallyOfFinitePresentation U.hom ∧ QuasiCompact U.hom ∧ QuasiSeparated U.hom ∧
      LocallyOfFinitePresentation R.hom ∧ QuasiCompact R.hom ∧ QuasiSeparated R.hom ∧
      Etale t.left ∧ Etale s.left ∧
      IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a := by
  obtain ⟨U, a, hU, ha, hs, hUf⟩ := exists_affine_atlas hfp
  let : IsAffine U.left := hU
  let : LocallyOfFinitePresentation U.hom := hUf
  let R := FieldPointEtaleLift.selfPullback a
  let t : R ⟶ U := FieldPointEtaleLift.selfFst a
  let s : R ⟶ U := FieldPointEtaleLift.selfSnd a
  have h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a :=
    FieldPointEtaleLift.selfPullback_isPullback a
  have ht : Etale t.left := ha.projection a _ _ h.flip
  have hs' : Etale s.left := ha.projection a _ _ h
  have : CompactSpace (U ⊗ U).left := by
    change CompactSpace (Limits.pullback U.hom U.hom : Scheme.{u})
    infer_instance
  have : CompactSpace R.left := EtaleChartFibreCount.compactSpace_selfPullback a hqs
  have : Etale t.left := ht
  have : LocallyOfFinitePresentation R.hom := by
    rw [← Over.w t]
    infer_instance
  let j : R ⟶ U ⊗ U := lift t s
  have : Mono j := by
    constructor
    intro Z f g e
    apply EtaleEquivalenceRelation.hom_ext_of_isPullback h
    · simpa [j] using congrArg (· ≫ fst U U) e
    · simpa [j] using congrArg (· ≫ snd U U) e
  have : _root_.AlgebraicGeometry.IsSeparated (U ⊗ U).hom := by
    change _root_.AlgebraicGeometry.IsSeparated (Limits.pullback.fst U.hom U.hom ≫ U.hom)
    infer_instance
  have : _root_.AlgebraicGeometry.IsSeparated R.hom := by
    rw [← Over.w j]
    infer_instance
  exact ⟨U, R, a, t, s, hU, ha, hs, hUf, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ht, hs', h⟩

/-- Choose an actual finitely presented scheme presentation, using the given
quasi-separatedness and finite presentation atlas. -/
def presentation
    (hqs : IsQuasiSeparated X)
    (hfp : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X) :
    Presentation X :=
  Classical.choice (by
    obtain ⟨U, R, a, t, s, hU, ha, hs, hUf, hUq, hUs, hRf, hRq, hRs, ht, hs', h⟩ :=
      exists_presentation hqs hfp
    exact ⟨⟨U, R, a, t, s, hU, ha, hs, hUf, hUq, hUs, hRf, hRq, hRs, ht, hs', h⟩⟩)

end FinitePresentationEtaleAtlas

end Langlands.AlgebraicGeometry.AlgebraicSpace
