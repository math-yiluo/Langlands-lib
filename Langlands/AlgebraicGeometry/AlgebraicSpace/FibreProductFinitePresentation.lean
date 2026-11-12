import Langlands.AlgebraicGeometry.AlgebraicSpace.FibreProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.TripleChartPullback
import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationChartSquares
import Langlands.AbelianScheme.TorsionFiniteEtale

/-! # Finite-presentation atlases for actual fibre products -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

local instance fibreProductEtaleComposition : MorphismProperty.IsStableUnderComposition (@Etale.{u}) :=
  (inferInstance : MorphismProperty.IsMultiplicative (@Etale.{u})).toIsStableUnderComposition

local instance fibreProductSurjectiveComposition : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
  (inferInstance : MorphismProperty.IsMultiplicative (@Surjective.{u})).toIsStableUnderComposition

local instance fibreProductEtaleRespectsIso : MorphismProperty.RespectsIso (@Etale.{u}) :=
  Etale.etale_isStableUnderBaseChange.respectsIso

local instance fibreProductOverSurjectiveComposition {S : Scheme.{u}} :
    (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).IsStableUnderComposition :=
  MorphismProperty.IsStableUnderComposition.inverseImage (Over.forget S)

namespace FibreProductFinitePresentation

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Z) (g : Y ⟶ Z)
  {U V C : Over S}
  (a : (schemeYoneda S).obj U ⟶ X.presheaf)
  (b : (schemeYoneda S).obj V ⟶ Y.presheaf)
  (c : (schemeYoneda S).obj C ⟶ Z.presheaf)

/-- The common target chart pulled back to the source chart of `X`. -/
abbrev leftScheme : Over S := (Z.representable_from_scheme c).pullback (a ≫ hom f)

/-- The common target chart pulled back to the source chart of `Y`. -/
abbrev rightScheme : Over S := (Z.representable_from_scheme c).pullback (b ≫ hom g)

abbrev leftToChart : leftScheme f a c ⟶ C :=
  Functor.relativelyRepresentable.fst' (Z.representable_from_scheme c) (a ≫ hom f)

abbrev leftToSource : leftScheme f a c ⟶ U :=
  (Z.representable_from_scheme c).snd (a ≫ hom f)

abbrev rightToChart : rightScheme g b c ⟶ C :=
  Functor.relativelyRepresentable.fst' (Z.representable_from_scheme c) (b ≫ hom g)

abbrev rightToSource : rightScheme g b c ⟶ V :=
  (Z.representable_from_scheme c).snd (b ≫ hom g)

/-- The actual scheme `(C ×_Z U) ×_C (C ×_Z V)`. -/
abbrev scheme : Over S := Limits.pullback (leftToChart f a c) (rightToChart g b c)

theorem leftSquare : IsPullback ((schemeYoneda S).map (leftToChart f a c))
    ((schemeYoneda S).map (leftToSource f a c)) c (a ≫ hom f) :=
  Functor.relativelyRepresentable.isPullback' (Z.representable_from_scheme c) (a ≫ hom f)

theorem rightSquare : IsPullback ((schemeYoneda S).map (rightToChart g b c))
    ((schemeYoneda S).map (rightToSource g b c)) c (b ≫ hom g) :=
  Functor.relativelyRepresentable.isPullback' (Z.representable_from_scheme c) (b ≫ hom g)

theorem middleSquare :
    IsPullback ((schemeYoneda S).map (Limits.pullback.fst (leftToChart f a c) (rightToChart g b c)))
      ((schemeYoneda S).map (Limits.pullback.snd (leftToChart f a c) (rightToChart g b c)))
      ((schemeYoneda S).map (leftToChart f a c))
      ((schemeYoneda S).map (rightToChart g b c)) :=
  (IsPullback.of_hasPullback _ _).map (schemeYoneda S)

/-- The represented square defining the first, two-chart atlas scheme. -/
theorem targetSquare :
    IsPullback
      ((schemeYoneda S).map (Functor.relativelyRepresentable.fst'
        (Z.representable_from_scheme (a ≫ hom f)) (b ≫ hom g)))
      ((schemeYoneda S).map ((Z.representable_from_scheme (a ≫ hom f)).snd (b ≫ hom g)))
      (a ≫ hom f) (b ≫ hom g) :=
  Functor.relativelyRepresentable.isPullback'
    (Z.representable_from_scheme (a ≫ hom f)) (b ≫ hom g)

/-- The scheme map from the common-chart refinement to the two-chart atlas scheme. -/
def toAtlas : scheme f g a b c ⟶ FibreProduct.atlasScheme (f := f) (g := g) a b :=
  (schemeYoneda S).preimage
    (TripleChartPullback.map (leftSquare f a c) (rightSquare g b c)
      (middleSquare f g a b c) (targetSquare f g a b))

/-- The common target-chart projection. -/
abbrev toChart : scheme f g a b c ⟶ C :=
  Limits.pullback.fst (leftToChart f a c) (rightToChart g b c) ≫ leftToChart f a c

/-- The refinement map is the actual represented base change of the target atlas. -/
theorem refinementSquare :
    IsPullback ((schemeYoneda S).map (toAtlas f g a b c))
      ((schemeYoneda S).map (toChart f g a b c))
      ((schemeYoneda S).map (Functor.relativelyRepresentable.fst'
        (Z.representable_from_scheme (a ≫ hom f)) (b ≫ hom g)) ≫ (a ≫ hom f)) c := by
  simpa only [toAtlas, Functor.map_preimage, toChart, Functor.map_comp] using
    TripleChartPullback.isPullback (leftSquare f a c) (rightSquare g b c)
      (middleSquare f g a b c) (targetSquare f g a b)

/-- The actual scheme atlas map to the constructed algebraic space. -/
def atlas : (schemeYoneda S).obj (scheme f g a b c) ⟶ (fibreProduct f g).presheaf :=
  (schemeYoneda S).map (toAtlas f g a b c) ≫
    FibreProduct.atlasMap a b ≫ (FibreProduct.presheafIso f g).inv

theorem atlas_isEtale (ha : IsEtale a) (hb : IsEtale b) (hc : IsEtale c) :
    IsEtale (atlas f g a b c) := by
  have he : Etale (toAtlas f g a b c).left :=
    hc.projection _ _ _ (refinementSquare f g a b c).flip
  exact ((isEtale_map _ he).comp
    (FibreProduct.relative_atlasMap (@Etale.{u}) ha hb)).comp_iso
      (FibreProduct.presheafIso f g).symm

theorem atlas_isSurjective (ha : IsSurjective a) (hb : IsSurjective b)
    (hc : IsSurjective c) : IsSurjective (atlas f g a b c) := by
  have he : Surjective (toAtlas f g a b c).left :=
    hc.projection _ _ _ (refinementSquare f g a b c).flip
  have : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget S)).IsStableUnderBaseChange := isStableUnderBaseChange_inverseImage_forget
  have hm : IsSurjective ((schemeYoneda S).map (toAtlas f g a b c)) :=
    MorphismProperty.relative_map
      (P := MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)) he
  have hcmp : IsSurjective ((schemeYoneda S).map (toAtlas f g a b c) ≫
      FibreProduct.atlasMap a b) := MorphismProperty.comp_mem
    (W := (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
      (schemeYoneda S)) _ _ hm (FibreProduct.relative_atlasMap (@Surjective.{u}) ha hb)
  change @IsSurjective S _ (FibreProduct.sheaf f g).obj
    ((schemeYoneda S).map (toAtlas f g a b c) ≫
      FibreProduct.atlasMap a b ≫ (FibreProduct.presheafIso f g).inv)
  rw [← Category.assoc]
  exact hcmp.comp_iso (FibreProduct.presheafIso f g).symm

/-- Local finite presentation of the three original atlas schemes implies local finite
presentation of the common-chart refinement. -/
theorem locallyOfFinitePresentation (hc : IsEtale c)
    [LocallyOfFinitePresentation U.hom] [LocallyOfFinitePresentation V.hom]
    [LocallyOfFinitePresentation C.hom] :
    LocallyOfFinitePresentation (scheme f g a b c).hom := by
  have : Etale (leftToSource f a c).left := hc.projection _ _ _ (leftSquare f a c)
  have : Etale (rightToSource g b c).left := hc.projection _ _ _ (rightSquare g b c)
  have : LocallyOfFinitePresentation (leftScheme f a c).hom := by
    rw [← Over.w (leftToSource f a c)]
    infer_instance
  have : LocallyOfFinitePresentation (rightScheme g b c).hom := by
    rw [← Over.w (rightToSource g b c)]
    infer_instance
  have : LocallyOfFinitePresentation ((rightToChart g b c).left ≫ C.hom) := by
    rw [Over.w]
    infer_instance
  have : LocallyOfFinitePresentation (rightToChart g b c).left :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp _ C.hom
  have : LocallyOfFinitePresentation
      (Limits.pullback.fst (leftToChart f a c) (rightToChart g b c)).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation.{u})
      ((IsPullback.of_hasPullback _ _).map (Over.forget S)).flip
      (by change LocallyOfFinitePresentation (rightToChart g b c).left; assumption)
  rw [← Over.w (Limits.pullback.fst (leftToChart f a c) (rightToChart g b c))]
  infer_instance

/-- The represented overlap of two affine schemes over a quasi-separated space is compact. -/
theorem compact_overlap [IsAffine S] [IsAffine C.left] [IsAffine U.left]
    (hZ : IsQuasiSeparated Z) : CompactSpace (leftScheme f a c).left := by
  have : IsAffine (C ⨯ U).left := IsAffine.of_isIso (Over.prodLeftIsoPullback C U).hom
  have : QuasiCompact (prod.lift (leftToChart f a c) (leftToSource f a c)).left :=
    relative_diagonal_property_chart_pairing (@QuasiCompact.{u}) hZ _ _ c (a ≫ hom f)
      (leftSquare f a c)
  exact QuasiCompact.compactSpace_of_compactSpace
    (prod.lift (leftToChart f a c) (leftToSource f a c)).left

/-- The common-chart atlas scheme is quasi-compact over the affine base. -/
theorem quasiCompact [IsAffine S] [IsAffine U.left] [IsAffine V.left] [IsAffine C.left]
    (hZ : IsQuasiSeparated Z) : QuasiCompact (scheme f g a b c).hom := by
  have : CompactSpace (leftScheme f a c).left := compact_overlap f a c hZ
  have : CompactSpace (rightScheme g b c).left := compact_overlap g b c hZ
  have : QuasiCompact (rightToChart g b c).left := inferInstance
  have : QuasiCompact (leftScheme f a c).hom := inferInstance
  have : QuasiCompact
      (Limits.pullback.fst (leftToChart f a c) (rightToChart g b c)).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact.{u})
      ((IsPullback.of_hasPullback _ _).map (Over.forget S)).flip
      (by change QuasiCompact (rightToChart g b c).left; assumption)
  rw [← Over.w (Limits.pullback.fst (leftToChart f a c) (rightToChart g b c))]
  infer_instance

end FibreProductFinitePresentation

namespace FibreProduct

variable {S : Scheme.{u}} [IsAffine S] {X Y Z : AlgebraicSpace S}

/-- The constructed fibre product has a quasi-compact, locally finitely presented atlas. -/
theorem hasAtlasProperty_finitePresentation (f : X ⟶ Z) (g : Y ⟶ Z)
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (hZ : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Z)
    (hZqs : IsQuasiSeparated Z) :
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) (fibreProduct f g) := by
  obtain ⟨U, a, hUa, ha, hsa, hUl⟩ := exists_affine_finitePresentation_atlas X hX
  obtain ⟨V, b, hVa, hb, hsb, hVl⟩ := exists_affine_finitePresentation_atlas Y hY
  obtain ⟨C, c, hCa, hc, hsc, hCl⟩ := exists_affine_finitePresentation_atlas Z hZ
  have : IsAffine U.left := hUa
  have : IsAffine V.left := hVa
  have : IsAffine C.left := hCa
  have : LocallyOfFinitePresentation U.hom := hUl
  have : LocallyOfFinitePresentation V.hom := hVl
  have : LocallyOfFinitePresentation C.hom := hCl
  exact ⟨FibreProductFinitePresentation.scheme f g a b c,
    FibreProductFinitePresentation.atlas f g a b c,
    FibreProductFinitePresentation.atlas_isEtale f g a b c ha hb hc,
    FibreProductFinitePresentation.atlas_isSurjective f g a b c hsa hsb hsc,
    FibreProductFinitePresentation.locallyOfFinitePresentation f g a b c hc,
    FibreProductFinitePresentation.quasiCompact f g a b c hZqs⟩

/-- Fibre products preserve both required finite-presentation properties with no
hypothesis on either morphism. -/
theorem finitePresentation (f : X ⟶ Z) (g : Y ⟶ Z)
    (hXqs : IsQuasiSeparated X) (hYqs : IsQuasiSeparated Y) (hZqs : IsQuasiSeparated Z)
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (hZ : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Z) :
    IsQuasiSeparated (fibreProduct f g) ∧
      HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) (fibreProduct f g) :=
  ⟨isQuasiSeparated f g hXqs hYqs, hasAtlasProperty_finitePresentation f g hX hY hZ hZqs⟩

/-- The same closure for the categorical chosen pullback. -/
theorem finitePresentation_pullback (f : X ⟶ Z) (g : Y ⟶ Z)
    (hXqs : IsQuasiSeparated X) (hYqs : IsQuasiSeparated Y) (hZqs : IsQuasiSeparated Z)
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (hZ : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Z) :
    IsQuasiSeparated (Limits.pullback f g) ∧
      HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u})
        (Limits.pullback f g) := by
  let e : (fibreProduct f g).presheaf ≅ (Limits.pullback f g).presheaf :=
    (forgetToPresheaf S).mapIso (isPullback f g).isoPullback
  have h := finitePresentation f g hXqs hYqs hZqs hX hY hZ
  have : MorphismProperty.RespectsIso (@QuasiCompact.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact ⟨relative_diag_of_iso (@QuasiCompact.{u}) e h.1, h.2.of_iso e⟩

end FibreProduct

end Langlands.AlgebraicGeometry.AlgebraicSpace
