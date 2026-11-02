import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationInvariantOpenDescent
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleTailOpenExtension

/-! # Nonidentity arrows in cartesian diagrams of equivalence relations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

namespace IsCartesianHom

variable {E F : EtaleEquivalenceRelation.{u}} {f : E.U ⟶ F.U} {g : E.R ⟶ F.R}
  (h : IsCartesianHom E F f g)

include h in
/-- A cartesian relation map reflects units, with their scheme structure. -/
lemma unit_isPullback : IsPullback f E.unit F.unit g := by
  have hu := OpenExtension.Comparison.unit_naturality h.1 h.2.w
  refine IsPullback.mk' hu.symm ?_ ?_
  · intro T a b _ hs
    exact (cancel_mono E.unit).mp hs
  · intro T a b hab
    have hf : (b ≫ E.s) ≫ f = a := by
      simpa only [Category.assoc, unit_s, Category.comp_id, h.2.w] using
        (congrArg (fun k => k ≫ F.s) hab).symm
    refine ⟨b ≫ E.s, hf, ?_⟩
    apply h.2.hom_ext
    · calc
        ((b ≫ E.s) ≫ E.unit) ≫ g = ((b ≫ E.s) ≫ f) ≫ F.unit := by
          simp only [Category.assoc, hu]
        _ = a ≫ F.unit := by rw [hf]
        _ = b ≫ g := hab
    · simp

include h in
lemma unit_opensRange_preimage : g ⁻¹ᵁ F.unit.opensRange = E.unit.opensRange := by
  simpa using
    (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      h.unit_isPullback (⊤ : F.U.Opens)).symm

variable [IsSeparated E.s] [IsSeparated F.s]

include h in
/-- Nonidentity arrows are preserved and reflected by a cartesian map. -/
lemma offDiagonalOpen_preimage :
    g ⁻¹ᵁ OpenExtension.offDiagonalOpen F = OpenExtension.offDiagonalOpen E := by
  ext x
  change g x ∉ Set.range F.unit ↔ x ∉ Set.range E.unit
  have hx := congrArg (fun V : E.R.Opens => x ∈ V) h.unit_opensRange_preimage
  change (g x ∈ Set.range F.unit) = (x ∈ Set.range E.unit) at hx
  exact not_congr (eq_iff_iff.mp hx)

/-- Restriction of a cartesian relation map to its nonidentity arrows. -/
def offDiagonalMap : (OpenExtension.offDiagonalOpen E).toScheme ⟶
    (OpenExtension.offDiagonalOpen F).toScheme :=
  g.resLE _ _ h.offDiagonalOpen_preimage.ge

@[reassoc (attr := simp)]
lemma offDiagonalMap_ι : h.offDiagonalMap ≫ (OpenExtension.offDiagonalOpen F).ι =
    (OpenExtension.offDiagonalOpen E).ι ≫ g :=
  Scheme.Hom.resLE_comp_ι _ _

lemma offDiagonalMap_isPullback :
    IsPullback h.offDiagonalMap (OpenExtension.offDiagonalOpen E).ι
      (OpenExtension.offDiagonalOpen F).ι g := by
  apply IsOpenImmersion.isPullback
  · exact h.offDiagonalMap_ι.symm
  · simpa only [Scheme.Opens.opensRange_ι] using h.offDiagonalOpen_preimage

end IsCartesianHom

namespace OpenExtension

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  {V : Scheme.{u}} (ι : E.U ⟶ V) [IsOpenImmersion ι]

/-- Affineness of the extension only needs affineness of the nonidentity arrows. -/
lemma arrows_isAffine_of_offDiagonal [IsAffine V]
    [IsAffine (offDiagonalOpen E).toScheme] : IsAffine (arrows E ι) :=
  IsAffine.of_isIso (arrowsCoprodIso E ι).hom

/-- If the extension is affine, its old nonidentity-arrow summand is affine. -/
lemma offDiagonal_isAffine_of_extension [IsAffine (arrows E ι)] :
    IsAffine (offDiagonalOpen E).toScheme := by
  have : IsAffine (V ⨿ (offDiagonalOpen E).toScheme) :=
    IsAffine.of_isIso (arrowsCoprodIso E ι).inv
  have : IsClosedImmersion (coprod.inr : (offDiagonalOpen E).toScheme ⟶
      V ⨿ (offDiagonalOpen E).toScheme) := by
    apply IsClosedImmersion.of_isPreimmersion
    rw [← (AlgebraicGeometry.isCompl_range_inl_inr V (offDiagonalOpen E).toScheme).compl_eq]
    exact (coprod.inl : V ⟶ V ⨿ (offDiagonalOpen E).toScheme).isOpenEmbedding.isOpen_range.isClosed_compl
  exact isAffine_of_isAffineHom (coprod.inr : (offDiagonalOpen E).toScheme ⟶
    V ⨿ (offDiagonalOpen E).toScheme)

end OpenExtension

namespace CartesianDiagram.OffDiagonal

variable {I : Type u} [Category.{u} I] (D : I ⥤ EtaleEquivalenceRelation.{u})
  [∀ i, IsSeparated (D.obj i).s]

/-- The actual diagram of nonidentity-arrow schemes. -/
def diagram : I ⥤ Scheme.{u} where
  obj i := (OpenExtension.offDiagonalOpen (D.obj i)).toScheme
  map a := (D.map a).isCartesian.offDiagonalMap
  map_id i := by
    apply (cancel_mono (OpenExtension.offDiagonalOpen (D.obj i)).ι).mp
    simp only [IsCartesianHom.offDiagonalMap_ι, Category.id_comp, Category.comp_id,
      D.map_id, id_relMap]
  map_comp a b := by
    apply (cancel_mono (OpenExtension.offDiagonalOpen (D.obj _)).ι).mp
    simp only [Category.assoc, IsCartesianHom.offDiagonalMap_ι,
      IsCartesianHom.offDiagonalMap_ι_assoc, D.map_comp, comp_relMap]

/-- Inclusion in the relation-scheme diagram. -/
def inclusion : diagram D ⟶ D ⋙ relationFunctor where
  app i := (OpenExtension.offDiagonalOpen (D.obj i)).ι
  naturality _ _ a := (D.map a).isCartesian.offDiagonalMap_ι

variable (c : Cone D) [IsSeparated c.pt.s]

/-- The nonidentity-arrow cone induced by a cartesian relation cone. -/
def cone : Cone (diagram D) where
  pt := (OpenExtension.offDiagonalOpen c.pt).toScheme
  π :=
    { app i := (c.π.app i).isCartesian.offDiagonalMap (E := c.pt) (F := D.obj i)
      naturality := by
        intro i j a
        change 𝟙 _ ≫ (c.π.app j).isCartesian.offDiagonalMap (E := c.pt) (F := D.obj j) =
          (c.π.app i).isCartesian.offDiagonalMap (E := c.pt) (F := D.obj i) ≫
            (D.map a).isCartesian.offDiagonalMap
        apply (cancel_mono (OpenExtension.offDiagonalOpen (D.obj j)).ι).mp
        simp only [Category.id_comp, Category.assoc, IsCartesianHom.offDiagonalMap_ι,
          IsCartesianHom.offDiagonalMap_ι_assoc]
        rw [← comp_relMap, c.w a] }

attribute [local instance] IsCofiltered.isConnected

/-- Taking nonidentity arrows preserves the supplied cofiltered object limit. -/
def isLimit [IsCofiltered I] (hc : IsLimit (objectFunctor.mapCone c)) :
    IsLimit (cone D c) :=
  isLimitOfIsPullbackOfIsConnected (inclusion D) (cone D c) (relationFunctor.mapCone c)
    { hom := (OpenExtension.offDiagonalOpen c.pt).ι
      w := fun i => ((c.π.app i).isCartesian.offDiagonalMap_ι (E := c.pt) (F := D.obj i)).symm }
    (fun i => (c.π.app i).isCartesian.offDiagonalMap_isPullback (E := c.pt) (F := D.obj i))
    (CartesianDiagram.isLimitRelation D c hc)

instance map_isAffine [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a).objMap]
    {i j : I} (a : i ⟶ j) : IsAffineHom ((diagram D).map a) := by
  have : IsAffineHom (D.map a).relMap :=
    MorphismProperty.of_isPullback (D.map a).isCartesian.2.flip inferInstance
  exact MorphismProperty.of_isPullback
    (D.map a).isCartesian.offDiagonalMap_isPullback.flip inferInstance

include c in
/-- An affine limit of nonidentity arrows has an affine nonidentity-arrow level. -/
lemma exists_isAffine [IsCofiltered I]
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a).objMap]
    [∀ i, CompactSpace (D.obj i).R] [∀ i, QuasiSeparatedSpace (D.obj i).R]
    [IsAffine (OpenExtension.offDiagonalOpen c.pt).toScheme]
    (hc : IsLimit (objectFunctor.mapCone c)) :
    ∃ i, IsAffine (OpenExtension.offDiagonalOpen (D.obj i)).toScheme := by
  have (i : I) : CompactSpace ((diagram D).obj i) :=
    isCompact_iff_compactSpace.mp (OpenExtension.offDiagonalOpen_isClosed (D.obj i)).isCompact
  have (i : I) : QuasiSeparatedSpace ((diagram D).obj i) :=
    quasiSeparatedSpace_of_quasiSeparated (OpenExtension.offDiagonalOpen (D.obj i)).ι
  have : IsAffine (cone D c).pt :=
    inferInstanceAs (IsAffine (OpenExtension.offDiagonalOpen c.pt).toScheme)
  exact Scheme.exists_isAffine_of_isLimit (diagram D) (cone D c) (isLimit D c hc)

/-- Affineness of nonidentity arrows persists at every level above one affine level. -/
lemma isAffine_of_map [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a).objMap]
    {i j : I} (a : i ⟶ j)
    [IsAffine (OpenExtension.offDiagonalOpen (D.obj j)).toScheme] :
    IsAffine (OpenExtension.offDiagonalOpen (D.obj i)).toScheme := by
  have : IsAffine ((diagram D).obj j) :=
    inferInstanceAs (IsAffine (OpenExtension.offDiagonalOpen (D.obj j)).toScheme)
  exact isAffine_of_isAffineHom ((diagram D).map a)

end CartesianDiagram.OffDiagonal

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R] [IsClosedImmersion (prod.lift E.t E.s)]

instance tupleTailNextRelation_source_isSeparated (N p : ℕ) :
    IsSeparated (E.tupleTailNextRelation N p).s :=
  MorphismProperty.of_isPullback (E.tupleTailNextRelation_isCartesianHom N p).2 inferInstance

/-- The actual invariant next-threshold restriction has affine nonidentity arrows. -/
lemma tupleTailNextRelation_offDiagonal_isAffine (N p : ℕ) (hp : p < N + 1) :
    IsAffine (OpenExtension.offDiagonalOpen (E.tupleTailNextRelation N p)).toScheme := by
  have : IsAffine (OpenExtension.arrows (E.tupleTailNextRelation N p)
      (E.tupleTailNextOpen N p).ι) :=
    IsAffine.of_isIso (E.tupleTailOpenExtensionArrowsIso N p hp).hom
  exact OpenExtension.offDiagonal_isAffine_of_extension
    (E.tupleTailNextRelation N p) (E.tupleTailNextOpen N p).ι

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
