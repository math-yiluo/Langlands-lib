import Langlands.AlgebraicGeometry.AlgebraicSpace.PullbackDiagonals
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Actual fibre products of algebraic spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

variable {S : Scheme.{u}}

/-- The actual presheaf fibre product has representable diagonal. -/
theorem hasRepresentableDiagonal_pullback {F G H : Presheaf S}
    (f : F ⟶ H) (g : G ⟶ H)
    (hF : HasRepresentableDiagonal F) (hG : HasRepresentableDiagonal G) :
    HasRepresentableDiagonal (Limits.pullback f g) :=
  PullbackDiagonals.pullback (schemeYoneda S).relativelyRepresentable f g hF hG

namespace FibreProduct

variable {X Y Z : AlgebraicSpace S} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The actual fppf-sheaf pullback. -/
abbrev sheaf : FppfSheaf S := Limits.pullback f.hom g.hom

/-- Its whole underlying presheaf is the actual presheaf pullback. -/
def presheafIso : (sheaf f g).obj ≅ Limits.pullback (hom f) (hom g) :=
  PreservesPullback.iso (sheafToPresheaf (fppfTopology S) (Type (u + 1))) f.hom g.hom

variable {f g}

/-- The scheme representing the fibre product of two chosen scheme charts over `Z`. -/
abbrev atlasScheme {U V : Over S}
    (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf) : Over S :=
  (Z.representable_from_scheme (a ≫ hom f)).pullback (b ≫ hom g)

/-- A whole-presheaf representation of the fibre product of the two charts. -/
def atlasSchemeIso {U V : Over S}
    (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf) :
    (schemeYoneda S).obj (atlasScheme (f := f) (g := g) a b) ≅
      Limits.pullback (a ≫ hom f) (b ≫ hom g) :=
  (Functor.relativelyRepresentable.isPullback
    (Z.representable_from_scheme (a ≫ hom f)) (b ≫ hom g)).isoPullback

/-- The atlas map is the actual morphism of pullbacks, after the full scheme comparison. -/
def atlasMap {U V : Over S}
    (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf) :
    (schemeYoneda S).obj (atlasScheme (f := f) (g := g) a b) ⟶
      Limits.pullback (hom f) (hom g) :=
  (atlasSchemeIso a b).hom ≫
    Limits.pullback.map _ _ _ _ a b (𝟙 Z.presheaf) (by simp) (by simp)

/-- Any relative scheme property stable under composition passes from the two charts
 to their fibre-product atlas map. -/
theorem relative_atlasMap (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] [P.IsStableUnderComposition]
    {U V : Over S}
    {a : (schemeYoneda S).obj U ⟶ X.presheaf}
    {b : (schemeYoneda S).obj V ⟶ Y.presheaf}
    (ha : (P.inverseImage (Over.forget S)).relative (schemeYoneda S) a)
    (hb : (P.inverseImage (Over.forget S)).relative (schemeYoneda S) b) :
    (P.inverseImage (Over.forget S)).relative (schemeYoneda S)
      (atlasMap (f := f) (g := g) a b) := by
  apply MorphismProperty.RespectsIso.precomp
  exact MorphismProperty.pullbackMap ha hb rfl rfl

variable (f g)

/-- The actual sheaf pullback satisfies the unchanged algebraic-space predicate. -/
theorem isAlgebraicSpace : IsAlgebraicSpace S (sheaf f g) := by
  have : MorphismProperty.IsStableUnderComposition (@Etale.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative (@Etale.{u})).toIsStableUnderComposition
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    Etale.etale_isStableUnderBaseChange.respectsIso
  have : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative (@Surjective.{u})).toIsStableUnderComposition
  obtain ⟨U, a, ha, hs⟩ := X.property.2
  obtain ⟨V, b, hb, ht⟩ := Y.property.2
  refine ⟨hasRepresentableDiagonal_of_iso (presheafIso f g).symm
      (hasRepresentableDiagonal_pullback (hom f) (hom g)
        X.hasRepresentableDiagonal Y.hasRepresentableDiagonal),
    atlasScheme (f := f) (g := g) a b,
    atlasMap a b ≫ (presheafIso f g).inv, ?_, ?_⟩
  · exact IsEtale.comp_iso (relative_atlasMap (@Etale.{u}) ha hb) (presheafIso f g).symm
  · exact IsSurjective.comp_iso (relative_atlasMap (@Surjective.{u}) hs ht)
      (presheafIso f g).symm

end FibreProduct

/-- The fibre product of arbitrary algebraic spaces over the given scheme. -/
def fibreProduct {X Y Z : AlgebraicSpace S} (f : X ⟶ Z) (g : Y ⟶ Z) : AlgebraicSpace S :=
  ⟨FibreProduct.sheaf f g, FibreProduct.isAlgebraicSpace f g⟩

namespace FibreProduct

variable {X Y Z : AlgebraicSpace S} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- First actual algebraic-space projection. -/
def fst : fibreProduct f g ⟶ X := ObjectProperty.homMk (Limits.pullback.fst f.hom g.hom)

/-- Second actual algebraic-space projection. -/
def snd : fibreProduct f g ⟶ Y := ObjectProperty.homMk (Limits.pullback.snd f.hom g.hom)

/-- The presheaf comparison identifies the first projection. -/
@[reassoc (attr := simp)]
theorem presheafIso_hom_fst :
    (presheafIso f g).hom ≫ Limits.pullback.fst (hom f) (hom g) = hom (fst f g) :=
  PreservesPullback.iso_hom_fst _ _ _

/-- The presheaf comparison identifies the second projection. -/
@[reassoc (attr := simp)]
theorem presheafIso_hom_snd :
    (presheafIso f g).hom ≫ Limits.pullback.snd (hom f) (hom g) = hom (snd f g) :=
  PreservesPullback.iso_hom_snd _ _ _

/-- The square is cartesian in the actual category of algebraic spaces. -/
theorem isPullback : IsPullback (fst f g) (snd f g) f g := by
  apply IsPullback.of_map (forgetToSheaf S)
  · apply (homEquiv _ _).injective
    exact (sheafToPresheaf (fppfTopology S) (Type (u + 1))).congr_map
      (Limits.pullback.condition (f := f.hom) (g := g.hom))
  · exact IsPullback.of_hasPullback f.hom g.hom

/-- The constructed square remains cartesian on the whole underlying presheaves. -/
theorem isPullback_presheaf :
    IsPullback (hom (fst f g)) (hom (snd f g)) (hom f) (hom g) :=
  (IsPullback.of_hasPullback f.hom g.hom).map
    (sheafToPresheaf (fppfTopology S) (Type (u + 1)))

/-- Quasi-separatedness passes to the constructed fibre product. -/
theorem isQuasiSeparated (hX : IsQuasiSeparated X) (hY : IsQuasiSeparated Y) :
    IsQuasiSeparated (fibreProduct f g) := by
  let P := (MorphismProperty.inverseImage (@QuasiCompact.{u}) (Over.forget S)).relative
    (schemeYoneda S)
  have : MorphismProperty.IsStableUnderComposition (@QuasiCompact.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative (@QuasiCompact.{u})).toIsStableUnderComposition
  have : MorphismProperty.RespectsIso (@QuasiCompact.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (MorphismProperty.inverseImage (@QuasiCompact.{u}) (Over.forget S)).IsMultiplicative := {
    id_mem := fun U => by change QuasiCompact (𝟙 U.left); infer_instance
    comp_mem := fun a b ha hb => by
      change QuasiCompact (a.left ≫ b.left)
      have : QuasiCompact a.left := ha
      have : QuasiCompact b.left := hb
      infer_instance }
  have : (MorphismProperty.inverseImage (@QuasiCompact.{u}) (Over.forget S)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have : P.IsMultiplicative := by
    exact MorphismProperty.relative_isMultiplicative
      (P := MorphismProperty.inverseImage (@QuasiCompact.{u}) (Over.forget S))
      (F := schemeYoneda S)
  exact relative_diag_of_iso (@QuasiCompact.{u}) (presheafIso f g).symm
    (PullbackDiagonals.pullback P (hom f) (hom g) hX hY)

end FibreProduct

instance {X Y Z : AlgebraicSpace S} (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g :=
  ⟨⟨_, (FibreProduct.isPullback f g).isLimit⟩⟩

instance (S : Scheme.{u}) : HasPullbacks (AlgebraicSpace S) :=
  hasPullbacks_of_hasLimit_cospan (AlgebraicSpace S)

instance {X Y Z : AlgebraicSpace S} (f : X ⟶ Z) (g : Y ⟶ Z) :
    PreservesLimit (cospan f g) (forgetToPresheaf S) :=
  preservesLimit_of_preserves_limit_cone (FibreProduct.isPullback f g).isLimit
    ((isLimitMapConePullbackConeEquiv (forgetToPresheaf S)
      (FibreProduct.isPullback f g).w).symm
      (FibreProduct.isPullback_presheaf f g).isLimit)

instance (S : Scheme.{u}) : PreservesLimitsOfShape WalkingCospan (forgetToPresheaf S) where
  preservesLimit {K} := preservesLimit_of_iso_diagram _ (diagramIsoCospan K).symm

end Langlands.AlgebraicGeometry.AlgebraicSpace
