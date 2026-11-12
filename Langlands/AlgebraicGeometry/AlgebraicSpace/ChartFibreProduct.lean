import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismProperties
import Langlands.AlgebraicGeometry.AlgebraicSpace.ExtensionProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsOpenProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasIsoTransport
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeHelpers
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Langlands.Global.AdelicSpaceLevelPointsStatement

/-!
# Fibre products of algebraic spaces with schemes

For a morphism of algebraic spaces `f : X ⟶ Y` and a map `g : h_V ⟶ Y` from an actual scheme,
the elementwise fibre product `X ×_Y h_V` is a presheaf whose sections over `T` are pairs
`(x, v)` with `f x = g v`. If `f` is separated and quasi-compact and `V` is affine, it is a
separated algebraic space; over a field it is of finite type when `X` is locally of finite
type and `g` is étale.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace ChartFibre

variable {S : Scheme.{u}}

section Presheaf

variable {F G H : Presheaf S} (f : F ⟶ G) (g : H ⟶ G)

/-- The elementwise fibre product of presheaves: sections are pairs with equal images. -/
@[simps obj map]
def fibre : Presheaf S where
  obj T := {p : F.obj T × H.obj T // f.app T p.1 = g.app T p.2}
  map φ := ↾fun p ↦ ⟨(F.map φ p.1.1, H.map φ p.1.2), by
    simp only [NatTrans.naturality_apply, p.2]⟩

/-- The first projection of the fibre product. -/
@[simps app]
def fst : fibre f g ⟶ F where
  app _ := ↾fun p ↦ p.1.1

/-- The second projection of the fibre product. -/
@[simps app]
def snd : fibre f g ⟶ H where
  app _ := ↾fun p ↦ p.1.2

/-- The elementwise fibre product is a pullback of presheaves. -/
theorem isPullback : IsPullback (fst f g) (snd f g) f g := by
  apply isPullback_of_elements
  · intro T p
    exact p.2
  · intro T p p' h₁ h₂
    exact Subtype.ext (Prod.ext h₁ h₂)
  · intro T x y h
    exact ⟨⟨(x, y), h⟩, rfl, rfl⟩

end Presheaf

section Yoneda

variable {F G : Presheaf S}

/-- Composition after a Yoneda point, with the universe of the presheaves fixed. -/
theorem yoneda_symm_comp {U : Over S} (x : F.obj (op U)) (f : F ⟶ G) :
    uliftYonedaEquiv.{u + 1}.symm x ≫ f = uliftYonedaEquiv.{u + 1}.symm (f.app _ x) :=
  uliftYonedaEquiv_symm_comp x f

/-- Restriction of a Yoneda point, with the universe of the presheaves fixed. -/
theorem yoneda_symm_map {T U : Over S} (h : T ⟶ U) (x : F.obj (op U)) :
    uliftYonedaEquiv.{u + 1}.symm (F.map h.op x) =
      (schemeYoneda S).map h ≫ uliftYonedaEquiv.{u + 1}.symm x :=
  uliftYonedaEquiv_symm_map h.op x

end Yoneda

section Space

variable {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- For a separated morphism, two sections with the same image agree exactly on a closed
subscheme. -/
theorem exists_representsEqualizer_of_isSeparatedMorphism (hf : IsSeparatedMorphism f)
    {U : Over S} (x y : X.sections U) (hxy : mapSections f U x = mapSections f U y) :
    ∃ (Z : Over S) (ι : Z ⟶ U), RepresentsEqualizer (F := X.presheaf) ι x y ∧
      _root_.AlgebraicGeometry.IsClosedImmersion ι.left := by
  have hw : uliftYonedaEquiv.{u + 1}.symm x ≫ hom f = uliftYonedaEquiv.{u + 1}.symm y ≫ hom f := by
    rw [yoneda_symm_comp, yoneda_symm_comp]
    exact congrArg _ hxy
  let t : (schemeYoneda S).obj U ⟶ Limits.pullback (hom f) (hom f) :=
    pullback.lift (uliftYonedaEquiv.{u + 1}.symm x) (uliftYonedaEquiv.{u + 1}.symm y) hw
  let hr : IsRepresentableMorphism (pullback.diagonal (hom f)) := hf.representable
  have hsq := hr.isPullback t
  refine ⟨hr.pullback t, hr.snd t, fun T h ↦ ⟨?_, fun hxy' ↦ ?_⟩,
    hf.pullback_closedImmersion hr t⟩
  · rintro ⟨z, rfl⟩
    have e₁ := congr($(hsq.w) ≫ pullback.fst _ _)
    have e₂ := congr($(hsq.w) ≫ pullback.snd _ _)
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      t, pullback.lift_fst, pullback.lift_snd] at e₁ e₂
    have e := congrArg (fun α ↦ ((schemeYoneda S).map z ≫ α).app (op T)
      (ULift.up (𝟙 T))) (e₁.symm.trans e₂)
    simpa [schemeYoneda_app_up, uliftYonedaEquiv_apply] using e
  · let a : (schemeYoneda S).obj T ⟶ X.presheaf :=
      uliftYonedaEquiv.{u + 1}.symm (X.presheaf.map h.op x)
    have w : a ≫ pullback.diagonal (hom f) = (schemeYoneda S).map h ≫ t := by
      apply pullback.hom_ext
      · change (a ≫ pullback.diagonal (hom f)) ≫ pullback.fst _ _ =
          ((schemeYoneda S).map h ≫ pullback.lift _ _ hw) ≫ pullback.fst _ _
        rw [Category.assoc, Category.assoc, pullback.diagonal_fst, pullback.lift_fst,
          Category.comp_id]
        exact yoneda_symm_map h x
      · change (a ≫ pullback.diagonal (hom f)) ≫ pullback.snd _ _ =
          ((schemeYoneda S).map h ≫ pullback.lift _ _ hw) ≫ pullback.snd _ _
        rw [Category.assoc, Category.assoc, pullback.diagonal_snd, pullback.lift_snd,
          Category.comp_id, ← yoneda_symm_map h y, ← hxy']
    obtain ⟨z, hz⟩ := (schemeYoneda S).map_surjective (hsq.lift a ((schemeYoneda S).map h) w)
    refine ⟨z, (schemeYoneda S).map_injective ?_⟩
    rw [Functor.map_comp, hz, hsq.lift_snd]

variable {V : Over S} (g : (schemeYoneda S).obj V ⟶ Y.presheaf)

/-- The fibre product of sheaves is a sheaf. -/
theorem isSheaf_fibre : Presheaf.IsSheaf (fppfTopology S) (fibre (hom f) g) := by
  refine ObjectProperty.prop_of_isLimit (P := Presheaf.IsSheaf (fppfTopology S))
    (isPullback (hom f) g).isLimit ?_
  rintro (_ | ⟨_ | _⟩)
  · exact Y.toSheaf.property
  · exact X.toSheaf.property
  · exact ((schemeSheaf S).obj V).property

/-- Equalizer loci in the fibre product are closed when `f` is separated and `V` is separated. -/
theorem exists_representsEqualizer_fibre (hf : IsSeparatedMorphism f)
    [_root_.AlgebraicGeometry.IsSeparated V.hom]
    {U : Over S} (x y : (fibre (hom f) g).obj (op U)) :
    ∃ (Z : Over S) (ι : Z ⟶ U), RepresentsEqualizer ι x y ∧
      _root_.AlgebraicGeometry.IsClosedImmersion ι.left := by
  obtain ⟨Z₁, ι₁, h₁, hc₁⟩ := exists_representsEqualizer_of_relative_diag
    (P := @_root_.AlgebraicGeometry.IsClosedImmersion)
    (isClosedImmersion_diag_schemeYoneda V) x.1.2 y.1.2
  let x' := (fibre (hom f) g).map ι₁.op x
  let y' := (fibre (hom f) g).map ι₁.op y
  have hv : x'.1.2 = y'.1.2 := (h₁ ι₁).1 ⟨𝟙 _, Category.id_comp _⟩
  have hxy : mapSections f Z₁ x'.1.1 = mapSections f Z₁ y'.1.1 := by
    change (hom f).app _ x'.1.1 = (hom f).app _ y'.1.1
    rw [x'.2, y'.2, hv]
  obtain ⟨Z₂, ι₂, h₂, hc₂⟩ :=
    exists_representsEqualizer_of_isSeparatedMorphism f hf x'.1.1 y'.1.1 hxy
  refine ⟨Z₂, ι₂ ≫ ι₁, fun T h ↦ ⟨?_, fun hxy' ↦ ?_⟩, ?_⟩
  · rintro ⟨z, rfl⟩
    apply Subtype.ext
    apply Prod.ext
    · have := (h₂ (z ≫ ι₂)).1 ⟨z, rfl⟩
      have e : ∀ p : (fibre (hom f) g).obj (op U),
          ((fibre (hom f) g).map (z ≫ ι₂ ≫ ι₁).op p).1.1 =
            X.presheaf.map (z ≫ ι₂).op ((fibre (hom f) g).map ι₁.op p).1.1 := by
        intro p
        change X.presheaf.map (z ≫ ι₂ ≫ ι₁).op p.1.1 =
          X.presheaf.map (z ≫ ι₂).op (X.presheaf.map ι₁.op p.1.1)
        rw [← Category.assoc, op_comp, Functor.map_comp_apply]
      rw [e, e]
      exact this
    · exact (h₁ (z ≫ ι₂ ≫ ι₁)).1 ⟨z ≫ ι₂, Category.assoc _ _ _⟩
  · have hv' := congrArg (fun p ↦ p.1.2) hxy'
    obtain ⟨z₁, hz₁⟩ := (h₁ h).2 hv'
    have hX' : X.presheaf.map z₁.op x'.1.1 = X.presheaf.map z₁.op y'.1.1 := by
      have h1 := congrArg (fun p ↦ p.1.1) hxy'
      change X.presheaf.map h.op x.1.1 = X.presheaf.map h.op y.1.1 at h1
      change X.presheaf.map z₁.op (X.presheaf.map ι₁.op x.1.1) =
        X.presheaf.map z₁.op (X.presheaf.map ι₁.op y.1.1)
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, hz₁]
      exact h1
    obtain ⟨z₂, hz₂⟩ := (h₂ z₁).2 hX'
    exact ⟨z₂, by rw [← Category.assoc, hz₂, hz₁]⟩
  · change _root_.AlgebraicGeometry.IsClosedImmersion (ι₂.left ≫ ι₁.left)
    infer_instance

/-- The fibre product has a closed-immersion diagonal. -/
theorem isClosedImmersion_diag_fibre (hf : IsSeparatedMorphism f)
    [_root_.AlgebraicGeometry.IsSeparated V.hom] :
    IsClosedImmersion (Limits.diag (fibre (hom f) g)) :=
  isClosedImmersion_diag_of_representsEqualizer fun _ x y ↦
    exists_representsEqualizer_fibre f g hf x y

/-- A quasi-compact morphism gives the fibre product over an affine scheme a quasi-compact étale
atlas. -/
theorem exists_atlas_fibre (hqc : IsQuasiCompactMorphism f) [IsAffine V.left] :
    ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ fibre (hom f) g),
      CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a := by
  obtain ⟨U, a, hU, ha, hs⟩ := hqc V inferInstance g
  let e := (isPullback (hom f) g).isoPullback
  exact ⟨U, a ≫ e.inv, hU, ha.comp_iso e.symm, hs.comp_iso e.symm⟩

/-- The fibre product is an algebraic space. -/
theorem isAlgebraicSpace_fibre (hf : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    [_root_.AlgebraicGeometry.IsSeparated V.hom] [IsAffine V.left] :
    IsAlgebraicSpace S ⟨fibre (hom f) g, isSheaf_fibre f g⟩ := by
  obtain ⟨U, a, -, ha, hs⟩ := exists_atlas_fibre f g hqc
  exact ⟨(isClosedImmersion_diag_fibre f g hf).representable, U, a, ha, hs⟩

/-- The fibre product `X ×_Y h_V` as an algebraic space. -/
def space (hf : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    [_root_.AlgebraicGeometry.IsSeparated V.hom]
    [IsAffine V.left] : AlgebraicSpace S :=
  ⟨⟨fibre (hom f) g, isSheaf_fibre f g⟩, isAlgebraicSpace_fibre f g hf hqc⟩

variable (hf : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
  [_root_.AlgebraicGeometry.IsSeparated V.hom]
  [IsAffine V.left]

/-- The fibre product is separated. -/
theorem isSeparated_space : IsSeparated (space f g hf hqc) :=
  isClosedImmersion_diag_fibre f g hf

/-- The first projection `X ×_Y h_V ⟶ X`. -/
def pr₁ : space f g hf hqc ⟶ X := homMk (fst (hom f) g)

/-- The second projection `X ×_Y h_V ⟶ h_V`. -/
def pr₂ : space f g hf hqc ⟶ (schemeToSpace S).obj V := homMk (snd (hom f) g)

end Space

section FiniteType

variable {C : Type u} [CommRing C] {X Y : AlgebraicSpace (Spec (CommRingCat.of C))} (f : X ⟶ Y)
  {V : Over (Spec (CommRingCat.of C))} (g : (schemeYoneda _).obj V ⟶ Y.presheaf)

/-- The first projection is étale when `g` is. -/
theorem isEtale_fst (hg : IsEtale g) : IsEtale (fst (hom f) g) := by
  have := MorphismProperty.relative_isStableUnderBaseChange
    (P := MorphismProperty.inverseImage (@Etale.{u}) (Over.forget (Spec (CommRingCat.of C))))
    (F := schemeYoneda _)
  exact this.of_isPullback (isPullback (hom f) g).flip hg

/-- Over an affine base, the fibre product along an étale `g` is of finite type when `X` is
locally of finite type. -/
theorem finiteTypeOverRing_space (hX : LocallyOfFiniteTypeOverBase X) (hg : IsEtale g)
    (hf : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    [_root_.AlgebraicGeometry.IsSeparated V.hom] [IsAffine V.left] :
    FiniteTypeOverRing C (space f g hf hqc) := by
  obtain ⟨U, a, hU, ha, hs⟩ := exists_atlas_fibre f g hqc
  refine ⟨U, a, ha, hs, ?_, ?_⟩
  · exact HenselianIntegralPointsOpen.locallyOfFiniteType_of_isEtale hX (a ≫ fst (hom f) g)
      (IsEtale.comp ha (isEtale_fst f g hg))
  · have := hU
    change QuasiCompact U.hom
    infer_instance

end FiniteType

end ChartFibre

end Langlands.AlgebraicGeometry.AlgebraicSpace
