import Langlands.Representation.Jacquet.CoefficientExactness
import Langlands.Representation.Jacquet.LocalizationFiltration
import Langlands.Representation.Filtration.QuotientFirstIso

/-! Natural comparisons for actual native character-one image filtrations. -/

noncomputable section
open CategoryTheory

namespace Langlands.Jacquet.Localization.Coefficient

universe uR uG uV uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {C : Type uC} [Category.{vC} C] {F : C ⥤ Rep.{uV} R G}
  (U : Subgroup G) (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)

/-- The canonical quotient map on a subfunctor, with codomain its actual
image in the ambient native quotient. -/
def imageHom (S : RepSubfunctor F) :
    S.toFunctor ⋙ functor U 1 M hMU (isInvariant_one U M hMU) ⟶
      (imageSubfunctor U 1 M hMU (isInvariant_one U M hMU) S).toFunctor where
  app X := Rep.ofHom
    { toLinearMap :=
        (map U 1 M hMU (isInvariant_one U M hMU) (S.inclusion.app X).hom).toLinearMap.codRestrict
          (imageSubrepresentation U 1 M hMU (isInvariant_one U M hMU)
            (F.obj X).ρ (S.obj X)).toSubmodule (by
            intro q
            obtain ⟨v, rfl⟩ := mk_surjective (S.representation X).ρ U 1 q
            exact ⟨v.val, v.property, rfl⟩)
      isIntertwining' m := by
        apply LinearMap.ext
        intro q
        apply Subtype.ext
        exact LinearMap.congr_fun
          ((map U 1 M hMU (isInvariant_one U M hMU)
            (S.inclusion.app X).hom).isIntertwining' m) q }
  naturality := by
    intro X Y f
    ext q
    obtain ⟨v, rfl⟩ := mk_surjective (S.representation X).ρ U 1 q
    rfl

@[simp]
theorem imageHom_mk (S : RepSubfunctor F) (X : C) (v : S.representation X) :
    (((imageHom U M hMU S).app X).hom (mk (S.representation X).ρ U 1 v)).val =
      mk (F.obj X).ρ U 1 v.val := rfl

theorem imageHom_surjective (S : RepSubfunctor F) (X : C) :
    Function.Surjective ((imageHom U M hMU S).app X).hom := by
  rintro ⟨q, hq⟩
  obtain ⟨v, hv, rfl⟩ := hq
  exact ⟨mk (S.representation X).ρ U 1 ⟨v, hv⟩, rfl⟩

variable [Algebra ℂ R] [TopologicalSpace G] [IsTopologicalGroup G]
  (hU : IsLimitOfCompactSubgroups U) (hF : ∀ X, IsSmooth (F.obj X).ρ)

/-- Smooth native subquotient exactness identifies each localized subfunctor
naturally with its actual ambient image. -/
def imageIso (S : RepSubfunctor F) :
    S.toFunctor ⋙ functor U 1 M hMU (isInvariant_one U M hMU) ≅
      (imageSubfunctor U 1 M hMU (isInvariant_one U M hMU) S).toFunctor :=
  NatIso.ofComponents
    (fun X => Rep.mkIso (((imageHom U M hMU S).app X).hom.ofBijective
      ⟨fun _ _ h => map_one_injective U hU M hMU (S.inclusion.app X).hom
          (S.inclusion_injective X) (hF X) (congrArg Subtype.val h),
        imageHom_surjective U M hMU S X⟩))
    (fun f => (imageHom U M hMU S).naturality f)

/-- The map from the upper ambient image to the native quotient of the
original actual successive quotient. -/
def imageQuotientMap (S T : RepSubfunctor F) :
    (imageSubfunctor U 1 M hMU (isInvariant_one U M hMU) T).toFunctor ⟶
      S.quotientFunctor T ⋙ functor U 1 M hMU (isInvariant_one U M hMU) :=
  (imageIso U M hMU hU hF T).inv ≫
    Functor.whiskerRight (S.quotientNatProjection T)
      (functor U 1 M hMU (isInvariant_one U M hMU))

@[simp]
theorem imageQuotientMap_imageHom (S T : RepSubfunctor F)
    (X : C) (v : Coinvariants (T.representation X).ρ U 1) :
    ((imageQuotientMap U M hMU hU hF S T).app X).hom
        (((imageHom U M hMU T).app X).hom v) =
      map U 1 M hMU (isInvariant_one U M hMU) (S.quotientProjection T X).hom v := by
  change map U 1 M hMU (isInvariant_one U M hMU) (S.quotientProjection T X).hom
    (((imageIso U M hMU hU hF T).inv.app X).hom
      (((imageIso U M hMU hU hF T).hom.app X).hom v)) = _
  exact congrArg
    (map U 1 M hMU (isInvariant_one U M hMU) (S.quotientProjection T X).hom)
    (Rep.inv_hom_apply _ _ ((imageIso U M hMU hU hF T).app X) v)

private def inclusionOfLE (S T : RepSubfunctor F)
    (h : ∀ X, S.obj X ≤ T.obj X) (X : C) :
    (S.representation X).ρ.IntertwiningMap (T.representation X).ρ where
  toLinearMap := Submodule.inclusion (h X)
  isIntertwining' _ := rfl

omit [Algebra ℂ R] [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem inclusionOfLE_range (S T : RepSubfunctor F)
    (h : ∀ X, S.obj X ≤ T.obj X) (X : C) :
    LinearMap.range (inclusionOfLE S T h X).toLinearMap =
      LinearMap.ker (S.quotientProjection T X).hom.toLinearMap := by
  change LinearMap.range (Submodule.inclusion (h X)) =
    LinearMap.ker (S.lowerInUpper T X).toSubmodule.mkQ
  rw [Submodule.ker_mkQ]
  apply Submodule.ext
  intro v
  change (∃ w : S.representation X, (⟨w.val, h X w.property⟩ :
    T.representation X) = v) ↔ v.val ∈ S.obj X
  constructor
  · rintro ⟨w, rfl⟩
    exact w.property
  · intro hv
    exact ⟨⟨v.val, hv⟩, rfl⟩

/-- The actual lower ambient image is exactly the kernel on the upper image. -/
theorem imageQuotientMap_kernel (S T : RepSubfunctor F)
    (h : ∀ X, S.obj X ≤ T.obj X) (X : C)
    (v : (imageSubfunctor U 1 M hMU (isInvariant_one U M hMU) T).representation X) :
    v ∈ (imageSubfunctor U 1 M hMU (isInvariant_one U M hMU) S).lowerInUpper
        (imageSubfunctor U 1 M hMU (isInvariant_one U M hMU) T) X ↔
      ((imageQuotientMap U M hMU hU hF S T).app X).hom v = 0 := by
  obtain ⟨v, rfl⟩ := imageHom_surjective U M hMU T X v
  change (∃ w ∈ S.obj X, mk (F.obj X).ρ U 1 w =
      map U 1 M hMU (isInvariant_one U M hMU) (T.inclusion.app X).hom v) ↔ _
  rw [imageQuotientMap_imageHom U M hMU hU hF S T X v]
  have hex := map_range_eq_ker U 1 M hMU (isInvariant_one U M hMU)
    (inclusionOfLE S T h X) (S.quotientProjection T X).hom
    (S.quotientProjection_surjective T X) (inclusionOfLE_range S T h X)
  change (∃ w ∈ S.obj X, mk (F.obj X).ρ U 1 w =
      map U 1 M hMU (isInvariant_one U M hMU) (T.inclusion.app X).hom v) ↔
    map U 1 M hMU (isInvariant_one U M hMU) (S.quotientProjection T X).hom v = 0
  constructor
  · rintro ⟨w, hw, hwv⟩
    have hz :
        map U 1 M hMU (isInvariant_one U M hMU) (T.inclusion.app X).hom
            (map U 1 M hMU (isInvariant_one U M hMU) (inclusionOfLE S T h X)
              (mk (S.representation X).ρ U 1 ⟨w, hw⟩)) =
          map U 1 M hMU (isInvariant_one U M hMU) (T.inclusion.app X).hom v := hwv
    have hinj := map_one_injective U hU M hMU (T.inclusion.app X).hom
      (T.inclusion_injective X) (hF X)
    have hv : v ∈ LinearMap.range
        (map U 1 M hMU (isInvariant_one U M hMU) (inclusionOfLE S T h X)).toLinearMap :=
      ⟨mk (S.representation X).ρ U 1 ⟨w, hw⟩, hinj hz⟩
    rw [hex] at hv
    exact hv
  · intro hv
    have hv' : v ∈ LinearMap.ker
        (map U 1 M hMU (isInvariant_one U M hMU)
          (S.quotientProjection T X).hom).toLinearMap := hv
    rw [← hex] at hv'
    obtain ⟨z, rfl⟩ := hv'
    obtain ⟨w, rfl⟩ := mk_surjective (S.representation X).ρ U 1 z
    exact ⟨w.val, w.property, rfl⟩

theorem imageQuotientMap_surjective (S T : RepSubfunctor F) (X : C) :
    Function.Surjective ((imageQuotientMap U M hMU hU hF S T).app X).hom := by
  intro v
  obtain ⟨w, rfl⟩ := map_surjective U 1 M hMU (isInvariant_one U M hMU)
    (S.quotientProjection T X).hom (S.quotientProjection_surjective T X) v
  exact ⟨((imageHom U M hMU T).app X).hom w,
    imageQuotientMap_imageHom U M hMU hU hF S T X w⟩

/-- The native quotient of the actual upper image by the actual lower image
is naturally the native quotient of the original successive quotient. -/
def imageQuotientIso (S T : RepSubfunctor F) (h : ∀ X, S.obj X ≤ T.obj X) :
    (imageSubfunctor U 1 M hMU (isInvariant_one U M hMU) S).quotientFunctor
        (imageSubfunctor U 1 M hMU (isInvariant_one U M hMU) T) ≅
      S.quotientFunctor T ⋙ functor U 1 M hMU (isInvariant_one U M hMU) :=
  (imageSubfunctor U 1 M hMU (isInvariant_one U M hMU) S).quotientNatIsoOfSurjective
    (imageSubfunctor U 1 M hMU (isInvariant_one U M hMU) T)
    (imageQuotientMap U M hMU hU hF S T)
    (imageQuotientMap_kernel U M hMU hU hF S T h)
    (imageQuotientMap_surjective U M hMU hU hF S T)

/-- On a class represented by an actual upper vector, the comparison is the
native class of its actual successive-quotient class. -/
@[simp]
theorem imageQuotientIso_projection (S T : RepSubfunctor F)
    (h : ∀ X, S.obj X ≤ T.obj X) (X : C) (v : T.representation X) :
    ((imageQuotientIso U M hMU hU hF S T h).hom.app X).hom
        (((imageSubfunctor U 1 M hMU (isInvariant_one U M hMU) S).quotientProjection
          (imageSubfunctor U 1 M hMU (isInvariant_one U M hMU) T) X).hom
          (((imageHom U M hMU T).app X).hom (mk (T.representation X).ρ U 1 v))) =
      mk (S.quotientObj T X).ρ U 1 ((S.quotientProjection T X).hom v) :=
  imageQuotientMap_imageHom U M hMU hU hF S T X (mk (T.representation X).ρ U 1 v)

/-- Every grade of the fixed actual image filtration is naturally the native
character-one quotient of the corresponding original grade. -/
def imageFiltrationGradedIso {n : ℕ} (s : RepFunctorFiltration F n) (i : Fin n) :
    (imageFiltration U 1 M hMU (isInvariant_one U M hMU) s).graded i ≅
      s.graded i ⋙ functor U 1 M hMU (isInvariant_one U M hMU) :=
  imageQuotientIso U M hMU hU hF (s.step i.castSucc) (s.step i.succ)
    (fun X => s.step_le_next X i)

end Langlands.Jacquet.Localization.Coefficient
