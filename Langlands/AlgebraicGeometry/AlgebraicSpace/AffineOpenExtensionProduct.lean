import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineOpenSubfunctors
import Langlands.AlgebraicGeometry.AlgebraicSpace.ExtensionProduct

/-! # Affine open subfunctors under affine change of the represented factor -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-- A representable transformation whose every represented scheme projection
is affine. -/
def IsAffineMorphism {S : Scheme.{u}} {F G : Presheaf S} (f : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage (@IsAffineHom.{u})
    (Over.forget S)).relative (schemeYoneda S) f

namespace AffineOpenSubfunctors

variable {S : Scheme.{u}} {F G : Presheaf S}

local instance : (MorphismProperty.inverseImage (@IsAffineHom.{u})
    (Over.forget S)).RespectsIso := by
  have : MorphismProperty.RespectsIso (@IsAffineHom.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact MorphismProperty.RespectsIso.inverseImage _ _

/-- An affine open pulls back to an affine open along a representable affine map. -/
theorem IsAffineOpen.preimage_of_affine (f : F ⟶ G)
    (hf : IsAffineMorphism f)
    {A : Subfunctor G} (hA : IsAffineOpen A) :
    IsAffineOpen (A.preimage f) := by
  obtain ⟨hA, V, hV, ⟨e⟩⟩ := hA
  let : IsAffine V.left := hV
  let a := e.hom ≫ A.ι
  have ha : IsOpenImmersion a :=
    (MorphismProperty.cancel_left_of_respectsIso
      ((SliceOpenGluing.openProperty S).relative (schemeYoneda S)) e.hom A.ι).mpr hA
  let hr := hf.rep
  let W := hr.pullback a
  let p : W ⟶ V := hr.snd a
  let b : (schemeYoneda S).obj W ⟶ F := hr.fst a
  have h : IsPullback b ((schemeYoneda S).map p) f a := hr.isPullback a
  let : IsAffineHom p.left := hf.property a b p h
  have hW : IsAffine W.left := isAffine_of_isAffineHom p.left
  have hb : IsOpenImmersion b := MorphismProperty.of_isPullback
    (P := (SliceOpenGluing.openProperty S).relative (schemeYoneda S)) h.flip ha
  have hra : Subfunctor.range a = A := by
    simp [a, Subfunctor.range_comp, Subfunctor.range_eq_top, Subfunctor.image_top]
  have hrb : Subfunctor.range b = A.preimage f := by
    rw [OpenSubfunctorLifting.range_eq_preimage_of_isPullback h.flip, hra]
  let c := Subfunctor.lift b (le_of_eq hrb)
  have hc : c ≫ (A.preimage f).ι = b := Subfunctor.lift_ι _ _
  let : Mono b := SliceOpenGluing.open_mono hb
  let : Mono c := mono_of_mono_fac hc
  have : IsIso c := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro T
    rw [isIso_iff_bijective]
    constructor
    · exact (CategoryTheory.mono_iff_injective (c.app T)).mp inferInstance
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (Subfunctor.range b).obj T := by rwa [hrb]
      obtain ⟨y, hy⟩ := hx'
      exact ⟨y, Subtype.ext hy⟩
  refine ⟨?_, W, hW, ⟨asIso c⟩⟩
  apply (MorphismProperty.cancel_left_of_respectsIso
    ((SliceOpenGluing.openProperty S).relative (schemeYoneda S)) c (A.preimage f).ι).mp
  rwa [hc]

/-- Pullback along an affine change of the represented factor preserves affine opens. -/
theorem IsAffineOpen.preimage_mapRight {F : Presheaf S} {Λ Λ' : Over S}
    (ρ : Λ' ⟶ Λ) [IsAffineHom ρ.left]
    {A : Subfunctor (extProd F Λ)} (hA : IsAffineOpen A) :
    IsAffineOpen (A.preimage (extProd.mapRight ρ)) := by
  apply hA.preimage_of_affine
  apply MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage (@IsAffineHom.{u})
      (Over.forget S)).relative (schemeYoneda S)) (extProd.isPullback_mapRight ρ).flip
  apply MorphismProperty.relative.of_exists
  intro T g
  obtain ⟨g, rfl⟩ := (schemeYoneda S).map_surjective g
  let h := IsPullback.of_hasPullback ρ g
  exact ⟨_, _, _, h.map (schemeYoneda S),
    MorphismProperty.of_isPullback (P := @IsAffineHom.{u})
      (h.map (Over.forget S)) (inferInstanceAs (IsAffineHom ρ.left))⟩

end AffineOpenSubfunctors

end Langlands.AlgebraicGeometry.AlgebraicSpace
