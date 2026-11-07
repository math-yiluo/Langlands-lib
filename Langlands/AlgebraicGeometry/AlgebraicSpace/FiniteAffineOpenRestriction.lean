import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubspaceGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteAffineUniversalNeighborhoods
import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Quasi-affine sources over compact universal-open restrictions -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteAffineOpenRestriction

open OpenSubfunctorLifting FiniteAffineUniversalNeighborhoods

variable {S : Scheme.{u}} {Y : AlgebraicSpace S} {U : Over S}

/-- The actual scheme obtained by restricting a scheme source to an open subspace. -/
def sourceOverOpen (π : (schemeYoneda S).obj U ⟶ Y.presheaf)
    (A : Subfunctor Y.presheaf) (hA : IsOpenImmersion A.ι) : Over S :=
  hA.rep.pullback π

/-- The open immersion from the restricted source to the original source scheme. -/
def toSource (π : (schemeYoneda S).obj U ⟶ Y.presheaf)
    (A : Subfunctor Y.presheaf) (hA : IsOpenImmersion A.ι) :
    sourceOverOpen π A hA ⟶ U :=
  hA.rep.snd π

/-- The restricted finite transformation to the open subfunctor. -/
def toOpen (π : (schemeYoneda S).obj U ⟶ Y.presheaf)
    (A : Subfunctor Y.presheaf) (hA : IsOpenImmersion A.ι) :
    (schemeYoneda S).obj (sourceOverOpen π A hA) ⟶ A.toFunctor :=
  hA.rep.fst π

theorem sourceOverOpen_square (π : (schemeYoneda S).obj U ⟶ Y.presheaf)
    (A : Subfunctor Y.presheaf) (hA : IsOpenImmersion A.ι) :
    IsPullback (toOpen π A hA) ((schemeYoneda S).map (toSource π A hA)) A.ι π :=
  hA.rep.isPullback π

theorem toSource_isOpenImmersion (π : (schemeYoneda S).obj U ⟶ Y.presheaf)
    (A : Subfunctor Y.presheaf) (hA : IsOpenImmersion A.ι) :
    _root_.AlgebraicGeometry.IsOpenImmersion (toSource π A hA).left :=
  hA.property_snd π

theorem toOpen_isFinite (π : (schemeYoneda S).obj U ⟶ Y.presheaf)
    (hπ : IsFinite π) (A : Subfunctor Y.presheaf) (hA : IsOpenImmersion A.ι) :
    IsFinite (toOpen π A hA) := by
  let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
      (Over.forget S))
  exact MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
      (Over.forget S)).relative (schemeYoneda S))
    (sourceOverOpen_square π A hA).flip hπ

theorem toOpen_isSurjective (π : (schemeYoneda S).obj U ⟶ Y.presheaf)
    (hπ : IsSurjective π) (A : Subfunctor Y.presheaf) (hA : IsOpenImmersion A.ι) :
    IsSurjective (toOpen π A hA) := by
  let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
    (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S))
  exact MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget S)).relative (schemeYoneda S))
    (sourceOverOpen_square π A hA).flip hπ

theorem range_toSource (π : (schemeYoneda S).obj U ⟶ Y.presheaf)
    (A : Subfunctor Y.presheaf) (hA : IsOpenImmersion A.ι) :
    Subfunctor.range ((schemeYoneda S).map (toSource π A hA)) = A.preimage π := by
  have h := range_eq_preimage_of_isPullback (sourceOverOpen_square π A hA)
  rwa [Subfunctor.range_ι] at h

/-- The restricted source factors through an affine source open if the target
open lies in its universal image. -/
theorem exists_toAffine (π : (schemeYoneda S).obj U ⟶ Y.presheaf)
    (A : Subfunctor Y.presheaf) (hA : IsOpenImmersion A.ι)
    (V : U.left.affineOpens) (hAV : A ≤ universalAffineOpen π V) :
    ∃ b : sourceOverOpen π A hA ⟶ affineOpenTest V,
      b ≫ affineOpenInclusion V = toSource π A hA := by
  have hpre : A.preimage π ≤
      Subfunctor.range ((schemeYoneda S).map (affineOpenInclusion V)) :=
    (universalImage_le_iff π _ A).mp hAV
  have hle : Subfunctor.range ((schemeYoneda S).map (toSource π A hA)) ≤
      Subfunctor.range ((schemeYoneda S).map (affineOpenInclusion V)) := by
    rw [range_toSource]
    exact hpre
  have hmem : ULift.up (toSource π A hA) ∈
      (Subfunctor.range ((schemeYoneda S).map (affineOpenInclusion V))).obj
        (op (sourceOverOpen π A hA)) := by
    apply hle
    exact ⟨ULift.up (𝟙 _), by simp⟩
  obtain ⟨⟨b⟩, hb⟩ := hmem
  refine ⟨b, ?_⟩
  change ULift.up (b ≫ affineOpenInclusion V) = ULift.up (toSource π A hA) at hb
  exact ULift.up_injective hb

/-- A finite source restricted to a compact open inside a universal affine-source
neighborhood is an actual quasi-affine scheme. -/
theorem sourceOverOpen_isQuasiAffine
    (π : (schemeYoneda S).obj U ⟶ Y.presheaf) (hπ : IsFinite π)
    (A : Subfunctor Y.presheaf) (hA : IsOpenImmersion A.ι)
    (hAc : IsQuasiCompact (OpenSubspaceGeometry.openSubspace Y A hA))
    (V : U.left.affineOpens) (hAV : A ≤ universalAffineOpen π V) :
    (sourceOverOpen π A hA).left.IsQuasiAffine := by
  obtain ⟨b, hb⟩ := exists_toAffine π A hA V hAV
  let : CompactSpace (sourceOverOpen π A hA).left :=
    OpenSubspaceGeometry.compactSpace_of_finite_source hAc
      (toOpen π A hA) (toOpen_isFinite π hπ A hA)
  let : IsAffine (affineOpenTest V).left := V.property
  let : _root_.AlgebraicGeometry.IsOpenImmersion (toSource π A hA).left :=
    toSource_isOpenImmersion π A hA
  have hcomp : b.left ≫ (affineOpenInclusion V).left = (toSource π A hA).left :=
    congrArg Over.Hom.left hb
  let : _root_.AlgebraicGeometry.IsOpenImmersion
      (b.left ≫ (affineOpenInclusion V).left) := by
    rw [hcomp]
    infer_instance
  let : _root_.AlgebraicGeometry.IsOpenImmersion b.left :=
    _root_.AlgebraicGeometry.IsOpenImmersion.of_comp b.left (affineOpenInclusion V).left
  exact Scheme.IsQuasiAffine.of_isImmersion b.left

end Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteAffineOpenRestriction
