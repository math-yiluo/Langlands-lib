import Langlands.AlgebraicGeometry.Picard.SquareGluingRestriction
import Langlands.AlgebraicGeometry.Picard.SquareTrivialEffectivity
import Langlands.AlgebraicGeometry.Picard.InfinitesimalSimultaneousTrivialization
import Langlands.AlgebraicGeometry.Picard.InfinitesimalAffineOpenNilpotence

/-! # Local effectivity for actual infinitesimal Picard gluing data -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.InfinitesimalLocalEffectivity

open InfinitesimalAffineOpenSquare

variable {Y₀ Y₁ Y₂ Y : Scheme.{u}}
  (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y)
  (w : i₁ ≫ j₁ = i₂ ≫ j₂)
  (D : PicardGroupoid.SquareGluingData i₁ i₂)

/-- The exact restricted datum is realized by the trivial line bundle. -/
def IsEffectiveOn (U : Y.Opens) : Prop :=
  Nonempty
    ((PicardGroupoid.squareGluingComparison
        (leftRestriction i₁ j₁ U) (rightRestriction i₁ i₂ j₁ j₂ w U)
        (j₁ ∣_ U) (j₂ ∣_ U) (restriction_comm i₁ i₂ j₁ j₂ w U)).obj
          (Core.mk (LineBundle.trivial U.toScheme)) ≅
      (SquareGluingRestriction.toOpen i₁ i₂ j₁ j₂ w U).obj D)

/-- An affine neighborhood whose exact restricted datum is realized by its
trivial line bundle under the ordinary square comparison. -/
structure EffectiveAffineNeighborhood (V : Y.Opens) (x : Y) where
  opens : Y.Opens
  affine : IsAffineOpen opens
  mem : x ∈ opens
  le : opens ≤ V
  effective : IsEffectiveOn i₁ i₂ j₁ j₂ w D opens

/-- Frames on the two exact inverse images realize the restricted datum. -/
lemma isEffectiveOn_of_frames (U : Y.Opens)
    (hi₂ : Function.Surjective (rightRestriction i₁ i₂ j₁ j₂ w U).appTop.hom)
    (hn : IsNilpotent (RingHom.ker (rightRestriction i₁ i₂ j₁ j₂ w U).appTop.hom))
    (τ₁ : (Scheme.Modules.pullback (j₁ ⁻¹ᵁ U).ι).obj D.left.of.obj ≅
      Langlands.SchemeModule.structureModule (j₁ ⁻¹ᵁ U).toScheme)
    (τ₂ : (Scheme.Modules.pullback (j₂ ⁻¹ᵁ U).ι).obj D.right.of.obj ≅
      Langlands.SchemeModule.structureModule (j₂ ⁻¹ᵁ U).toScheme) :
    IsEffectiveOn i₁ i₂ j₁ j₂ w D U :=
  ⟨SquareTrivialEffectivity.trivialObjectIso _ _ _ _ _ hi₂ hn _ τ₁ τ₂⟩

/-- Turn a simultaneous affine neighborhood into an effective one using the
nilpotent-surjective map of sections on its exact right overlap. -/
def ofSimultaneousNeighborhood {V : Y.Opens} {x : Y}
    (N : InfinitesimalSimultaneousTrivialization.SimultaneousAffineNeighborhood
      j₁ j₂ D.left.of D.right.of V x)
    (hi₂ : Function.Surjective
      (rightRestriction i₁ i₂ j₁ j₂ w N.opens).appTop.hom)
    (hn : IsNilpotent
      (RingHom.ker (rightRestriction i₁ i₂ j₁ j₂ w N.opens).appTop.hom)) :
    EffectiveAffineNeighborhood i₁ i₂ j₁ j₂ w D V x :=
  ⟨N.opens, N.affine, N.mem, N.le,
    isEffectiveOn_of_frames i₁ i₂ j₁ j₂ w D N.opens hi₂ hn
      N.fstTrivialization N.sndTrivialization⟩

section Relative

variable {k R A B C : Type u} [CommRing k]
  [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k R] [Algebra k A] [Algebra k B] [Algebra k C]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (p : R →ₐ[k] A) (q : R →ₐ[k] B) (a : A →ₐ[k] C) (b : B →ₐ[k] C)
  (h : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
    (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom))
  (hb : Function.Surjective b) (hn : IsNilpotent (RingHom.ker b.toRingHom))
  (D : PicardGroupoid.SquareGluingData
    ((relativeSpace f).map (affineBaseMap a))
    ((relativeSpace f).map (affineBaseMap b)))

/-- Every actual gluing datum is effective on an affine neighborhood of any
point, with the neighborhood contained in any prescribed open neighborhood. -/
def affineSquareNeighborhood
    (V : ((relativeSpace f).obj (affineBase k R)).Opens)
    (x : (relativeSpace f).obj (affineBase k R)) (hxV : x ∈ V) :
    EffectiveAffineNeighborhood
      ((relativeSpace f).map (affineBaseMap a))
      ((relativeSpace f).map (affineBaseMap b))
      ((relativeSpace f).map (affineBaseMap p))
      ((relativeSpace f).map (affineBaseMap q))
      (PicardGroupoid.relativeSquare_comm f _ _ _ _
        (PicardGroupoid.affineSquare_comm p q a b h)) D V x := by
  let N := InfinitesimalSimultaneousTrivialization.affineSquareNeighborhood
    f p q a b h hb hn D.left.of D.right.of
      (SquareTrivialEffectivity.overlapIso _ _ D) V x hxV
  have hnil := InfinitesimalAffineOpenNilpotence.rightRestriction_appTop_nilpotentSurjective
    f p q a b h hb hn N.opens N.affine
  exact ofSimultaneousNeighborhood _ _ _ _ _ D N hnil.1 hnil.2

end Relative

end Langlands.AlgebraicGeometry.Picard.InfinitesimalLocalEffectivity
