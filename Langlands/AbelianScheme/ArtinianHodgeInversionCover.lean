import Langlands.AbelianScheme.ArtinianHodgeStructureCohomology
import Langlands.AlgebraicGeometry.AffineCechDeRhamCoverPullback
import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqDegreeTwoSum

/-! # An affine cover on which inversion acts by exchanging charts -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

open Langlands.Cohomology
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter)

section Doubling

variable {X : Scheme.{u}} (U : Scheme.AffineOpenCover.{u} X) (a : X ⟶ X) [IsIso a]

/-- The affine cover consisting of the original charts and their images by an automorphism. -/
def doubledCover : Scheme.AffineOpenCover.{u} X where
  I₀ := Bool × U.I₀
  X ij := U.X ij.2
  f ij := if ij.1 then U.f ij.2 ≫ a else U.f ij.2
  idx x := (false, U.idx x)
  covers x := U.covers x
  map_prop := by
    rintro ⟨b, i⟩
    cases b
    · exact U.map_prop i
    · exact inferInstanceAs (IsOpenImmersion (U.f i ≫ a))

instance [Finite U.I₀] : Finite (doubledCover U a).I₀ := inferInstanceAs (Finite (Bool × U.I₀))

/-- Exchange the original chart and its image. -/
abbrev swapChart (ij : (doubledCover U a).I₀) : (doubledCover U a).I₀ := (!ij.1, ij.2)

lemma swapChart_swapChart (ij : (doubledCover U a).I₀) :
    swapChart U a (swapChart U a ij) = ij := by
  obtain ⟨b, i⟩ := ij
  cases b <;> rfl

lemma doubledCover_le_preimage (ha : a ≫ a = 𝟙 X) (ij : (doubledCover U a).I₀) :
    coverOpens (doubledCover U a) ij ≤
      a ⁻¹ᵁ coverOpens (doubledCover U a) (swapChart U a ij) := by
  rcases ij with ⟨b, i⟩
  cases b <;> intro x hx
  · rcases hx with ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · rcases hx with ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    change U.f i y = a (a (U.f i y))
    rw [← Scheme.Hom.comp_apply, ha]
    rfl

end Doubling

section Involutions

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {U : Scheme.AffineOpenCover.{u} X} (a : X ⟶ X) (ha : a ≫ f = f)
  (β : U.I₀ → U.I₀) (hβ : ∀ i, coverOpens U i ≤ a ⁻¹ᵁ coverOpens U (β i))

/-- The pullback of a scheme involution that permutes the cover by an involution
is a cochain involution. -/
lemma pullFunctions_involutive (hs : a ≫ a = 𝟙 X) (hb : Function.Involutive β) (p : ℕ) :
    Function.Involutive (pullFunctions a ha β hβ p) := by
  intro c
  change Cech.pull a (coverOpens U) (coverOpens U) β hβ p
    (Cech.pull a (coverOpens U) (coverOpens U) β hβ p c) = c
  rw [Cech.pull_comp]
  funext σ
  rw [Cech.pull_apply]
  have hσ : (β ∘ β) ∘ σ = σ := funext fun j => hb (σ j)
  have e : inter (coverOpens U) σ ≤ (a ≫ a) ⁻¹ᵁ inter (coverOpens U) σ := by
    rw [hs]
    exact le_rfl
  rw [Cech.appLE_congr_idx _ c hσ _ e]
  have hi := Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof.appLE_congr_hom
    hs _ _ e
  rw [hi]
  change (X.presheaf.map (𝟙 (op (inter (coverOpens U) σ)))) (c σ) = c σ
  rw [X.presheaf.map_id]
  rfl

end Involutions

end Langlands.AlgebraicGeometry.AffineCechDeRham

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.AffineCechDeRham

variable {S : Scheme.{u}} (B : AbelianScheme S)

/-- Inversion on the underlying scheme is an isomorphism. -/
instance inversion_left_isIso : IsIso ι[B.X].left := (Over.forget S).map_isIso ι[B.X]

lemma inversion_left_sq : ι[B.X].left ≫ ι[B.X].left = 𝟙 B.X.left := by
  change (Over.forget S).map (ι[B.X] ≫ ι[B.X]) = (Over.forget S).map (𝟙 _)
  congr 1
  simp

variable (U : Scheme.AffineOpenCover.{u} B.X.left)

/-- The supplied charts and their images under group inversion. -/
abbrev inversionCover := doubledCover U ι[B.X].left

/-- The original chart inside the cover adapted to inversion. -/
abbrev inversionOriginalChart (i : U.I₀) : (inversionCover B U).I₀ := (false, i)

lemma inversionOriginalChart_le (i : U.I₀) :
    coverOpens U i ≤ (𝟙 B.X.left : B.X.left ⟶ B.X.left) ⁻¹ᵁ
      coverOpens (inversionCover B U) (inversionOriginalChart B U i) :=
  le_rfl

end Langlands.AbelianScheme
