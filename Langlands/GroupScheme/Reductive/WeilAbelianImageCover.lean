import Langlands.GroupScheme.Reductive.RelativeDerivedInputs
import Langlands.GroupScheme.AffinePoints

/-! # Points of a group scheme are separated by an fppf cover of the base by affine pieces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Langlands.GroupScheme.AffineCoverSeparation

variable {A : Type u} [CommRing A]

/-- `X ⊗[A] P`, as an `A`-algebra. -/
abbrev tensorAlg (X P : CommAlgCat.{u} (CommRingCat.of A)) : CommAlgCat.{u} (CommRingCat.of A) :=
  CommAlgCat.of (CommRingCat.of A) (X ⊗[A] P)

/-- The inclusion `X → X ⊗[A] P`. -/
def inclLeft (X P : CommAlgCat.{u} (CommRingCat.of A)) : X ⟶ tensorAlg X P :=
  CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := X) (B := P))

variable {ι : Type u} (P : ι → CommAlgCat.{u} (CommRingCat.of A))
  (hflat : ∀ i, (algebraMap A (P i)).Flat)
  (hfp : ∀ i, (algebraMap A (P i)).FinitePresentation)
  (hsurj : ∀ p : PrimeSpectrum A, ∃ i, ∃ q : PrimeSpectrum (P i),
    PrimeSpectrum.comap (algebraMap A (P i)) q = p)

/-- The fppf cover of `Spec A` by the spectra of the algebras `P i`. -/
def specCover : Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation))
    (Spec (CommRingCat.of A)) :=
  Scheme.Cover.mkOfCovers ι (fun i => Spec (CommRingCat.of (P i)))
    (fun i => Spec.map (CommRingCat.ofHom (algebraMap A (P i))))
    (fun x => by
      obtain ⟨i, q, hq⟩ := hsurj x
      exact ⟨i, q, hq⟩)
    (fun i => ⟨(Flat.SpecMap_iff).2 (hflat i),
      (LocallyOfFinitePresentation.SpecMap_iff _).2 (hfp i)⟩)

include hflat hfp hsurj in
/-- **Separation of points by a cover.** Points of a group scheme `M` over `X` are equal if they
become equal over every `X ⊗[A] P i`, for an fppf family of `A`-algebras `P i` covering `Spec A`. -/
theorem affinePoint_eq_of_cover (M : GroupScheme (Spec (CommRingCat.of A)))
    (X : CommAlgCat.{u} (CommRingCat.of A)) (a b : M.affinePoints X)
    (h : ∀ i, M.affinePointMap (inclLeft X (P i)) a = M.affinePointMap (inclLeft X (P i)) b) :
    a = b := by
  let 𝒲 := (specCover P hflat hfp hsurj).pullback₁ ((algSpec (CommRingCat.of A)).obj (op X)).hom
  haveI := RelativeDerived.effectiveEpiFamily_fppfCover 𝒲
  apply Over.OverMorphism.ext
  apply EffectiveEpiFamily.hom_ext 𝒲.X 𝒲.f
  intro i
  have hi := congrArg CommaMorphism.left (h i)
  rw [affinePointMap_apply, affinePointMap_apply] at hi
  change Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A)
      (A := X) (B := P i))) ≫ a.left =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A)
      (A := X) (B := P i))) ≫ b.left at hi
  change pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A X)))
      (Spec.map (CommRingCat.ofHom (algebraMap A (P i)))) ≫ a.left =
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A X)))
      (Spec.map (CommRingCat.ofHom (algebraMap A (P i)))) ≫ b.left
  rw [← pullbackSpecIso_hom_fst A X (P i), Category.assoc, Category.assoc, hi]

end Langlands.GroupScheme.AffineCoverSeparation
