import Langlands.GroupScheme.Adjoint.Normalizer
import Langlands.GroupScheme.Adjoint.RealCocharacterProof

/-! # Adjoint translation coordinates and actual normalizer equivariance -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.Geometry.Building Langlands.GroupScheme.RealTorusSpace

namespace Langlands.GroupScheme.IsAdjointSplitTorusImage

variable {k : Type u} [Field k]
variable {G A : GroupScheme (Spec (CommRingCat.of k))}
variable {T T_ad : CommGroupScheme (Spec (CommRingCat.of k))}
variable {q : G ⟶ A} {i : T.toGrp ⟶ G} {j : T_ad.toGrp ⟶ A} {p : T ⟶ T_ad}
variable (h : IsAdjointSplitTorusImage q i j p)

section Linear

variable [Mono i.hom.hom.left] [Mono j.hom.hom.left]

/-- The actual torus map intertwines the actual normalizer actions on real cocharacters. -/
theorem cocharacterMapReal_normalizerAction (n : normalizerPoints i) (v : V T) :
    cocharacterMapReal p (normalizerAction i n v) =
      normalizerAction j (h.normalizerPointsMap n) (cocharacterMapReal p v) := by
  induction v using TensorProduct.inductionOn with
  | tmul r ν =>
    simp only [normalizerAction_tmul, cocharacterMapReal_tmul,
      Category.assoc, h.normalizingAut_comp n]
  | add v w hv hw => simp only [map_add, hv, hw]

end Linear

variable [IsAffineHom G.X.hom]

/-- Translation coordinates in the actual adjoint torus, induced by the actual torus map. -/
def translationEquiv : TranslationSpace i ≃ₗ[ℝ] V T_ad :=
  Classical.choose (adjointRealCocharacterComparison k G A T T_ad q i j p h).2.2

/-- The translation equivalence is the actual map on quotient representatives. -/
theorem translationEquiv_mk (v : V T) :
    h.translationEquiv (Submodule.Quotient.mk v) = cocharacterMapReal p v :=
  Classical.choose_spec (adjointRealCocharacterComparison k G A T T_ad q i j p h).2.2 v

/-- The representative formula determines the translation equivalence uniquely. -/
theorem translationEquiv_unique (e : TranslationSpace i ≃ₗ[ℝ] V T_ad)
    (he : ∀ v : V T, e (Submodule.Quotient.mk v) = cocharacterMapReal p v) :
    e = h.translationEquiv := by
  apply LinearEquiv.ext
  intro v
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  rw [he, h.translationEquiv_mk]

variable [Mono i.hom.hom.left]

/-- Adjoint translation coordinates intertwine the actual quotient derivative
with the actual target normalizer action. -/
theorem translationEquiv_translationAction [Mono j.hom.hom.left] (n : normalizerPoints i)
    (v : TranslationSpace i) :
    h.translationEquiv (translationAction i n v) =
      normalizerAction j (h.normalizerPointsMap n) (h.translationEquiv v) := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  rw [translationAction_mk, h.translationEquiv_mk, h.translationEquiv_mk]
  exact h.cocharacterMapReal_normalizerAction n w

variable {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- The displacement of two points of the same valuation apartment, in the
actual adjoint torus coordinates. -/
def adjointDisplacement (x y : D.Apartment) : V T_ad :=
  h.translationEquiv (x -ᵥ y)

/-- Adjoint displacement is additive along a chain of apartment points. -/
theorem adjointDisplacement_add (x y z : D.Apartment) :
    h.adjointDisplacement D x y + h.adjointDisplacement D y z =
      h.adjointDisplacement D x z := by
  rw [adjointDisplacement, adjointDisplacement, adjointDisplacement,
    ← map_add, vsub_add_vsub_cancel]

/-- Translating the first apartment point adds the corresponding adjoint vector. -/
theorem adjointDisplacement_vadd (v : TranslationSpace i) (x y : D.Apartment) :
    h.adjointDisplacement D (v +ᵥ x) y =
      h.translationEquiv v + h.adjointDisplacement D x y := by
  rw [adjointDisplacement, vadd_vsub_assoc, map_add, adjointDisplacement]

/-- On the same actual valuation apartment, conjugation of both points has
the actual adjoint normalizer action on their displacement. -/
theorem adjointDisplacement_smul [Mono j.hom.hom.left]
    (n : normalizerPoints i) (x y : D.Apartment) :
    h.adjointDisplacement D (n • x) (n • y) =
      normalizerAction j (h.normalizerPointsMap n) (h.adjointDisplacement D x y) := by
  have hd : (n • x) -ᵥ (n • y) = translationAction i n (x -ᵥ y) := by
    simpa only [vsub_vadd, vadd_vsub] using
      congrArg (fun z : D.Apartment => z -ᵥ (n • y)) (D.smul_vadd n (x -ᵥ y) y)
  rw [adjointDisplacement, hd, h.translationEquiv_translationAction, adjointDisplacement]

end Langlands.GroupScheme.IsAdjointSplitTorusImage
