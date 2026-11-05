import Langlands.GroupScheme.Rational.PointedLaurentCoordinates
import Langlands.GroupScheme.Rational.LaurentFrobeniusPullback

/-! # Finite Frobenius generators of actual primitive group coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Corepresented

variable {k : Type u} [Field k]
    {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
    {B : CommAlgCat.{u} (CommRingCat.of k)}
    (e : (F ⋙ forget GrpCat).CorepresentableBy B)
    {I : Type u} (σ : B →ₐ[k] AddMonoidAlgebra k (I → ℤ))
    (hε : (LaurentAugmentation.augmentation k (I → ℤ)).comp σ =
      AffineLinearEmbedding.counit e)

/-- The actual pointed Laurent pullback on primitive coordinate functions. -/
def primitiveLaurentPullback :
    primitiveFunctions e →ₗ[k] LaurentAugmentation.space k (I → ℤ) :=
  LaurentAugmentation.pointedPullback σ (primitiveFunctions e) (by
    intro b hb
    rw [← AlgHom.comp_apply, hε]
    exact counit_eq_zero_of_mem_primitiveFunctions e hb)

@[simp] theorem primitiveLaurentPullback_val (b : primitiveFunctions e) :
    (primitiveLaurentPullback e σ hε b).val = σ b := rfl

theorem primitiveLaurentPullback_injective (hσ : Function.Injective σ) :
    Function.Injective (primitiveLaurentPullback e σ hε) := by
  intro b c h
  apply Subtype.ext
  exact hσ (congrArg Subtype.val h)

variable {p : ℕ} [Fact p.Prime] [CharP k p]

open LaurentAugmentation in
open Classical in
/-- Finite primitive families admit Frobenius-independent replacements, retaining
their generated coordinate algebra and their full Laurent Frobenius span. -/
theorem exists_primitiveFrobGenerators (hσ : Function.Injective σ)
    (T : Finset (primitiveFunctions e)) :
    ∃ (s : Finset {m : I → ℤ // IsPrimitive p m})
      (G : Finset (primitiveFunctions e)),
      frobSpan k p I (primitiveLaurentPullback e σ hε '' (T : Set (primitiveFunctions e))) ≤
        finiteOrbitSpace k p I s ∧
      (primitiveLaurentPullback e σ hε '' (G : Set (primitiveFunctions e))) ⊆
        frobSpan k p I (primitiveLaurentPullback e σ hε '' (T : Set (primitiveFunctions e))) ∧
      frobSpan k p I (primitiveLaurentPullback e σ hε '' (T : Set (primitiveFunctions e))) =
        frobSpan k p I (primitiveLaurentPullback e σ hε '' (G : Set (primitiveFunctions e))) ∧
      Algebra.adjoin k (Subtype.val '' (T : Set (primitiveFunctions e))) =
        Algebra.adjoin k (Subtype.val '' (G : Set (primitiveFunctions e))) ∧
      TorusLinearization.FrobIndep
        (G.image (finiteEncoding k p I s ∘ primitiveLaurentPullback e σ hε)) := by
  exact exists_finiteFrobGenerators_pullback σ (primitiveFunctions e) _
    hσ (fun _ hb => pow_mem_primitiveFunctions e p hb) T

open LaurentAugmentation in
open Classical in
/-- Actual pointed split-torus domination supplies finite primitive replacements
with injective Laurent pullback and Frobenius-independent finite encodings. -/
theorem exists_pointed_primitiveFrobGenerators
    [IsReduced (groupScheme F e).X.left]
    (hdom : HasPointedSplitTorusDomination (groupScheme F e))
    (T : Finset (primitiveFunctions e)) :
    ∃ (I : Type u) (_ : Fintype I)
      (σ : B →ₐ[k] AddMonoidAlgebra k (I → ℤ))
      (hε : (augmentation k (I → ℤ)).comp σ = AffineLinearEmbedding.counit e)
      (s : Finset {m : I → ℤ // IsPrimitive p m})
      (G : Finset (primitiveFunctions e)),
      Function.Injective σ ∧
      frobSpan k p I (primitiveLaurentPullback e σ hε '' (G : Set (primitiveFunctions e))) ≤
        finiteOrbitSpace k p I s ∧
      Algebra.adjoin k (Subtype.val '' (T : Set (primitiveFunctions e))) =
        Algebra.adjoin k (Subtype.val '' (G : Set (primitiveFunctions e))) ∧
      TorusLinearization.FrobIndep
        (G.image (finiteEncoding k p I s ∘ primitiveLaurentPullback e σ hε)) := by
  obtain ⟨I, hI, σ, hσ, hε⟩ := exists_pointedLaurentPullback e hdom
  obtain ⟨s, G, hs, _, hspan, halg, hind⟩ :=
    exists_primitiveFrobGenerators e σ hε (p := p) hσ T
  exact ⟨I, hI, σ, hε, s, G, hσ, hspan ▸ hs, halg, hind⟩

end Langlands.GroupScheme.Corepresented
