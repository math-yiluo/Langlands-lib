import Langlands.Algebra.EssFinitePresentationTowerCancellationStatement
import Langlands.Algebra.TensorRetractionKernelFGProof
import Langlands.Algebra.EssFinitePresentationBaseChangeProof
import Langlands.Algebra.EssFinitePresentationFiniteQuotient
import Mathlib.RingTheory.EssentialFiniteness

/-! # Cancellation of essential finite presentation in an algebra tower -/

universe u v w

open scoped TensorProduct

namespace Langlands.Algebra

private theorem essFiniteType_of_essFinitePresentation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (h : EssFinitePresentation R S) : _root_.Algebra.EssFiniteType R S := by
  obtain ⟨n, I, hI, M, ⟨e⟩⟩ := h
  have : _root_.Algebra.FinitePresentation R (MvPolynomial (Fin n) R ⧸ I) :=
    _root_.Algebra.FinitePresentation.quotient hI
  exact (_root_.Algebra.EssFiniteType.iff_of_algEquiv
    (S := Localization M) e).mp inferInstance

/-- Essential finite presentation cancels in a compatible algebra tower, with
the given algebra structures and three independent universes. -/
theorem essFinitePresentationTowerCancellation :
    EssFinitePresentationTowerCancellationStatement.{u,v,w} := by
  intro R S T _ _ _ _ _ _ _ hS hT
  let μ : S ⊗[R] T →ₐ[S] T := (AlgHom.liftEquiv R S T T) (AlgHom.id R T)
  have hμ : Function.Surjective μ := by
    intro t
    exact ⟨1 ⊗ₜ[R] t, by simp [μ]⟩
  have hker : (RingHom.ker μ.toRingHom).FG :=
    tensorRetractionKernelFG R S T (essFiniteType_of_essFinitePresentation hS)
  have hQ : EssFinitePresentation S ((S ⊗[R] T) ⧸ RingHom.ker μ.toRingHom) :=
    essFinitePresentationFiniteQuotient S (S ⊗[R] T) (RingHom.ker μ.toRingHom)
      (essFinitePresentation_baseChange S hT) hker
  exact essFinitePresentation_of_algEquiv (Ideal.quotientKerAlgEquivOfSurjective hμ) hQ

end Langlands.Algebra
