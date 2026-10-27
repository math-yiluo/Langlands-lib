import Langlands.Algebra.EssFinitePresentationBaseChangeStatement
import Langlands.Algebra.EssFinitePresentationTransportProof
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Localization.BaseChange

/-! # Essential finite presentation under base change (Stacks 0AUF): proof -/

universe u v w z

open scoped TensorProduct

namespace Langlands.Algebra

/-- Let `Q` be a finitely presented `R`-algebra, `M` an arbitrary submonoid of `Q`, and
`e : Localization M ≃ₐ[R] A`. Then for an arbitrary `R`-algebra `B`, the base change `B ⊗[R] A`
is essentially of finite presentation over `B`. -/
theorem essFinitePresentation_baseChange_of_algEquiv_localization
    {R : Type u} {Q : Type v} {A : Type w} (B : Type z)
    [CommRing R] [CommRing Q] [CommRing A] [CommRing B]
    [Algebra R Q] [Algebra R A] [Algebra R B] [_root_.Algebra.FinitePresentation R Q]
    (M : Submonoid Q) (e : Localization M ≃ₐ[R] A) :
    EssFinitePresentation B (B ⊗[R] A) := by
  let φ : B ⊗[R] Q →ₐ[B] B ⊗[R] Localization M :=
    _root_.Algebra.TensorProduct.map (AlgHom.id B B)
      (IsScalarTower.toAlgHom R Q (Localization M))
  let : Algebra (B ⊗[R] Q) (B ⊗[R] Localization M) := φ.toAlgebra
  have : IsScalarTower B (B ⊗[R] Q) (B ⊗[R] Localization M) :=
    IsScalarTower.of_algebraMap_eq fun b => (φ.commutes b).symm
  have H : (algebraMap (B ⊗[R] Q) (B ⊗[R] Localization M)).comp
        _root_.Algebra.TensorProduct.includeRight.toRingHom =
      _root_.Algebra.TensorProduct.includeRight.toRingHom.comp
        (algebraMap Q (Localization M)) :=
    RingHom.ext fun q => by
      change φ (1 ⊗ₜ q) = 1 ⊗ₜ algebraMap Q (Localization M) q
      simp [φ]
  have : IsLocalization (M.map (_root_.Algebra.TensorProduct.includeRight (R := R) (A := B)))
      (B ⊗[R] Localization M) :=
    IsLocalization.tensorProduct_tensorProduct_right R B M (Localization M) H
  have hL : EssFinitePresentation B (B ⊗[R] Localization M) :=
    essFinitePresentation_of_isLocalization B (B ⊗[R] Q) (B ⊗[R] Localization M)
      (M.map (_root_.Algebra.TensorProduct.includeRight (R := R) (A := B)))
  exact essFinitePresentation_of_algEquiv
    (_root_.Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) e) hL

/-- Base change along an arbitrary `R`-algebra `B` preserves essential finite presentation:
if `A` is essentially of finite presentation over `R`, then `B ⊗[R] A`, with its left-factor
`B`-algebra structure, is essentially of finite presentation over `B`. -/
theorem essFinitePresentation_baseChange
    {R : Type u} {A : Type v} (B : Type w)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (h : EssFinitePresentation R A) : EssFinitePresentation B (B ⊗[R] A) := by
  obtain ⟨n, I, hI, M, ⟨e⟩⟩ := h
  have : _root_.Algebra.FinitePresentation R (MvPolynomial (Fin n) R ⧸ I) :=
    _root_.Algebra.FinitePresentation.quotient hI
  exact essFinitePresentation_baseChange_of_algEquiv_localization B M e

/-- The exact published base-change proposition (Stacks 0AUF). -/
theorem essFinitePresentationBaseChange : EssFinitePresentationBaseChangeStatement.{u, v, w} :=
  fun _ _ B _ _ _ _ _ h => essFinitePresentation_baseChange B h

example : EssFinitePresentationBaseChangeStatement.{u, v, w} :=
  @essFinitePresentationBaseChange.{u, v, w}

end Langlands.Algebra
