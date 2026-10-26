import Langlands.Algebra.EssFinitePresentationTransportStatement
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RingHom.FinitePresentation

/-! # Essential finite presentation: localization and isomorphism transport -/

universe u v w

namespace Langlands.Algebra

/-- An arbitrary localization of a finitely presented algebra is essentially of
finite presentation, with independent universes for all three rings. -/
theorem essFinitePresentation_of_isLocalization
    (R : Type u) (A : Type v) (B : Type w)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [_root_.Algebra.FinitePresentation R A]
    (M : Submonoid A) [IsLocalization M B] :
    EssFinitePresentation R B := by
  obtain ⟨n, I, e, hI⟩ :=
    _root_.Algebra.FinitePresentation.iff.mp
      (inferInstance : _root_.Algebra.FinitePresentation R A)
  let N : Submonoid (MvPolynomial (Fin n) R ⧸ I) := M.comap e
  refine ⟨n, I, hI, N, ⟨?_⟩⟩
  exact IsLocalization.algEquivOfAlgEquiv (Localization N) B e
    (Submonoid.map_comap_eq_of_surjective e.surjective M)

/-- Essential finite presentation is preserved by an algebra isomorphism of the target. -/
theorem essFinitePresentation_of_algEquiv
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (e : S ≃ₐ[R] T) (h : EssFinitePresentation R S) :
    EssFinitePresentation R T := by
  obtain ⟨n, I, hI, M, ⟨a⟩⟩ := h
  exact ⟨n, I, hI, M, ⟨a.trans e⟩⟩

/-- The inline ring-hom interpretation of essential finite presentation respects
both source and target isomorphisms, with the induced algebra structures. -/
theorem essFinitePresentation_respectsIso :
    RingHom.RespectsIso
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) =>
        @EssFinitePresentation R S _ _ f.toAlgebra) := by
  constructor
  · intro R S T _ _ _ f e hf
    let : Algebra R S := f.toAlgebra
    let : Algebra R T := (e.toRingHom.comp f).toAlgebra
    let a : S ≃ₐ[R] T := { e with commutes' := fun _ => rfl }
    exact essFinitePresentation_of_algEquiv a hf
  · intro R S T _ _ _ f e hf
    let : Algebra S T := f.toAlgebra
    obtain ⟨n, I, hI, M, ⟨a⟩⟩ := hf
    let A := MvPolynomial (Fin n) S ⧸ I
    let : Algebra R A := ((algebraMap S A).comp e.toRingHom).toAlgebra
    let : Algebra R T := (f.comp e.toRingHom).toAlgebra
    let : Algebra A T :=
      (a.toRingEquiv.toRingHom.comp (algebraMap A (Localization M))).toAlgebra
    have : _root_.Algebra.FinitePresentation S A :=
      _root_.Algebra.FinitePresentation.quotient hI
    have : _root_.Algebra.FinitePresentation R A :=
      RingHom.finitePresentation_respectsIso.2 (algebraMap S A) e
        (RingHom.finitePresentation_algebraMap.mpr inferInstance)
    let b : Localization M ≃ₐ[A] T :=
      { a.toRingEquiv with commutes' := fun _ => rfl }
    have : IsLocalization M T :=
      IsLocalization.isLocalization_of_algEquiv (S := Localization M) M b
    have : IsScalarTower R A T :=
      IsScalarTower.of_algebraMap_eq fun r => by
        change f (e r) =
          a (algebraMap A (Localization M) (algebraMap S A (e r)))
        rw [← IsScalarTower.algebraMap_apply S A (Localization M)]
        exact (a.commutes (e r)).symm
    exact essFinitePresentation_of_isLocalization R A T M

/-- The exact published localization-construction and isomorphism-transport proposition. -/
theorem essFinitePresentationTransport :
    EssFinitePresentationTransportStatement.{u, v, w} :=
  ⟨essFinitePresentation_of_isLocalization, essFinitePresentation_respectsIso⟩

example : EssFinitePresentationTransportStatement.{u, v, w} :=
  @essFinitePresentationTransport.{u, v, w}

end Langlands.Algebra
