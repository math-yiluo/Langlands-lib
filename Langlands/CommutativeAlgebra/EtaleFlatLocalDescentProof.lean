import Mathlib
import Langlands.CommutativeAlgebra.EtaleLocalizedBaseChangeDescentStatement

/-! # Local flatness and local etaleness -/

open TensorProduct

namespace Langlands.CommutativeAlgebra

universe u v w x y

/-- Flatness descends along a faithfully flat extension of the source algebra. -/
theorem flat_of_flat_of_faithfullyFlat
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Flat A C] [Module.FaithfullyFlat B C] : Module.Flat A B := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  let F : B ⊗[A] N →ₗ[B] B ⊗[A] N' := AlgebraTensorModule.map (A := B) LinearMap.id f
  change Function.Injective F
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective B C F).mp
  have hmap : LinearMap.lTensor C F =
      (AlgebraTensorModule.cancelBaseChange A B C C N').symm.toLinearMap ∘ₗ
        (AlgebraTensorModule.map (A := C) LinearMap.id f) ∘ₗ
          (AlgebraTensorModule.cancelBaseChange A B C C N).toLinearMap := by
    ext c b
    simp [F]
  rw [hmap]
  exact (AlgebraTensorModule.cancelBaseChange A B C C N').symm.injective.comp
    ((Module.Flat.lTensor_preserves_injective_linearMap (M := C) f hf).comp
      (AlgebraTensorModule.cancelBaseChange A B C C N).injective)

set_option backward.isDefEq.respectTransparency false in
/-- A flat, formally unramified local algebra that is a localization of a finitely
presented algebra is formally etale. -/
theorem formallyEtale_of_flat_of_formallyUnramified
    (A B P : Type*) [CommRing A] [CommRing B] [CommRing P]
    [Algebra A B] [Algebra A P] [Algebra P B] [IsScalarTower A P B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    (M : Submonoid P) [IsLocalization M B] [Algebra.FinitePresentation A P]
    [Module.Flat A B] [Algebra.FormallyUnramified A B] :
    Algebra.FormallyEtale A B := by
  have : Algebra.EssFiniteType P B := Algebra.EssFiniteType.of_isLocalization B M
  have : Algebra.EssFiniteType A B := Algebra.EssFiniteType.comp A P B
  have : Algebra.FormallyEtale (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] B) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field _ _
  have : Algebra.FormallySmooth A B :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor M
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

set_option backward.isDefEq.respectTransparency false in
/-- Formal unramifiedness descends from a localization of a pushout if the
map from the original source algebra to that localization is faithfully flat. -/
theorem formallyUnramified_of_localized_baseChange
    (A T B D C : Type*) [CommRing A] [CommRing T] [CommRing B]
    [CommRing D] [CommRing C]
    [Algebra A T] [Algebra A B] [Algebra A D] [Algebra T D] [Algebra B D]
    [IsScalarTower A T D] [IsScalarTower A B D] [Algebra.IsPushout A T B D]
    [Algebra T C] [Algebra B C] [Algebra D C]
    [IsScalarTower T D C] [IsScalarTower B D C]
    (M : Submonoid D) [IsLocalization M C]
    [Module.FaithfullyFlat B C] [Algebra.FormallyUnramified T C] :
    Algebra.FormallyUnramified A B := by
  have : Algebra.FormallyEtale D C := Algebra.FormallyEtale.of_isLocalization M
  let e : C ⊗[B] Ω[B⁄A] ≃ₗ[C] Ω[C⁄T] :=
    (AlgebraTensorModule.cancelBaseChange B D C C Ω[B⁄A]).symm ≪≫ₗ
      (KaehlerDifferential.tensorKaehlerEquiv A T B D).baseChange D C _ _ ≪≫ₗ
        KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale T D C
  have : Subsingleton (C ⊗[B] Ω[B⁄A]) := e.subsingleton
  exact ⟨Module.FaithfullyFlat.lTensor_reflects_triviality B C _⟩

set_option backward.isDefEq.respectTransparency false in
/-- The local flat and formally unramified criterion for an algebra essentially
of finite presentation, using the Library's standard-presentation predicate. -/
theorem formallyEtale_of_flat_of_formallyUnramified_of_essFinitePresentation
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Module.Flat A B] [Algebra.FormallyUnramified A B]
    (h : Langlands.Algebra.EssFinitePresentation A B) :
    Algebra.FormallyEtale A B := by
  obtain ⟨n, I, hI, M, ⟨e⟩⟩ := h
  let P := MvPolynomial (Fin n) A ⧸ I
  let : Algebra P B := (e.toRingHom.comp (algebraMap P (Localization M))).toAlgebra
  have : IsScalarTower A P B :=
      IsScalarTower.of_algebraMap_eq (R := A) (S := P) (A := B) fun a ↦ by
    change algebraMap A B a = e (algebraMap P (Localization M) (algebraMap A P a))
    rw [← IsScalarTower.algebraMap_apply A P (Localization M), e.commutes]
  let e' : Localization M ≃ₐ[P] B :=
    { e.toRingEquiv with commutes' := fun _ ↦ rfl }
  have : IsLocalization M B :=
    IsLocalization.isLocalization_of_algEquiv (S := Localization M) M e'
  have : Algebra.FinitePresentation A P := Algebra.FinitePresentation.quotient hI
  exact formallyEtale_of_flat_of_formallyUnramified A B P M

/-- The exact local algebra descent proposition. -/
theorem etaleLocalizedBaseChangeDescent :
    EtaleLocalizedBaseChangeDescentStatement.{u, v, w, x, y} := by
  intro A T B D C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    M _ _ _ _ h
  have : Module.Flat A B := flat_of_flat_of_faithfullyFlat A B C
  have : Algebra.FormallyUnramified A B :=
    formallyUnramified_of_localized_baseChange A T B D C M
  exact formallyEtale_of_flat_of_formallyUnramified_of_essFinitePresentation A B h

end Langlands.CommutativeAlgebra
