import Langlands.AlgebraicGeometry.Picard.AffineLineBundlePicard
import Langlands.AlgebraicGeometry.Modules.TildeRankOneSpreading
import Mathlib.RingTheory.Localization.BaseChange

/-! # Generic trivializations on total principal neighbourhoods -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Picard

/-- The actual affine sections, with their canonical spectrum coefficient
structure, form an invertible module over the defining ring. -/
theorem invertible_moduleSpecΓ_of_lineBundle {B : CommRingCat.{u}}
    (L : LineBundle (Spec B)) :
    Module.Invertible B (moduleSpecΓFunctor.obj L.obj) := by
  let G := Γ(Spec B, ⊤)
  let M := Γ(L.obj, ⊤)
  let V := Module.Dual G M
  have : Module.Invertible G M := invertible_sections_of_lineBundle L
  have hb : Function.Bijective (algebraMap B G) :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv
  have : TensorProduct.CompatibleSMul B G V M :=
    .of_algebraMap_surjective V M hb.surjective
  let a : B ≃ₗ[B] G := LinearEquiv.ofBijective (Algebra.linearMap B G) hb
  exact Module.Invertible.right
    (TensorProduct.equivOfCompatibleSMul G B B V M ≪≫ₗ
      (Module.Invertible.linearEquiv G M).restrictScalars B ≪≫ₗ a.symm)

variable {R A : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
  [CommRing A] [Algebra R A] [Algebra.Smooth R A]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  (P : Ideal A) [P.IsPrime]

/-- Localizing a generic smooth affine algebra at all total-space
functions outside a specified prime kills its module Picard group. -/
theorem subsingleton_pic_generic_localization :
    Subsingleton (CommRing.Pic
      (Localization (Algebra.algebraMapSubmonoid (A ⊗[R] K) P.primeCompl))) := by
  let T := Localization.AtPrime P ⊗[R] K
  have hT : Subsingleton (CommRing.Pic T) :=
    Langlands.CommutativeAlgebra.subsingleton_pic_of_isLocalization_of_regularLocal
      (Langlands.CommutativeAlgebra.finitelyPresentedRegularRing_atPrime_of_smoothAt_of_valuationRing
        (R := R) P)
      (Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors R))
  let C := Localization.AtPrime P ⊗[A] (A ⊗[R] K)
  let : Algebra (A ⊗[R] K) C := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization
      (Algebra.algebraMapSubmonoid (A ⊗[R] K) P.primeCompl) C :=
    IsLocalization.tensorRight (R := A) (S := A ⊗[R] K)
      (Localization.AtPrime P) P.primeCompl
  let e : C ≃+* T :=
    (Algebra.TensorProduct.cancelBaseChange R A A (Localization.AtPrime P) K).toRingEquiv
  have : Subsingleton (CommRing.Pic C) :=
    Langlands.CommutativeAlgebra.subsingleton_pic_of_ringEquiv e.symm
  exact Langlands.CommutativeAlgebra.subsingleton_pic_of_ringEquiv
    (IsLocalization.algEquiv
      (Algebra.algebraMapSubmonoid (A ⊗[R] K) P.primeCompl)
      C (Localization _)).toRingEquiv

/-- An invertible module on the generic affine scheme is trivial after
inverting one total-space function outside the specified prime. -/
theorem exists_generic_principal_module_trivialization
    (N : Type u) [AddCommGroup N] [Module (A ⊗[R] K) N]
    [Module.Invertible (A ⊗[R] K) N] :
    ∃ a : A, a ∉ P ∧ Nonempty
      (LocalizedModule.Away (algebraMap A (A ⊗[R] K) a) N ≃ₗ[
        Localization.Away (algebraMap A (A ⊗[R] K) a)]
        Localization.Away (algebraMap A (A ⊗[R] K) a)) := by
  let B := A ⊗[R] K
  let S := Algebra.algebraMapSubmonoid B P.primeCompl
  have : Subsingleton (CommRing.Pic (Localization S)) :=
    subsingleton_pic_generic_localization K P
  have : Module.FinitePresentation B N :=
    Module.finitePresentation_of_projective B N
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (CommRing.Pic.subsingleton_iff.mp
      (inferInstance : Subsingleton (CommRing.Pic (Localization S)))
      (LocalizedModule S N) inferInstance)
  obtain ⟨b, hb, l, _⟩ :=
    Module.FinitePresentation.exists_lift_equiv_of_isLocalizedModule S
      (LocalizedModule.mkLinearMap S N) (Algebra.linearMap B (Localization S))
      (e.restrictScalars B)
  obtain ⟨a, ha, rfl⟩ := hb
  let a' : LocalizedModule.Away (algebraMap A B a) B ≃ₗ[
      Localization.Away (algebraMap A B a)] Localization.Away (algebraMap A B a) :=
    LocalizedModule.equivTensorProduct (.powers (algebraMap A B a)) B ≪≫ₗ
      TensorProduct.AlgebraTensorModule.rid B _ _
  exact ⟨a, ha, ⟨l ≪≫ₗ a'⟩⟩

/-- The actual generic line bundle is trivial over the generic part of
one total principal neighbourhood of the specified prime. -/
theorem exists_generic_principal_lineBundle_trivialization
    (D : LineBundle (Spec (CommRingCat.of (A ⊗[R] K)))) :
    ∃ a : A, a ∉ P ∧ Nonempty
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap (A ⊗[R] K)
          (Localization.Away (algebraMap A (A ⊗[R] K) a)))))).obj D.obj ≅
        SheafOfModules.unit (Spec (CommRingCat.of
          (Localization.Away (algebraMap A (A ⊗[R] K) a)))).ringCatSheaf) := by
  let B : CommRingCat.{u} := .of (A ⊗[R] K)
  let M := moduleSpecΓFunctor.obj D.obj
  have : Module.Invertible B M := invertible_moduleSpecΓ_of_lineBundle D
  obtain ⟨a, ha, ⟨e⟩⟩ := exists_generic_principal_module_trivialization (R := R) (A := A) K P M
  let C : CommRingCat.{u} := .of (Localization.Away (algebraMap A B a))
  let f := Spec.map (CommRingCat.ofHom (algebraMap B C))
  let e' : C ⊗[B] M ≃ₗ[C] C :=
    (LocalizedModule.equivTensorProduct (.powers (algebraMap A B a)) M).symm ≪≫ₗ e
  exact ⟨a, ha, ⟨(Scheme.Modules.pullback f).mapIso (asIso D.obj.fromTildeΓ).symm ≪≫
    Langlands.Scheme.Modules.tildePullbackAlgebraIso B C M ≪≫
      (tilde.functor C).mapIso e'.toModuleIso ≪≫ tildeSelf⟩⟩

/-- Choose a total function outside the specified prime together with an
actual trivialization on the generic part of its principal neighbourhood. -/
def genericPrincipalLineBundleTrivialization
    (D : LineBundle (Spec (CommRingCat.of (A ⊗[R] K)))) :
    Σ a : {a : A // a ∉ P},
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap (A ⊗[R] K)
          (Localization.Away (algebraMap A (A ⊗[R] K) a.1)))))).obj D.obj ≅
        SheafOfModules.unit (Spec (CommRingCat.of
          (Localization.Away (algebraMap A (A ⊗[R] K) a.1)))).ringCatSheaf :=
  let h := exists_generic_principal_lineBundle_trivialization K P D
  ⟨⟨h.choose, h.choose_spec.1⟩, h.choose_spec.2.some⟩

end Langlands.AlgebraicGeometry.Picard
