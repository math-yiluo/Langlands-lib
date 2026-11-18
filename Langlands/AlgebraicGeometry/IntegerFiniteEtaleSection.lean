import Langlands.Algebra.IntegerFiniteEtalePicard
import Langlands.GroupScheme.Multiplicative
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Sections of finite étale covers of the integers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Algebra

/-- A nonzero module-finite étale integer algebra has an integer point. -/
theorem nonempty_intPoint_of_finiteEtale (A : Type u) [CommRing A] [Nontrivial A]
    [Algebra.Etale ℤ A] [Module.Finite ℤ A] : Nonempty (A →+* ℤ) := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (bot_ne_top : (⊥ : Ideal A) ≠ ⊤)
  exact ⟨minimalPrimePoint A hp⟩

end Langlands.Algebra

namespace Langlands.AlgebraicGeometry

/-- Every finite étale surjective morphism to the lifted integer spectrum
has a section over that original base. -/
def IntegerFiniteEtaleSectionStatement : Prop :=
  ∀ {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)))
    [IsFinite p] [Etale p] [Surjective p],
    ∃ σ : Spec (CommRingCat.of (ULift.{u} ℤ)) ⟶ X, σ ≫ p = 𝟙 _

/-- A finite étale surjective morphism to the lifted integer spectrum has a
section over the original base. -/
theorem exists_section_of_finiteEtale_integer
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)))
    [IsFinite p] [Etale p] [Surjective p] :
    ∃ σ : Spec (CommRingCat.of (ULift.{u} ℤ)) ⟶ X, σ ≫ p = 𝟙 _ := by
  have : IsAffine X := isAffine_of_isAffineHom p
  let φ := Spec.preimage (X.isoSpec.inv ≫ p)
  have hφ : Spec.map φ = X.isoSpec.inv ≫ p := Spec.map_preimage _
  have : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hne : Nonempty X := by
    obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of (ULift.{u} ℤ))))
    obtain ⟨x, _⟩ := p.surjective z
    exact ⟨x⟩
  have : Nontrivial Γ(X, ⊤) := by
    obtain ⟨x⟩ := hne
    exact PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨X.isoSpec.hom x⟩
  algebraize [φ.hom]
  let : SMul (ULift.{u} ℤ) Γ(X, ⊤) := Algebra.toSMul
  let : Module (ULift.{u} ℤ) Γ(X, ⊤) := Algebra.toModule
  let : IsScalarTower ℤ (ULift.{u} ℤ) Γ(X, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have : Module.Finite (ULift.{u} ℤ) Γ(X, ⊤) :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff φ).mp ‹IsFinite (Spec.map φ)›)
  have : Algebra.Etale (ULift.{u} ℤ) Γ(X, ⊤) :=
    RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale)).mp ‹Etale (Spec.map φ)›)
  let e : ℤ ≃ₐ[ℤ] ULift.{u} ℤ := ULift.algEquiv.symm
  have : Algebra.Etale ℤ (ULift.{u} ℤ) := Algebra.Etale.of_equiv e
  have : Module.Finite ℤ (ULift.{u} ℤ) := Module.Finite.equiv e.toLinearEquiv
  have : Algebra.Etale ℤ Γ(X, ⊤) := Algebra.Etale.comp ℤ (ULift.{u} ℤ) Γ(X, ⊤)
  have : Module.Finite ℤ Γ(X, ⊤) := Module.Finite.trans (ULift.{u} ℤ) Γ(X, ⊤)
  obtain ⟨a⟩ := Langlands.Algebra.nonempty_intPoint_of_finiteEtale Γ(X, ⊤)
  refine ⟨Spec.map (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp a)) ≫
    X.isoSpec.inv, ?_⟩
  exact specULiftZIsTerminal.hom_ext _ _

end Langlands.AlgebraicGeometry
