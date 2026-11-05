import Langlands.AlgebraicGeometry.Modules.IdealAdicQuotients
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Descent through actual ideal quotients -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Modules.IdealAdic

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)

local instance idealAdicQuotientDescentInst1 : (Scheme.Modules.toPresheafOfModules X).Additive :=
  inferInstanceAs (SheafOfModules.forget X.ringCatSheaf).Additive

local instance idealAdicQuotientDescentInst2 : (sheafify X).Additive :=
  (sheafifyAdjunction X).left_adjoint_additive

/-- Vanishing on the sheaf of ideal multiples is equivalent to vanishing on
all of its sectionwise generators. -/
lemma inclusion_comp_eq_zero_iff (I : Ideal R) {M N : X.Modules} (φ : M ⟶ N) :
    inclusion f I M ≫ φ = 0 ↔
      ∀ (U : X.Opens) (a : R), a ∈ I → ∀ m : Γ(M, U),
        φ.app U (scalar f U a • m) = 0 := by
  have hAdj : (sheafifyAdjunction X).homEquiv _ N (inclusion f I M ≫ φ) =
      (multiplePresubmodule f I M).ι ≫ φ.val := by
    unfold inclusion
    rw [Category.assoc]
    change (sheafifyAdjunction X).homEquiv _ N
      ((sheafify X).map (multiplePresubmodule f I M).ι ≫
        (sheafifyAdjunction X).counit.app M ≫ φ) = _
    rw [Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right,
      ← Adjunction.homEquiv_symm_id]
    erw [Equiv.apply_symm_apply, Category.id_comp]
    rfl
  constructor
  · intro h U a ha m
    have hp : (multiplePresubmodule f I M).ι ≫ φ.val = 0 := by
      rw [← hAdj, h, Adjunction.homAddEquiv_zero]
    have hm : scalar f U a • m ∈ (multiplePresubmodule f I M).obj (op U) :=
      Submodule.subset_span ⟨a, ha, m, rfl⟩
    exact congrArg (fun ψ => ψ.app (op U) ⟨scalar f U a • m, hm⟩) hp
  · intro h
    have hp : (multiplePresubmodule f I M).ι ≫ φ.val = 0 := by
      apply PresheafOfModules.hom_ext
      intro U
      have hz : (multiplePresubmodule f I M).obj U ≤
          LinearMap.ker (φ.val.app U).hom := by
        apply Submodule.span_le.2
        rintro _ ⟨a, ha, m, rfl⟩
        exact h U.unop a ha m
      ext m
      exact hz m.property
    apply ((sheafifyAdjunction X).homEquiv _ N).injective
    rw [hAdj, hp, Adjunction.homAddEquiv_zero]

/-- The canonical factorization of a map annihilating the ideal generators. -/
def desc (I : Ideal R) {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ (U : X.Opens) (a : R), a ∈ I → ∀ m : Γ(M, U),
      φ.app U (scalar f U a • m) = 0) : quotient f I M ⟶ N :=
  cokernel.desc (inclusion f I M) φ ((inclusion_comp_eq_zero_iff f I φ).2 h)

@[reassoc (attr := simp)]
lemma projection_desc (I : Ideal R) {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ (U : X.Opens) (a : R), a ∈ I → ∀ m : Γ(M, U),
      φ.app U (scalar f U a • m) = 0) :
    projection f I M ≫ desc f I φ h = φ :=
  cokernel.π_desc _ _ _

/-- The factorization is uniquely characterized by the original map. -/
lemma desc_unique (I : Ideal R) {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ (U : X.Opens) (a : R), a ∈ I → ∀ m : Γ(M, U),
      φ.app U (scalar f U a • m) = 0) (ψ : quotient f I M ⟶ N)
    (hψ : projection f I M ≫ ψ = φ) : ψ = desc f I φ h := by
  apply (cancel_epi (projection f I M)).1
  rw [hψ, projection_desc]

end Langlands.AlgebraicGeometry.Modules.IdealAdic
