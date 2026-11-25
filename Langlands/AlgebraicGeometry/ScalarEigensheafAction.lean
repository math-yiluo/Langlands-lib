import Langlands.AlgebraicGeometry.ScalarEigensheaf

/-! # Commuting actions on simultaneous scalar eigensubsheaves -/

noncomputable section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

namespace Langlands.Scheme.Modules

variable {S : AlgebraicGeometry.Scheme.{u}} {R : Type v} [Ring R]
  {A : Type w} [Ring A] {M N : S.Modules}
  (ρ : R →+* End M) (χ : R →+* Γ(S, ⊤))
  (σ : A →+* End M)
  (hσ : ∀ (r : R) (a : A), (ρ r).asHom ≫ (σ a).asHom = (σ a).asHom ≫ (ρ r).asHom)

/-- Restrict an actual commuting ring action to the simultaneous scalar eigensubsheaf. -/
def scalarEigensheafAction : A →+* End (scalarEigensheaf ρ χ) where
  toFun a := End.of (scalarEigensheafMap ρ (σ a).asHom (fun r => hσ r a))
  map_one' := by
    apply End.ext
    change (_ : scalarEigensheaf ρ χ ⟶ scalarEigensheaf ρ χ) = _
    ext U x
    apply Subtype.ext
    change (σ 1).asHom.app U x.val = x.val
    rw [map_one]
    rfl
  map_mul' := by
    intro a b
    apply End.ext
    change (_ : scalarEigensheaf ρ χ ⟶ scalarEigensheaf ρ χ) = _
    ext U x
    apply Subtype.ext
    change (σ (a * b)).asHom.app U x.val = (σ a).asHom.app U ((σ b).asHom.app U x.val)
    rw [map_mul]
    rfl
  map_zero' := by
    apply End.ext
    change (_ : scalarEigensheaf ρ χ ⟶ scalarEigensheaf ρ χ) = _
    ext U x
    apply Subtype.ext
    change (σ 0).asHom.app U x.val = 0
    rw [map_zero]
    rfl
  map_add' := by
    intro a b
    apply End.ext
    change (_ : scalarEigensheaf ρ χ ⟶ scalarEigensheaf ρ χ) = _
    ext U x
    apply Subtype.ext
    change (σ (a + b)).asHom.app U x.val = (σ a).asHom.app U x.val + (σ b).asHom.app U x.val
    rw [map_add]
    rfl

@[simp]
theorem scalarEigensheafAction_app (a : A) (U : S.Opens)
    (x : Γ(scalarEigensheaf ρ χ, U)) :
    ((scalarEigensheafAction ρ χ σ hσ a).asHom.app U x).val =
      (σ a).asHom.app U x.val := rfl

@[reassoc (attr := simp)]
theorem scalarEigensheafAction_ι (a : A) :
    (scalarEigensheafAction ρ χ σ hσ a).asHom ≫ scalarEigensheafι ρ χ =
      scalarEigensheafι ρ χ ≫ (σ a).asHom := rfl

variable {ρ χ σ hσ}
  (τ : R →+* End N) (υ : A →+* End N)
  (hυ : ∀ (r : R) (a : A), (τ r).asHom ≫ (υ a).asHom = (υ a).asHom ≫ (τ r).asHom)
  (f : M ⟶ N) (hf : ∀ r : R, (ρ r).asHom ≫ f = f ≫ (τ r).asHom)
  (hA : ∀ a : A, (σ a).asHom ≫ f = f ≫ (υ a).asHom)

include hA in
/-- A map intertwining both ambient actions intertwines their constructed restrictions. -/
theorem scalarEigensheafMap_intertwines (a : A) :
    (scalarEigensheafAction ρ χ σ hσ a).asHom ≫ scalarEigensheafMap τ f hf =
      scalarEigensheafMap τ f hf ≫ (scalarEigensheafAction τ χ υ hυ a).asHom := by
  ext U x
  apply Subtype.ext
  exact congrArg (fun g : M ⟶ N => g.app U x.val) (hA a)

end Langlands.Scheme.Modules
