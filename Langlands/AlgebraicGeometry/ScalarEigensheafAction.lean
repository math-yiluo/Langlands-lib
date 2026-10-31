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
  (hσ : ∀ (r : R) (a : A), ρ r ≫ σ a = σ a ≫ ρ r)

/-- Restrict an actual commuting ring action to the simultaneous scalar eigensubsheaf. -/
def scalarEigensheafAction : A →+* End (scalarEigensheaf ρ χ) where
  toFun a := scalarEigensheafMap ρ (σ a) (fun r => hσ r a)
  map_one' := by
    change (_ : scalarEigensheaf ρ χ ⟶ scalarEigensheaf ρ χ) = _
    ext U x
    apply Subtype.ext
    change (σ 1).app U x.val = x.val
    rw [map_one]
    rfl
  map_mul' := by
    intro a b
    change (_ : scalarEigensheaf ρ χ ⟶ scalarEigensheaf ρ χ) = _
    ext U x
    apply Subtype.ext
    change (σ (a * b)).app U x.val = (σ a).app U ((σ b).app U x.val)
    rw [map_mul]
    rfl
  map_zero' := by
    change (_ : scalarEigensheaf ρ χ ⟶ scalarEigensheaf ρ χ) = _
    ext U x
    apply Subtype.ext
    change (σ 0).app U x.val = 0
    rw [map_zero]
    rfl
  map_add' := by
    intro a b
    change (_ : scalarEigensheaf ρ χ ⟶ scalarEigensheaf ρ χ) = _
    ext U x
    apply Subtype.ext
    change (σ (a + b)).app U x.val = (σ a).app U x.val + (σ b).app U x.val
    rw [map_add]
    rfl

@[simp]
theorem scalarEigensheafAction_app (a : A) (U : S.Opens)
    (x : Γ(scalarEigensheaf ρ χ, U)) :
    ((scalarEigensheafAction ρ χ σ hσ a).app U x).val =
      (σ a).app U x.val := rfl

@[reassoc (attr := simp)]
theorem scalarEigensheafAction_ι (a : A) :
    scalarEigensheafAction ρ χ σ hσ a ≫ scalarEigensheafι ρ χ =
      scalarEigensheafι ρ χ ≫ σ a := rfl

variable {ρ χ σ hσ}
  (τ : R →+* End N) (υ : A →+* End N)
  (hυ : ∀ (r : R) (a : A), τ r ≫ υ a = υ a ≫ τ r)
  (f : M ⟶ N) (hf : ∀ r : R, ρ r ≫ f = f ≫ τ r)
  (hA : ∀ a : A, σ a ≫ f = f ≫ υ a)

include hA in
/-- A map intertwining both ambient actions intertwines their constructed restrictions. -/
theorem scalarEigensheafMap_intertwines (a : A) :
    scalarEigensheafAction ρ χ σ hσ a ≫ scalarEigensheafMap τ f hf =
      scalarEigensheafMap τ f hf ≫ scalarEigensheafAction τ χ υ hυ a := by
  ext U x
  apply Subtype.ext
  exact congrArg (fun g : M ⟶ N => g.app U x.val) (hA a)

end Langlands.Scheme.Modules
