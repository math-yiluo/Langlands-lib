import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateLineRestriction
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.GlobalLinearAction

/-! # Canonical coordinate sections of relative projective space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.RelativeProjectiveSpace

open ProjectiveSpace.CoordinateLines

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (n : ℕ)

/-- The actual relative projective section of a coordinate basis line. -/
def basisSection (X : Scheme.{u}) (j : Fin (n + 1)) :
    X ⟶ RelativeProjectiveSpace X n :=
  liftOverPolynomial n X.toSpecΓ (𝟙 X)
    (basisPoint (R := Γ(X, ⊤)) n X j) (by
      rw [basisPoint_toSpec, Category.id_comp]
      change X.toSpecΓ ≫ Spec.map (𝟙 _) = X.toSpecΓ
      rw [Spec.map_id, Category.comp_id])

@[reassoc (attr := simp)]
theorem basisSection_toBase (X : Scheme.{u}) (j : Fin (n + 1)) :
    basisSection n X j ≫ toBase X n = 𝟙 X := by
  simp [basisSection]

@[reassoc (attr := simp)]
theorem basisSection_toPolynomial (X : Scheme.{u}) (j : Fin (n + 1)) :
    basisSection n X j ≫ toPolynomial n X.toSpecΓ =
      basisPoint (R := Γ(X, ⊤)) n X j := by
  exact liftOverPolynomial_toPolynomial _ _ _ _

/-- Basis sections are natural under every morphism of scheme bases. -/
@[reassoc]
theorem basisSection_naturality {X Y : Scheme.{u}} (f : Y ⟶ X) (j : Fin (n + 1)) :
    f ≫ basisSection n X j = basisSection n Y j ≫ map n f := by
  let := f.appTop.hom.toAlgebra
  apply hom_ext_toPolynomial X.toSpecΓ
  · simp
  · have hp := toPolynomial_coefficientMap (n := n) (f ≫ X.toSpecΓ) Y.toSpecΓ
      f.appTop.hom (Scheme.toSpecΓ_naturality f).symm
    simp only [Category.assoc, basisSection_toPolynomial, map_toPolynomial]
    rw [← hp, ← Category.assoc, basisSection_toPolynomial]
    rw [comp_basisPoint n f (by ext r; rfl) j,
      basisPoint_coefficientMap n f.appTop.hom (by ext r; rfl) j]

/-- The actual relative action fixes the basis section exactly when its
basis vector is multiplied by one unit of global functions. -/
theorem basisSection_globalLinearAction_eq_iff (X : Scheme.{u}) (j : Fin (n + 1))
    (e : (Fin (n + 1) → Γ(X, ⊤)) ≃ₗ[Γ(X, ⊤)] (Fin (n + 1) → Γ(X, ⊤))) :
    basisSection n X j ≫ globalLinearAction n e = basisSection n X j ↔
      ∃ u : Γ(X, ⊤)ˣ, e (Pi.single j 1) = u • Pi.single j 1 := by
  have hpoly :
      basisSection n X j ≫ globalLinearAction n e = basisSection n X j ↔
        basisPoint (R := Γ(X, ⊤)) n X j ≫ ProjectiveSpace.linearAction Γ(X, ⊤) n e =
          basisPoint (R := Γ(X, ⊤)) n X j := by
    constructor
    · intro h
      have h' := congrArg (fun z => z ≫ toPolynomial n X.toSpecΓ) h
      simpa only [globalLinearAction, Category.assoc, linearAction_toPolynomial,
        basisSection_toPolynomial_assoc, basisSection_toPolynomial] using h'
    · intro h
      apply hom_ext_toPolynomial X.toSpecΓ
      · simp
      · simpa only [globalLinearAction, Category.assoc, linearAction_toPolynomial,
          basisSection_toPolynomial_assoc, basisSection_toPolynomial] using h
  rw [hpoly, basisPoint_linearAction_eq_iff]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, funext hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, congrFun hu⟩

end Langlands.AlgebraicGeometry.RelativeProjectiveSpace
