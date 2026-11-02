import Langlands.AlgebraicGeometry.EtaleAlgebraUniformPointBound
import Langlands.AlgebraicGeometry.FiniteEtale.AffineQuotientCoconeProof
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Uniform bounds for field-valued fibres of affine étale morphisms -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]

/-- A bound obtained from the map on global sections of an affine étale
morphism, independently of a field-valued base point. -/
noncomputable def affineEtalePointBound (f : X ⟶ Y) [Etale f] : ℕ := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have : Algebra.Etale Γ(Y, ⊤) Γ(X, ⊤) :=
    HasRingHomProperty.appTop (P := @Etale) f inferInstance
  exact EtaleAlgebraPointBound.uniformBound Γ(Y, ⊤) Γ(X, ⊤)

theorem affineEtale_fibrePoints_finite_card_le (f : X ⟶ Y) [Etale f]
    (K : Type u) [Field K] (a : Spec (.of K) ⟶ Y) :
    Finite {g : Spec (.of K) ⟶ X // g ≫ f = a} ∧
      Nat.card {g : Spec (.of K) ⟶ X // g ≫ f = a} ≤ affineEtalePointBound f := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have : Algebra.Etale Γ(Y, ⊤) Γ(X, ⊤) :=
    HasRingHomProperty.appTop (P := @Etale) f inferInstance
  let a' := FiniteEtale.affinePointEquiv Y (.of K) a
  let : Algebra Γ(Y, ⊤) K := a'.hom.toAlgebra
  let ev : {g : Spec (.of K) ⟶ X // g ≫ f = a} → (Γ(X, ⊤) →ₐ[Γ(Y, ⊤)] K) :=
    fun g =>
      { toRingHom := (FiniteEtale.affinePointEquiv X (.of K) g.1).hom
        commutes' := fun r => by
          have hg : f.appTop ≫ FiniteEtale.affinePointEquiv X (.of K) g.1 = a' := by
            rw [← FiniteEtale.affinePointEquiv_comp, g.2]
          exact congrArg (fun z : Γ(Y, ⊤) ⟶ CommRingCat.of K => z.hom r) hg }
  have hev : Function.Injective ev := by
    intro g h heq
    apply Subtype.ext
    apply (FiniteEtale.affinePointEquiv X (.of K)).injective
    ext s
    exact DFunLike.congr_fun heq s
  obtain ⟨hfin, hbound⟩ :=
    EtaleAlgebraPointBound.hom_finite_card_le (R := Γ(Y, ⊤)) (S := Γ(X, ⊤)) K
  let := hfin
  exact ⟨Finite.of_injective ev hev,
    (Nat.card_le_card_of_injective ev hev).trans hbound⟩

end Langlands.AlgebraicGeometry
