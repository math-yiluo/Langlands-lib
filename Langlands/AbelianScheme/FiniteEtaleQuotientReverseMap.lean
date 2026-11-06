import Langlands.AbelianScheme.FiniteEtaleQuotientExistenceProof
import Langlands.AbelianScheme.IsogenyActionDescent
import Langlands.CategoryTheory.RationalizationIntegralInverse

/-! # Reverse maps of finite étale quotients with bounded kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.FiniteEtaleSubgroup

variable {S : Scheme.{u}} {A : AbelianScheme S}

namespace QuotientData

variable {K : FiniteEtaleSubgroup A} (D : K.QuotientData) (N : ℕ)
  (hK : K.inclusion ≫ commHom (N • 𝟙 A) = 0)

/-- Multiplication by `N` descends to the quotient when it kills the subgroup. -/
def inverseMultiple : D.B ⟶ A :=
  D.lift (N • 𝟙 A) hK

@[reassoc]
theorem q_inverseMultiple :
    D.q ≫ D.inverseMultiple N hK = N • 𝟙 A :=
  D.fac_lift _ _

@[reassoc]
theorem inverseMultiple_q :
    D.inverseMultiple N hK ≫ D.q = N • 𝟙 D.B := by
  apply IsogenyActionDescent.hom_ext D.isIsogeny
  rw [← Category.assoc, q_inverseMultiple, Preadditive.nsmul_comp,
    Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]

/-- The reverse map is uniquely determined by its composite with the quotient. -/
theorem inverseMultiple_unique (r : D.B ⟶ A)
    (hr : D.q ≫ r = N • 𝟙 A) : r = D.inverseMultiple N hK :=
  IsogenyActionDescent.hom_ext D.isIsogeny _ _
    (hr.trans (D.q_inverseMultiple N hK).symm)

/-- The quotient and its reverse map give integral inverse-multiple data. -/
def inverseData (hN : 0 < N) : Rationalization.IntegralInverseData A D.B where
  multiple := N
  multiple_ne_zero := Int.natCast_ne_zero.mpr (ne_of_gt hN)
  hom := D.q
  inv := D.inverseMultiple N hK
  hom_inv := by simpa only [natCast_zsmul] using D.q_inverseMultiple N hK
  inv_hom := by simpa only [natCast_zsmul] using D.inverseMultiple_q N hK

/-- A quotient by a subgroup killed by a positive integer is rationally invertible. -/
def rationalIso (hN : 0 < N) : Rationalization.of A ≅ Rationalization.of D.B :=
  (D.inverseData N hK hN).toIso

@[simp]
theorem rationalIso_hom (hN : 0 < N) :
    (D.rationalIso N hK hN).hom = Rationalization.ofHom D.q := rfl

@[simp]
theorem rationalIso_inv (hN : 0 < N) :
    (D.rationalIso N hK hN).inv =
      (N : ℚ)⁻¹ • Rationalization.ofHom (D.inverseMultiple N hK) := rfl

end QuotientData

/-- Construct an actual quotient and both integral inverse-multiple equations,
using only the original finite-set fibre-affineness premise on `A`. -/
theorem exists_quotient_inverseMultiple_of_forall_finset_fibre
    [IsLocallyNoetherian S]
    (A : AbelianScheme S)
    (hfib : ∀ (F : Finset A.X.left) (t : S), (∀ x ∈ F, A.X.hom x = t) →
      ∃ W : A.X.left.Opens, IsAffineOpen W ∧ ∀ x ∈ F, x ∈ W)
    (K : FiniteEtaleSubgroup A) (N : ℕ)
    (hK : K.inclusion ≫ commHom (N • 𝟙 A) = 0) :
    ∃ (D : K.QuotientData) (r : D.B ⟶ A),
      D.q ≫ r = N • 𝟙 A ∧ r ≫ D.q = N • 𝟙 D.B := by
  obtain ⟨D⟩ :=
    FiniteEtaleQuotientExistence.nonempty_quotientData_of_forall_finset_fibre A hfib K
  exact ⟨D, D.inverseMultiple N hK, D.q_inverseMultiple N hK,
    D.inverseMultiple_q N hK⟩

end Langlands.AbelianScheme.FiniteEtaleSubgroup
