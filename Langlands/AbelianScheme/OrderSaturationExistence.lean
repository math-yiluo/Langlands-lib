import Langlands.AbelianScheme.OrderSaturation
import Langlands.AbelianScheme.InvertibleMultiplication
import Langlands.AbelianScheme.FiniteEtaleQuotientExistenceProof
import Langlands.CategoryTheory.RationalizationPositiveScaledActions

/-! # Integral order models under a finite-fibre affine-open criterion -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

variable {S : Scheme.{u}} {O : Type v} [Ring O] {A : AbelianScheme S}

/-- An actual integral order action, an actual finite étale isogeny from the original
abelian scheme, and integral inverse-multiple data with original rational equivariance. -/
structure IntegralOrderModel (α : O →+* Rationalization.End A) where
  B : AbelianScheme S
  action : O →+* End B
  inverseData : Rationalization.IntegralInverseData A B
  multiple_pos : 0 < inverseData.multiple
  isIsogeny : IsIsogeny inverseData.hom
  etale : Etale (hom inverseData.hom)
  intertwines : ∀ x : O,
    Rationalization.ofHom inverseData.hom ≫ Rationalization.ofEnd B (action x) =
      α x ≫ Rationalization.ofHom inverseData.hom

/-- Construct an integral order model over a characteristic-zero field scheme whenever
every finite subset of one fibre lies in an affine open of the original abelian scheme. -/
def integralOrderModelOfForallFinsetFibre
    (htor : TorsionFiniteEtaleStatement.{u})
    {K : Type u} [Field K] [CharZero K] (p : S ⟶ Spec (.of K))
    [IsLocallyNoetherian S] {I : Type u} [Fintype I] (b : Basis I ℤ O)
    (α : O →+* Rationalization.End A)
    (hfib : ∀ (F : Finset A.X.left) (s : S), (∀ x ∈ F, A.X.hom x = s) →
      ∃ W : A.X.left.Opens, IsAffineOpen W ∧ ∀ x ∈ F, x ∈ W) :
    IntegralOrderModel α := by
  classical
  let s₀ := Rationalization.scaledIntegralLift b α
  let s := s₀.positive
  let n := s₀.positiveIndex
  have hn : 0 < n := s₀.positiveIndex_pos
  have hncast : (n : ℤ) = s.denom := s₀.positiveIndex_cast
  have hnK : IsUnit (n : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
  have hnS : IsUnit (n : Γ(S, ⊤)) := by
    simpa only [map_natCast] using
      hnK.map ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom
  obtain ⟨hF, hE⟩ := htor S A n hn hnS
  haveI : IsFinite (GroupScheme.torsion A.toGrp s.denom).X.hom := by
    rw [← hncast]
    exact hF
  haveI : Etale (GroupScheme.torsion A.toGrp s.denom).X.hom := by
    rw [← hncast]
    exact hE
  let D : (OrderSaturation.subgroup b s).QuotientData :=
    Classical.choice
      (FiniteEtaleQuotientExistence.nonempty_quotientData_of_forall_finset_fibre A hfib _)
  have hnIso : IsIsogeny (s.denom • (𝟙 A)) := by
    rw [← hncast]
    exact multiplication_isIsogeny_of_isUnit A n hnS
  exact {
    B := D.B
    action := OrderSaturation.action b s D hnIso
    inverseData := OrderSaturation.inverseData b s D
    multiple_pos := s₀.positive_denom_pos
    isIsogeny := D.isIsogeny
    etale := D.etale
    intertwines := OrderSaturation.action_rational_fac b s D hnIso }

end Langlands.AbelianScheme
