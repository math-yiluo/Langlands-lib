import Langlands.Shimura.Unitary.HermitianDiscriminantComparison
import Langlands.Shimura.Unitary.FiniteSignedDeterminant

/-! # The discriminant at a nonsplit finite place with a split algebra -/

noncomputable section

universe u v

open Matrix
open scoped TensorProduct

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global.AdelicFunctoriality
open Langlands.Global (FiniteCompletion)
open Langlands.LocalClassField Langlands.ClassFieldTheory.Local Langlands.GaloisCohomology Langlands.Galois
open scoped FiniteExtension

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  {A : CSA.{v, v} K} [Algebra E A] [IsScalarTower E K A] {m : ℕ}

attribute [local instance] FiniteExtension.local_finite

set_option maxRecDepth 8192 in
/-- At a nonsplit finite place with zero upper Brauer invariants, the
discriminant detects the norm class of the signed determinant of the actual Hermitian chart. -/
theorem localInvariant_discriminant_at_nonsplit
    (P : EvenDiscriminantPresentation E A m) (D : CentralSimpleUnitaryData E K A (2 * m))
    (hn : 0 < 2 * m) (ι : PlaceEmbeddings E (AlgebraicClosure E))
    (p : Langlands.Global.FinitePlace E) (hp : ¬ IsSplitPlace E K p)
    (hz : ∀ q : FinitePlacesAbove K p, HasCompletedBrauerInvariant K A q.val 0) :
    localInvariant ι p (brauerEquiv E (AlgebraicClosure E) (P.brauerClass D.toSecondKindInvolution)) =
      (by
        classical
        exact if (nonsplitSignedDeterminant p hp D hn hz).val ∈
          normSubgroup (FiniteCompletion E p) (FiniteCompletion K (placeAbove K p).val)
        then 0 else rationalClass (1 / 2)) := by
  classical
  let F := FiniteCompletion E p
  let q := placeAbove K p
  let L := FiniteCompletion K q.val
  let : IsQuadraticExtension F L := ⟨nonsplitCompletion_finrank p hp⟩
  let eC := nonsplitCompletionCenterEquiv p hp
  let φ : L ≃ₐ[F] L :=
    uniquePlaceCompletionAutEquiv q (eq_placeAbove_of_nonsplit p hp) (cmConjugation E K)
  have hφK (k : K) :
      φ (algebraMap K L k) = algebraMap K L (cmConjugation E K k) :=
    uniquePlaceCompletionAutEquiv_algebraMap _ _ _ _
  have hφ : φ ≠ 1 := by
    intro h
    apply cmConjugation_ne_one E K
    apply AlgEquiv.ext
    intro k
    apply (algebraMap K L).injective
    rw [← hφK, h]
    rfl
  have hφC (z : L) : nonsplitCoefficientInvolution p hp z = φ z := by
    obtain ⟨x, rfl⟩ := eC.surjective z
    exact (AlgebraInvolution.transport_equiv _ eC x).trans
      (nonsplitCompletionCenterEquiv_conjugation p hp x)
  let G := nonsplitHermitianChart p D hn hp hz
  let d := nonsplitSignedDeterminant p hp D hn hz
  have hC (k : K) : eC (1 ⊗ₜ[E] k) = algebraMap K L k := by
    rw [nonsplitCompletionCenterEquiv_apply, completedCenterMap_tmul, map_one, one_mul]
  have hcenter (k : K) :
      G.equiv (1 ⊗ₜ[E] algebraMap K A k) =
        algebraMap L (Matrix (Fin (2 * m)) (Fin (2 * m)) L) (algebraMap K L k) := by
    have h := G.center_eq (eC (1 ⊗ₜ[E] k))
    change G.equiv (localCenterMap E K A p (eC.symm (eC (1 ⊗ₜ[E] k)))) = _ at h
    rw [eC.symm_apply_apply, localCenterMap_tmul, hC] at h
    exact h
  have htrans (X : Matrix (Fin (2 * m)) (Fin (2 * m)) L) :
      matrixTranspose (nonsplitCoefficientInvolution p hp) (2 * m) X = (X.map φ)ᵀ := by
    apply Matrix.ext
    intro i j
    exact hφC (X j i)
  have hHerm : ((G.gram : Matrix (Fin (2 * m)) (Fin (2 * m)) L).map φ)ᵀ = G.gram :=
    (htrans _).symm.trans G.hermitian
  have hAdj (a : A) : G.equiv (1 ⊗ₜ[E] D.involution a) =
      ((G.gram⁻¹ : GL (Fin (2 * m)) L) : Matrix (Fin (2 * m)) (Fin (2 * m)) L) *
        ((G.equiv (1 ⊗ₜ[E] a)).map φ)ᵀ * (G.gram : Matrix (Fin (2 * m)) (Fin (2 * m)) L) := by
    have h := G.adjoint_eq (1 ⊗ₜ[E] a)
    rw [localInvolution_tmul, AlgebraInvolution.adjoint_apply, htrans] at h
    exact h
  have hd : algebraMap F L (d.val : F) = (-1 : L)^m *
      (GeneralLinearGroup.det G.gram : L) := by
    have hn' : 2 * m / 2 = m := by omega
    simpa only [hn', GeneralLinearGroup.val_det_apply] using d.property
  have hnorm := discriminantClass_eq_zero_of_hermitian_chart P D φ hφ hφK G.equiv hcenter
    G.gram hHerm hAdj d.val hd
  let b := P.brauerClass D.toSecondKindInvolution
  let x := localInvariant ι p (brauerEquiv E (AlgebraicClosure E) b)
  have hx₂ : 2 • x = 0 := by
    change 2 • localInvariant ι p (brauerEquiv E (AlgebraicClosure E) b) = 0
    rw [← map_nsmul, ← map_nsmul, P.two_nsmul_brauerClass, map_zero, map_zero]
  have hx : x = 0 ↔ d.val ∈ normSubgroup F L := by
    let : ValuativeRel F := Langlands.Global.FiniteCompletion.valuativeRel p
    let : IsNonarchimedeanLocalField F := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField p
    change localInvariant ι p (brauerEquiv E (AlgebraicClosure E) b) = 0 ↔ _
    rw [localInvariant_brauerEquiv, map_eq_zero_iff _ (localBrauerInvariant F).injective]
    exact hnorm
  exact (halfClass_of_two_nsmul_eq_zero hx₂).trans (if_congr hx rfl rfl)

end Langlands.Shimura.FiniteUnitary
