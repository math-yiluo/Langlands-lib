import Langlands.ClassFieldTheory.Global.CyclicHasseNormProof
import Langlands.Global.FiniteCompletionLocalField
import Langlands.GroupScheme.Examples.HermitianHyperbolicSplitRankLower
import Langlands.GroupScheme.Examples.HermitianRootQuadraticForm
import Langlands.GroupScheme.Examples.HermitianRootUnitWitnesses
import Langlands.GroupScheme.OrthogonalMatrix.Hyperbolic
import Langlands.LinearAlgebra.LocalQuadraticAnisotropicDimensionBound
import Langlands.LinearAlgebra.NumberFieldQuadraticIsotropyOfCyclicNorm

/-! # Isotropy of Hermitian spaces over totally complex number fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module NumberField

namespace Langlands.GroupScheme

open SU3Root

variable {F L : Type u} [Field F] [NumberField F] [Field L] [Algebra F L]
  [Algebra.IsQuadraticExtension F L] [Algebra.IsSeparable F L]

/-- Every Hermitian space of dimension at least three over a quadratic
extension of a totally complex number field has an isotropic vector. -/
theorem HermitianRoot.numberField_exists_isotropic (hF : IsTotallyComplex F)
    {V : Type u} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (h : V →ₗ[L] V →ₛₗ[(fieldInvolution F L).bar.toRingHom] L)
    (hbar : ∀ x y, (fieldInvolution F L).bar (h x y) = h y x)
    (hn : 3 ≤ finrank L V) : ∃ v : V, v ≠ 0 ∧ h v v = 0 := by
  classical
  by_contra! han
  obtain ⟨D, hD, _, _⟩ := exists_anisotropic_diagonal_coordinates h hbar (fun x hx => by
    by_contra hne
    exact han x hne hx)
  let : FiniteDimensional F L :=
    .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two F L]; decide)
  let W := Fin (finrank L V) → L
  let Q := D.quadraticForm F L
  have hQ : Q.polarBilin.Nondegenerate :=
    LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
      (D.quadraticForm_polar_separatingLeft F L (D.weight_ne_zero hD))
  have hdim (K : Type u) [Field K] [Algebra F K] :
      finrank K (TensorProduct F K W) = 2 * finrank L V := by
    rw [Module.finrank_baseChange, DiagonalForm.quadraticForm_finrank F L, Fintype.card_fin]
  have hlocal (v : Global.Place F) : ¬ (Q.baseChange (Global.placeCompletion F v)).Anisotropic := by
    rcases v with v | v
    · let K := v.Completion
      let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (hF.isComplex v)
      let : IsAlgClosed K := ⟨fun f => Polynomial.Splits.of_splits_map
        e.toRingHom (IsAlgClosed.splits _) (fun x _ => e.surjective x)⟩
      obtain ⟨x, hx, hzero⟩ := OrthogonalMatrix.exists_isotropic
        (by rw [hdim K]; omega) (Q.baseChange K)
      exact fun hA => hx (hA x hzero)
    · let K := Global.FiniteCompletion F v
      let : ValuativeRel K := Global.FiniteCompletion.valuativeRel v
      let : IsNonarchimedeanLocalField K := Global.FiniteCompletion.isNonarchimedeanLocalField v
      intro hA
      have hd := Langlands.localQuadraticAnisotropicDimensionBound K _ (Q.baseChange K) hA
      rw [hdim K] at hd
      omega
  exact (Langlands.numberFieldQuadraticIsotropy_of_cyclicNorm
    Langlands.ClassFieldTheory.Global.cyclicHasseNorm F W Q hQ hlocal)
    ((D.quadraticForm_anisotropic_iff F L).mpr hD)

/-- A group presented by the special unitary group of a nonsingular Hermitian
matrix of size at least three is isotropic over a totally complex number field. -/
theorem HermitianMatrix.SchemeModel.Presentation.not_isAnisotropic_of_totallyComplex
    (hF : IsTotallyComplex F) {n : ℕ} (hn : 3 ≤ n)
    {H : HermitianMatrix.Form (fieldInvolution F L) (Fin n)}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (p : HermitianMatrix.SchemeModel.Presentation F L H G) : ¬ IsAnisotropic G := by
  obtain ⟨x, hx, hxx⟩ := HermitianRoot.numberField_exists_isotropic hF H.linearFirst
    H.bar_linearFirst (by simpa using hn)
  let W : Submodule L (Fin n → L) := L ∙ x
  have hW : H.IsTotallyIsotropic W := by
    apply (H.totallyIsotropic_iff_linearFirst W).mpr
    intro y hy z hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hz
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, hxx, smul_zero]
  have hb := p.finrank_le_splitRank W hW
  change (finrank L (L ∙ x) : ℕ∞) ≤ splitRank G at hb
  intro hG
  rw [finrank_span_singleton hx, show splitRank G = 0 from hG] at hb
  simp at hb

/-- Over a totally complex number field, groups with a scalar special
unitary presentation in dimension at least three are isotropic. -/
def NumberFieldTotallyComplexHermitianMatrixIsotropyStatement : Prop :=
  ∀ (F L : Type u) [Field F] [NumberField F] [Field L] [Algebra F L]
      [Algebra.IsQuadraticExtension F L] [Algebra.IsSeparable F L], IsTotallyComplex F →
    ∀ (n : ℕ), 3 ≤ n →
      ∀ (H : HermitianMatrix.Form (fieldInvolution F L) (Fin n))
        (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
        [LocallyOfFiniteType G.X.hom],
        HermitianMatrix.SchemeModel.Presentation F L H G → ¬ IsAnisotropic G

theorem numberFieldTotallyComplexHermitianMatrixIsotropy :
    NumberFieldTotallyComplexHermitianMatrixIsotropyStatement.{u} :=
  fun _ _ _ _ _ _ _ _ hF _ hn _ _ _ _ p => p.not_isAnisotropic_of_totallyComplex hF hn

end Langlands.GroupScheme
