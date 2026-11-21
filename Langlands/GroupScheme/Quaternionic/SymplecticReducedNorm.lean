import Langlands.GroupScheme.Quaternionic.DegreeSplittingIso
import Langlands.GroupScheme.Quaternionic.SymplecticPoints
import Mathlib.RingTheory.Flat.Basic

/-! # Reduced norm of an isometry of a symplectic Gram matrix -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Matrix
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]
  (σ : FirstKindInvolution F D) {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

/-- When the division involution has the orthogonal dimension, every isometry of an
invertible antihermitian Gram matrix has reduced norm one over each coefficient algebra. -/
theorem reducedNorm_eq_one_of_gram_isometry
    (hσ : Module.finrank F σ.symmetricSubspace =
      Langlands.CentralSimple.reducedDegree F D * (Langlands.CentralSimple.reducedDegree F D + 1) / 2)
    (H : Matrix n n D) (hH : σ.IsAntihermitian H) (hu : IsUnit H)
    (R : Type u) [CommRing R] [Algebra F R] (x : R ⊗[F] Matrix n n D)
    (hx : x * (1 ⊗ₜ[F] H) * (σ.matrix n).baseChange R x = 1 ⊗ₜ[F] H) :
    Langlands.CentralSimple.reducedNorm F (Matrix n n D) R x = 1 := by
  let L := Langlands.CentralSimple.finiteGaloisSplittingField F D
  let e := Langlands.CentralSimple.finiteGaloisSplittingChart F D
  let S := L ⊗[F] R
  let f : R →ₐ[F] S := Algebra.TensorProduct.includeRight
  let z := Algebra.TensorProduct.map f (AlgHom.id F (Matrix n n D)) x
  have hz : z * (1 ⊗ₜ[F] H) * (σ.matrix n).baseChange S z = 1 ⊗ₜ[F] H := by
    apply sub_eq_zero.mp
    change IsometryCut.defect (σ.matrix n) H z = 0
    rw [← IsometryCut.map_defect (σ.matrix n) H f x]
    have hzero : IsometryCut.defect (σ.matrix n) H x = 0 := sub_eq_zero.mpr hx
    rw [hzero, _root_.map_zero]
  have hs : Module.finrank F σ.symmetricSubspace =
      Fintype.card (Fin (Langlands.CentralSimple.reducedDegree F D)) *
        (Fintype.card (Fin (Langlands.CentralSimple.reducedDegree F D)) + 1) / 2 := by
    simpa only [Fintype.card_fin] using hσ
  obtain ⟨k, P, Q, hPQ, hQP, hJ⟩ := SymplecticMatrix.exists_mul_mul_transpose_eq_J
    (DegreeSplitting.splitGram e σ H) (DegreeSplitting.transpose_splitGram e σ hs hH)
    (DegreeSplitting.splitGram_diag e σ hs hH) (DegreeSplitting.det_splitGram_ne_zero e σ hu)
  let g : Matrix.symplecticGroup (Fin k) S :=
    ⟨DegreeSplitting.darbouxMatrix e P Q S z,
      (DegreeSplitting.darbouxMatrix_mem_iff e σ H P Q S hQP hJ z).2 hz⟩
  obtain ⟨w, _, hn, hw⟩ := DegreeSplitting.exists_darbouxMatrix_eq e σ H P Q S hPQ hQP hJ g
  have hwz : (w : S ⊗[F] Matrix n n D) = z :=
    DegreeSplitting.darbouxMatrix_injective e P Q S hQP hw
  have hf : Function.Injective f := Algebra.TensorProduct.includeRight_injective
    (algebraMap F L).injective
  apply hf
  rw [← Langlands.CentralSimple.reducedNorm_naturality F (Matrix n n D) f,
    _root_.map_one]
  change Langlands.CentralSimple.reducedNorm F (Matrix n n D) S z = 1
  exact hwz ▸ hn

/-- The symplectic and unitary inclusions have the same image for this Gram matrix on all tests. -/
def SymplecticAmbientRangeStatement : Prop :=
  ∀ (F D : Type u) [Field F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D]
    (σ : FirstKindInvolution F D) (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n D),
    Module.finrank F σ.symmetricSubspace =
      Langlands.CentralSimple.reducedDegree F D * (Langlands.CentralSimple.reducedDegree F D + 1) / 2 →
    σ.IsAntihermitian H → IsUnit H →
    ∀ (T : Over (Spec (CommRingCat.of F))) (x : T ⟶ (ambientUnits F D n).X),
      x ∈ (SubgroupFunctor.range (σ.symplecticAmbientι H)).carrier T ↔
        x ∈ (SubgroupFunctor.range (σ.unitaryGroupι H)).carrier T

theorem symplecticAmbientRange : SymplecticAmbientRangeStatement.{u} := by
  intro F D _ _ _ _ _ σ n _ _ _ H hσ hH hu T x
  rw [σ.mem_range_symplecticAmbientι_iff]
  refine ⟨And.left, fun hx => ⟨hx, ?_⟩⟩
  apply (Gm.pointsEquiv (Spec (CommRingCat.of F)) T).injective
  rw [CentralSimpleUnits.reducedNormHom_points, _root_.map_one]
  apply Units.ext
  exact σ.reducedNorm_eq_one_of_gram_isometry hσ H hH hu _ _
    ((σ.mem_range_unitaryGroupι_iff H x).mp hx)

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
