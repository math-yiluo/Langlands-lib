import Langlands.Algebra.CentralSimple.UnitaryPoints
import Langlands.Algebra.CentralSimple.SeparableClosureChart
import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.Basic

/-! # Reduced norm and an involution acting on the center -/

noncomputable section

open scoped TensorProduct

namespace Langlands.CentralSimple

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root
open Langlands.ReducedNorm

universe u

section Chart

variable {F E L B : Type u} [Field F] [Field E] [Field L]
  [Algebra F E] [Algebra E L] [Algebra F L]
  [Ring B] [Algebra E B] [Algebra F B]
  {I : Type*} [Fintype I] [DecidableEq I]

private def conjugateChartHom (c : E ≃ₐ[F] E) (k : L ≃ₐ[F] L)
    (hk : ∀ a : E, k (algebraMap E L a) = algebraMap E L (c a))
    (τ : FirstKindInvolution F B)
    (hτ : ∀ a : E, τ (algebraMap E B a) = algebraMap E B (c a))
    (e : L ⊗[E] B ≃ₐ[L] Matrix I I L) : B →ₐ[E] Matrix I I L where
  toFun b := (e ((1 : L) ⊗ₜ[E] τ b)).transpose.map k.symm
  map_one' := by
    rw [τ.map_one, ← Algebra.TensorProduct.one_def, map_one, Matrix.transpose_one]
    exact Matrix.map_one _ (map_zero k.symm) (map_one k.symm)
  map_mul' a b := by
    have h : ((1 : L) ⊗ₜ[E] τ b) * ((1 : L) ⊗ₜ[E] τ a) =
        (1 : L) ⊗ₜ[E] (τ b * τ a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [τ.map_mul, ← h, map_mul e, Matrix.transpose_mul, Matrix.map_mul]
  map_zero' := by simp
  map_add' a b := by
    simp [TensorProduct.tmul_add, Matrix.map_add _ (map_add k.symm)]
  commutes' a := by
    have hcomm : (1 : L) ⊗ₜ[E] algebraMap E B (c a) =
        algebraMap L (L ⊗[E] B) (algebraMap E L (c a)) := by
      change (1 : L) ⊗ₜ[E] algebraMap E B (c a) =
        algebraMap E L (c a) ⊗ₜ[E] (1 : B)
      rw [Algebra.algebraMap_eq_smul_one (R := E) (A := B), ← TensorProduct.smul_tmul,
        Algebra.smul_def, mul_one]
    rw [hτ, hcomm, e.commutes, ← hk]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Algebra.algebraMap_eq_smul_one]
    · simp [Algebra.algebraMap_eq_smul_one, hij]

variable [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B] [Nonempty I]

private def conjugateChart (c : E ≃ₐ[F] E) (k : L ≃ₐ[F] L)
    (hk : ∀ a : E, k (algebraMap E L a) = algebraMap E L (c a))
    (τ : FirstKindInvolution F B)
    (hτ : ∀ a : E, τ (algebraMap E B a) = algebraMap E B (c a))
    (e : L ⊗[E] B ≃ₐ[L] Matrix I I L) : L ⊗[E] B ≃ₐ[L] Matrix I I L := by
  let f := AlgHom.liftEquiv E L B (Matrix I I L) (conjugateChartHom c k hk τ hτ e)
  let : IsSimpleRing (L ⊗[E] B) := isSimpleRing_baseChange E B L
  exact AlgEquiv.ofBijective f ⟨f.toRingHom.injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank e.toLinearEquiv.finrank_eq).mp
      f.toRingHom.injective⟩

private theorem conjugateChart_one_tmul (c : E ≃ₐ[F] E) (k : L ≃ₐ[F] L)
    (hk : ∀ a : E, k (algebraMap E L a) = algebraMap E L (c a))
    (τ : FirstKindInvolution F B)
    (hτ : ∀ a : E, τ (algebraMap E B a) = algebraMap E B (c a))
    (e : L ⊗[E] B ≃ₐ[L] Matrix I I L) (b : B) :
    conjugateChart c k hk τ hτ e ((1 : L) ⊗ₜ[E] b) =
      (e ((1 : L) ⊗ₜ[E] τ b)).transpose.map k.symm := by
  change (AlgHom.liftEquiv E L B (Matrix I I L) (conjugateChartHom c k hk τ hτ e))
    ((1 : L) ⊗ₜ[E] b) = _
  simp [conjugateChartHom]

end Chart

variable {F E B : Type u} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
  [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]

/-- The relative reduced norm carries the extended involution to conjugation on
its coefficient algebra. -/
theorem relativeReducedNorm_involution (τ : FirstKindInvolution F B)
    (hτ : ∀ a : E, τ (algebraMap E B a) = algebraMap E B (conjugation F E a))
    (R : Type u) [CommRing R] [Algebra F R] (x : R ⊗[F] B) :
    reducedNorm E B (E ⊗[F] R) (UnitaryPoints.tensorEquiv F E B R (τ.baseChange R x)) =
      Algebra.TensorProduct.map (conjugation F E).toAlgHom (AlgHom.id F R)
        (reducedNorm E B (E ⊗[F] R) (UnitaryPoints.tensorEquiv F E B R x)) := by
  classical
  let L := AlgebraicClosure E
  let : IsAlgClosure F L := ⟨inferInstance, Algebra.IsAlgebraic.trans F E L⟩
  let c := conjugation F E
  let k := c.liftNormal L
  have hk (a : E) : k (algebraMap E L a) = algebraMap E L (c a) := c.liftNormal_commutes L a
  let D := reducedDegree E B
  let : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp (reducedNorm_degree_spec E B).1
  let L₀ := finiteGaloisSplittingField E B
  let ι : L₀ →ₐ[E] L := IsAlgClosed.lift
  let : Algebra L₀ L := ι.toRingHom.toAlgebra
  let : IsScalarTower E L₀ L := IsScalarTower.of_algHom ι
  let e := extendSplittingChart (finiteGaloisSplittingChart E B) L
  let e' := conjugateChart c k hk τ hτ e
  let S := E ⊗[F] R
  let T := L ⊗[F] R
  let : IsScalarTower E L T := IsScalarTower.of_algebraMap_eq' rfl
  let j : S →ₐ[E] T := Algebra.TensorProduct.map (Algebra.ofId E L) (AlgHom.id F R)
  let q : S →ₐ[F] S := Algebra.TensorProduct.map c.toAlgHom (AlgHom.id F R)
  let Q : T →ₐ[F] T := Algebra.TensorProduct.map k.toAlgHom (AlgHom.id F R)
  have hj : Function.Injective j := Module.Flat.rTensor_preserves_injective_linearMap
    ((Algebra.ofId E L).restrictScalars F).toLinearMap (algebraMap E L).injective
  have hq (s : S) : j (q s) = Q (j s) := by
    induction s using TensorProduct.inductionOn with
    | tmul a r =>
      change algebraMap E L (c a) ⊗ₜ[F] r = k (algebraMap E L a) ⊗ₜ[F] r
      rw [hk]
    | add a b ha hb => simp only [map_add, ha, hb]
  let bend : R ⊗[F] B →ₐ[F] T ⊗[E] B :=
    ((Algebra.TensorProduct.map j (AlgHom.id E B)).restrictScalars F).comp
      (UnitaryPoints.tensorEquiv F E B R).toAlgHom
  have hbend (r : R) (b : B) : bend (r ⊗ₜ[F] b) = ((1 : L) ⊗ₜ[F] r) ⊗ₜ[E] b := by
    change ((algebraMap E L (1 : E)) ⊗ₜ[F] r) ⊗ₜ[E] b = _
    rw [map_one]
  have hmat (z : R ⊗[F] B) : splittingMap e T (bend (τ.baseChange R z)) =
      (splittingMap e' T (bend z)).transpose.map Q := by
    induction z using TensorProduct.inductionOn with
    | tmul r b =>
      rw [FirstKindInvolution.baseChange_tmul, hbend, hbend,
        splittingMap_tmul, splittingMap_tmul, conjugateChart_one_tmul]
      ext i j
      change ((1 : L) ⊗ₜ[F] r) *
        (algebraMap L T (e ((1 : L) ⊗ₜ[E] τ b) i j)) =
        Q (((1 : L) ⊗ₜ[F] r) *
          (algebraMap L T (k.symm (e ((1 : L) ⊗ₜ[E] τ b) i j))))
      rw [map_mul]
      congr 1
      · change (1 : L) ⊗ₜ[F] r = k 1 ⊗ₜ[F] r
        rw [map_one]
      · change _ ⊗ₜ[F] (1 : R) = k (k.symm _) ⊗ₜ[F] (1 : R)
        rw [AlgEquiv.apply_symm_apply, Algebra.algebraMap_self_apply]
    | add z w hz hw =>
      simp only [map_add, hz, hw, Matrix.transpose_add,
        Matrix.map_add _ (map_add Q)]
  apply hj
  change j (reducedNorm E B S _) = j (q (reducedNorm E B S _))
  rw [hq, ← reducedNorm_naturality, ← reducedNorm_naturality]
  change reducedNorm E B T (bend (τ.baseChange R x)) = Q (reducedNorm E B T (bend x))
  rw [reducedNorm_eq_det E B e T, reducedNorm_eq_det E B e' T, hmat]
  exact (Q.map_det _).symm.trans (congrArg Q (Matrix.det_transpose _))

end Langlands.CentralSimple
