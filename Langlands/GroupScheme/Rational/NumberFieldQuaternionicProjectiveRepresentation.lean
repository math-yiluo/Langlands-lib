import Langlands.GroupScheme.Quaternionic.SkewHermitianComponentBaseChange
import Langlands.LinearAlgebra.NumberFieldQuadraticIsometryProof
import Langlands.Global.AdelicFunctoriality.Infinite
import Langlands.Global.AdelicFunctoriality.Extension

/-! # Projective representation of a pure quaternion by a skew-hermitian form -/

noncomputable section

universe u

open TensorProduct LinearMap NumberField IsDedekindDomain
open scoped TensorProduct NumberField

namespace Langlands.GroupScheme.KneserThree.QuatData

open QuadField Quaternionic Global.AdelicFunctoriality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  {τ : FirstKindInvolution F D} {V : Type u} [AddCommGroup V]
  [Module D V] [Module F V] [IsScalarTower F D V]
  (B : AntihermitianForm τ V)

private theorem bilinear_baseChange_map {K R : Type u}
    [Field K] [Algebra F K] [Field R] [Algebra F R]
    (f : K →ₐ[F] R) (x y : K ⊗[F] V) :
    TensorProduct.map f.toLinearMap (LinearMap.id : D →ₗ[F] D)
      (LinearMap.BilinMap.baseChange K B.toBilin x y) =
    LinearMap.BilinMap.baseChange R B.toBilin
      (TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[F] V) x)
      (TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[F] V) y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul k v =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul k' v' =>
      simp only [LinearMap.BilinMap.baseChange_tmul, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        LinearMap.id_apply, map_mul]

variable [NumberField F] [FiniteDimensional F V] (Q : QuatData F D)
  (hbar : ∀ z, τ z = Q.bar z)

local notation "E" => field Q.c

include hbar in
/-- If every completion represents the chosen pure quaternion, the form represents
  a value in its ground-field line on a nonzero vector. -/
theorem exists_nonzero_vector_on_pureLine (hB : B.toBilin.SeparatingLeft)
    (hlocal : ∀ v : Global.Place F, let R := Global.placeCompletion F v
      ∃ t : R ⊗[F] V, LinearMap.BilinMap.baseChange R B.toBilin t t =
        (1 : R) ⊗ₜ[F] Q.x) :
    ∃ x : V, x ≠ 0 ∧ ∃ a : F, B x x = a • Q.x := by
  let : NumberField E := NumberField.of_module_finite F E
  let : Module E V := Module.compHom V Q.ι.toRingHom
  let : IsScalarTower F E V := ⟨fun a b x => by
    change (Q.ι (a • b)) • x = a • (Q.ι b • x)
    rw [map_smul, smul_assoc]⟩
  let : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite F E V
  let : Invertible (2 : E) := invertibleOfNonzero (two_ne_zero : (2 : E) ≠ 0)
  let H := Q.symmetricComponent B hbar
  let q : QuadraticForm E V := H.toQuadraticMap
  have hH := Q.symmetricComponent_nondegenerate B hbar hB
  have hpolar (x y : V) : q.polarBilin x y = (2 : E) * H x y := by
    change H.toQuadraticMap.polarBilin x y = _
    rw [LinearMap.BilinMap.polarBilin_toQuadraticMap, LinearMap.add_apply, LinearMap.add_apply,
      LinearMap.flip_apply, show H y x = H x y from Q.symmetricComponent_swap B hbar x y, two_mul]
  have hq : q.polarBilin.Nondegenerate := by
    refine ⟨fun x hx => hH.1 x fun y => ?_, fun y hy => hH.2 y fun x => ?_⟩
    · exact (mul_eq_zero.mp ((hpolar x y).symm.trans (hx y))).resolve_left two_ne_zero
    · exact (mul_eq_zero.mp ((hpolar x y).symm.trans (hy x))).resolve_left two_ne_zero
  have localComparison {K R : Type u} [Field K] [Algebra F K] [Field R] [Algebra F R]
      [Algebra E R] [IsScalarTower F E R] (f : K →ₐ[F] R) (t : K ⊗[F] V)
      (ht : LinearMap.BilinMap.baseChange K B.toBilin t t = (1 : K) ⊗ₜ[F] Q.x) :
      ¬ (q.baseChange R).Anisotropic := by
    let u := TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[F] V) t
    have hu : LinearMap.BilinMap.baseChange R B.toBilin u u = (1 : R) ⊗ₜ[F] Q.x := by
      rw [← bilinear_baseChange_map B f t t, ht, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, LinearMap.id_apply]
    obtain ⟨w, hw, hz⟩ := Q.exists_isotropic_component_of_representation B hbar R u hu
    apply (QuadraticMap.not_anisotropic_iff_exists _).mpr
    refine ⟨w, hw, ?_⟩
    have hbase : q.baseChange R = (LinearMap.BilinForm.baseChange R H).toQuadraticMap := by
      apply baseChange_ext
      intro x
      rw [QuadraticForm.baseChange_tmul]
      change H x x • ((1 : R) * 1) =
        LinearMap.BilinForm.baseChange R H ((1 : R) ⊗ₜ[E] x) ((1 : R) ⊗ₜ[E] x)
      rw [LinearMap.BilinForm.baseChange_tmul]
    rw [hbase, LinearMap.BilinMap.toQuadraticMap_apply]
    exact hz
  have hplaces (w : Global.Place E) : ¬ (q.baseChange (Global.placeCompletion E w)).Anisotropic := by
    rcases w with w | w
    · let v := w.comap (algebraMap F E)
      let R := w.Completion
      let : Algebra F R := Algebra.compHom R (algebraMap F E)
      let : IsScalarTower F E R := IsScalarTower.of_algebraMap_eq fun _ => rfl
      let f : v.Completion →ₐ[F] R :=
        { toRingHom := infiniteCompletionMap (algebraMap F E) w
          commutes' := infiniteCompletionMap_coe (algebraMap F E) w }
      obtain ⟨t, ht⟩ := hlocal (.inl v)
      change ¬ (q.baseChange w.Completion).Anisotropic
      exact localComparison (K := v.Completion) (R := w.Completion) f t ht
    · let v := w.under (𝓞 F)
      let R := Global.FiniteCompletion E w
      let : Algebra F R := Algebra.compHom R (algebraMap F E)
      let : IsScalarTower F E R := IsScalarTower.of_algebraMap_eq fun _ => rfl
      let f : Global.FiniteCompletion F v →ₐ[F] R :=
        { toRingHom := FiniteExtension.completionMap v w
          commutes' := FiniteExtension.completionMap_coe v w }
      obtain ⟨t, ht⟩ := hlocal (.inr v)
      change ¬ (q.baseChange (Global.FiniteCompletion E w)).Anisotropic
      exact localComparison (K := Global.FiniteCompletion F v) (R := Global.FiniteCompletion E w) f t ht
  obtain ⟨x, hx, hzero⟩ := (QuadraticMap.not_anisotropic_iff_exists q).mp
    (Langlands.numberFieldQuadraticIsotropy_of_cyclicNorm ClassFieldTheory.Global.cyclicHasseNorm E V q hq hplaces)
  exact ⟨x, hx, (Q.symmetricComponent_self_eq_zero_iff B hbar two_ne_zero x).mp hzero⟩

end Langlands.GroupScheme.KneserThree.QuatData

namespace Langlands.GroupScheme.Quaternionic

open KneserThree

/-- Springer's projective representation lemma for quaternionic skew-hermitian forms. -/
def NumberFieldQuaternionicProjectiveRepresentationStatement : Prop :=
  ∀ (F D : Type u) [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D] (σ : FirstKindInvolution F D)
    (hdim : Module.finrank F D = 4) (hsym : Module.finrank F σ.symmetricSubspace = 3),
    let τ := σ.quaternionConjugation hdim hsym
    ∀ (V : Type u) [AddCommGroup V] [Module D V] [Module F V] [IsScalarTower F D V]
      [FiniteDimensional F V] (B : AntihermitianForm τ V) (a : D),
      B.toBilin.SeparatingLeft → a ≠ 0 → τ a = -a →
      (∀ v : Global.Place F, let R := Global.placeCompletion F v
        ∃ t : R ⊗[F] V, LinearMap.BilinMap.baseChange R B.toBilin t t = (1 : R) ⊗ₜ[F] a) →
      ∃ x : V, x ≠ 0 ∧ ∃ b : F, B x x = b • a

/-- Apply Hasse–Minkowski to the symmetric component over the pure quaternion's quadratic field. -/
theorem numberFieldQuaternionicProjectiveRepresentation :
    NumberFieldQuaternionicProjectiveRepresentationStatement.{u} := by
  intro F D _ _ _ _ _ _ σ hdim hsym τ V _ _ _ _ _ B a hB ha hτ hl
  obtain ⟨Q, hQa, hQ⟩ := Quaternion.exists_quatData_of_pure σ hdim hsym two_ne_zero ha hτ
  have hloc (v : Global.Place F) : let R := Global.placeCompletion F v
      ∃ t : R ⊗[F] V, LinearMap.BilinMap.baseChange R B.toBilin t t = (1 : R) ⊗ₜ[F] Q.x := by
    rw [hQa]
    exact hl v
  obtain ⟨x, hx, b, hb⟩ := Q.exists_nonzero_vector_on_pureLine B hQ hB hloc
  exact ⟨x, hx, b, hb.trans (congrArg (b • ·) hQa)⟩

end Langlands.GroupScheme.Quaternionic
