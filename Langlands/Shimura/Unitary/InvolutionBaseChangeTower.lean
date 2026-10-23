import Langlands.Shimura.Unitary.Similitude

noncomputable section
universe u v w z
open scoped TensorProduct

namespace Langlands.Shimura.AlgebraInvolution

section Equivalence
variable {R : Type u} {A : Type v} {B : Type w}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  (σ : AlgebraInvolution R A) (τ : AlgebraInvolution R B)
  (e : A ≃ₐ[R] B) (he : ∀ a, e (σ a) = τ (e a))

include he in
/-- An algebra equivalence intertwining involutions also intertwines their inverses. -/
theorem equiv_symm_involution (b : B) : e.symm (τ b) = σ (e.symm b) := by
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

/-- Transport similitudes through an actual involution-preserving algebra equivalence. -/
def similitudesEquiv : σ.similitudes ≃* τ.similitudes where
  toFun := σ.map τ e.toRingHom (RingHom.id R) he (fun r => e.commutes r)
  invFun := τ.map σ e.symm.toRingHom (RingHom.id R)
    (equiv_symm_involution σ τ e he) (fun r => e.symm.commutes r)
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact Units.ext (e.symm_apply_apply (x.val.1 : A))
    · exact Units.ext rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact Units.ext (e.apply_symm_apply (x.val.1 : B))
    · exact Units.ext rfl
  map_mul' := (σ.map τ e.toRingHom (RingHom.id R) he (fun r => e.commutes r)).map_mul

@[simp] theorem similitudesEquiv_unit (x : σ.similitudes) :
    ((similitudesEquiv σ τ e he x).val.1 : B) = e (x.val.1 : A) := rfl

@[simp] theorem similitudesEquiv_multiplier (x : σ.similitudes) :
    τ.multiplier (similitudesEquiv σ τ e he x) = σ.multiplier x := by
  exact Units.ext rfl

/-- Restrict an involution-preserving algebra equivalence to the unitary groups. -/
def unitaryEquiv : σ.unitary ≃* τ.unitary where
  toFun x := ⟨Units.map e.toMonoidHom x.val, by
    rw [τ.mem_unitary_iff]
    change e (x.val : A) * τ (e (x.val : A)) = 1
    rw [← he, ← _root_.map_mul, (σ.mem_unitary_iff x.val).mp x.property,
      _root_.map_one]⟩
  invFun x := ⟨Units.map e.symm.toMonoidHom x.val, by
    rw [σ.mem_unitary_iff]
    change e.symm (x.val : B) * σ (e.symm (x.val : B)) = 1
    rw [← equiv_symm_involution σ τ e he, ← _root_.map_mul,
      (τ.mem_unitary_iff x.val).mp x.property, _root_.map_one]⟩
  left_inv x := Subtype.ext (Units.ext (e.symm_apply_apply (x.val : A)))
  right_inv x := Subtype.ext (Units.ext (e.apply_symm_apply (x.val : B)))
  map_mul' x y := Subtype.ext (Units.ext (e.map_mul (x.val : A) (y.val : A)))

@[simp] theorem unitaryEquiv_unit (x : σ.unitary) :
    ((unitaryEquiv σ τ e he x).val : B) = e (x.val : A) := rfl

/-- The two transported groups have the same inclusion with multiplier one. -/
theorem unitaryEquiv_inclusion (x : σ.unitary) :
    τ.unitaryInclusion (unitaryEquiv σ τ e he x) =
      similitudesEquiv σ τ e he (σ.unitaryInclusion x) :=
  Subtype.ext (Prod.ext rfl (Units.ext rfl))

end Equivalence

section Tower
variable (R : Type u) (S : Type v) (T : Type w) (A : Type z)
  [CommRing R] [CommRing S] [CommRing T] [Ring A]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Algebra R A]

/-- Repeated scalar extension of a possibly noncommutative algebra, in the expansion direction. -/
def baseChangeTowerEquiv : T ⊗[R] A ≃ₐ[T] T ⊗[S] (S ⊗[R] A) :=
  AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A).symm
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ => by
      simp [Algebra.TensorProduct.tmul_mul_tmul]))

@[simp] theorem baseChangeTowerEquiv_tmul (t : T) (a : A) :
    baseChangeTowerEquiv R S T A (t ⊗ₜ[R] a) = t ⊗ₜ[S] ((1 : S) ⊗ₜ[R] a) := rfl

@[simp] theorem baseChangeTowerEquiv_symm_tmul (t : T) (s : S) (a : A) :
    (baseChangeTowerEquiv R S T A).symm (t ⊗ₜ[S] (s ⊗ₜ[R] a)) =
      (s • t) ⊗ₜ[R] a := rfl

variable {R A} (σ : AlgebraInvolution R A)

/-- The tensor-tower comparison preserves the coefficient-fixed involutions. -/
theorem baseChangeTowerEquiv_involution (x : T ⊗[R] A) :
    baseChangeTowerEquiv R S T A (σ.baseChange T x) =
      (σ.baseChange S).baseChange T (baseChangeTowerEquiv R S T A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul t a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Similitudes of direct and repeated scalar extension, with the same multiplier. -/
def baseChangeTowerSimilitudes :
    (σ.baseChange T).similitudes ≃* ((σ.baseChange S).baseChange T).similitudes :=
  similitudesEquiv (σ.baseChange T) ((σ.baseChange S).baseChange T)
    (baseChangeTowerEquiv R S T A) (baseChangeTowerEquiv_involution S T σ)

@[simp] theorem baseChangeTowerSimilitudes_unit (x : (σ.baseChange T).similitudes) :
    ((baseChangeTowerSimilitudes S T σ x).val.1 : T ⊗[S] (S ⊗[R] A)) =
      baseChangeTowerEquiv R S T A (x.val.1 : T ⊗[R] A) := rfl

@[simp] theorem baseChangeTowerSimilitudes_multiplier (x : (σ.baseChange T).similitudes) :
    ((σ.baseChange S).baseChange T).multiplier (baseChangeTowerSimilitudes S T σ x) =
      (σ.baseChange T).multiplier x :=
  similitudesEquiv_multiplier _ _ _ _ x

/-- Unitary groups of direct and repeated scalar extension. -/
def baseChangeTowerUnitary :
    (σ.baseChange T).unitary ≃* ((σ.baseChange S).baseChange T).unitary :=
  unitaryEquiv (σ.baseChange T) ((σ.baseChange S).baseChange T)
    (baseChangeTowerEquiv R S T A) (baseChangeTowerEquiv_involution S T σ)

@[simp] theorem baseChangeTowerUnitary_unit (x : (σ.baseChange T).unitary) :
    ((baseChangeTowerUnitary S T σ x).val : T ⊗[S] (S ⊗[R] A)) =
      baseChangeTowerEquiv R S T A (x.val : T ⊗[R] A) := rfl

theorem baseChangeTowerUnitary_inclusion (x : (σ.baseChange T).unitary) :
    ((σ.baseChange S).baseChange T).unitaryInclusion (baseChangeTowerUnitary S T σ x) =
      baseChangeTowerSimilitudes S T σ ((σ.baseChange T).unitaryInclusion x) :=
  unitaryEquiv_inclusion _ _ _ _ x

variable {S T} {U : Type w} [CommRing U] [Algebra R U] [Algebra S U]
  [IsScalarTower R S U]

/-- Tensor-tower expansion commutes with every map of the final coefficient algebra. -/
theorem baseChangeTowerEquiv_naturality (f : T →ₐ[S] U) (x : T ⊗[R] A) :
    baseChangeTowerEquiv R S U A (changeCoefficients (f.restrictScalars R) x) =
      changeCoefficients (A := S ⊗[R] A) f (baseChangeTowerEquiv R S T A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul t a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The similitude comparison is natural in the final coefficient algebra. -/
theorem baseChangeTowerSimilitudes_naturality (f : T →ₐ[S] U)
    (x : (σ.baseChange T).similitudes) :
    baseChangeTowerSimilitudes S U σ
      (σ.baseChangeMap (CommAlgCat.ofHom (f.restrictScalars R)) x) =
      (σ.baseChange S).baseChangeMap (CommAlgCat.ofHom f)
        (baseChangeTowerSimilitudes S T σ x) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    exact baseChangeTowerEquiv_naturality f (x.val.1 : T ⊗[R] A)
  · exact Units.ext rfl

end Tower
end Langlands.Shimura.AlgebraInvolution
