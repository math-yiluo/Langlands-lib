import Langlands.AlgebraicGeometry.GroupoidCoactionPushforwardCocycle

/-! # Lifting a coaction through source-cartesian coordinates -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C D P : Type u} [CommRing B] [CommRing C] [CommRing D] [CommRing P]
  [Algebra B C] [Algebra B D] [Algebra D P]
  [Algebra B P] [IsScalarTower B D P]
variable (e : P ≃ₐ[D] D ⊗[B] C)
variable {t : B →+* C} {td : D →+* P}
variable (ht : (cartesianBaseMap e).comp t = td.comp (algebraMap B D))
variable {M : Type v} [AddCommGroup M] [Module D M] [Module B M]
  [IsScalarTower B D M]
variable (θ : GroupoidCoaction t M)

/-- The only possible covering coaction map with prescribed pushforward. -/
def cartesianLiftMap : M →+ P ⊗[D] M :=
  (pushforwardTensorEquiv e).symm.toAddMonoidHom.comp θ.coaction

@[simp]
lemma cartesianLiftMap_apply (m : M) :
    cartesianLiftMap e θ m = (pushforwardTensorEquiv e).symm (θ.coaction m) := rfl

@[simp]
lemma pushforwardTensorEquiv_cartesianLiftMap (m : M) :
    pushforwardTensorEquiv e (cartesianLiftMap e θ m) = θ.coaction m :=
  (pushforwardTensorEquiv e).apply_symm_apply _

variable (hδ : ∀ (d : D) (m : M),
  cartesianLiftMap e θ (d • m) = td d • cartesianLiftMap e θ m)

section Points

variable {S : Type u} [CommRing S] [Algebra D S] [Algebra B S]
  [IsScalarTower B D S]

lemma restrictTensorScalars_lift_compose
    (ψ₁ : P →+* S) (ψ₂ : P →ₐ[D] S)
    (h : ψ₁.comp (algebraMap D P) = (ψ₂ : P →+* S).comp td)
    (x : P ⊗[D] M) :
    restrictTensorScalars (B := B) (D := D)
        (coactionCompose t M θ.coaction θ.map_smul
          (ψ₁.comp (cartesianBaseMap e)) (cartesianBasePoint e ψ₂)
          (cartesianBasePoint_compat e ht ψ₁ ψ₂ h) (pushforwardTensorEquiv e x)) =
      coactionCompose td M (cartesianLiftMap e θ) hδ ψ₁ ψ₂ h x := by
  obtain ⟨y, rfl⟩ := (pushforwardTensorEquiv (M := M) e).symm.surjective x
  induction y using TensorProduct.inductionOn with
  | tmul c m =>
    rw [pushforwardTensorEquiv_symm_tmul, pushforwardTensorEquiv_base_tmul]
    change restrictTensorScalars (B := B) (D := D)
        (ψ₁ (cartesianBaseMap e c) •
          LinearMap.rTensor M (cartesianBasePoint e ψ₂).toLinearMap
            (θ.coaction m)) = ψ₁ (cartesianBaseMap e c) •
          LinearMap.rTensor M ψ₂.toLinearMap (cartesianLiftMap e θ m)
    rw [(restrictTensorScalars (B := B) (D := D) (S := S) (M := M)).map_smul,
      ← pushforwardTensorEquiv_cartesianLiftMap e θ m,
      restrictTensorScalars_specialize]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end Points

/-- A base coaction whose cartesian lift is target-semilinear is a covering coaction. -/
def cartesianLiftCoaction : GroupoidCoaction td M where
  coaction := cartesianLiftMap e θ
  map_smul := hδ
  counit S _ _ ψ hψ m := by
    let : Algebra B S := ((algebraMap D S).comp (algebraMap B D)).toAlgebra
    let : IsScalarTower B D S := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hbase : (cartesianBasePoint e ψ : C →+* S).comp t = algebraMap B S := by
      change ((ψ : P →+* S).comp (cartesianBaseMap e)).comp t = _
      rw [RingHom.comp_assoc, ht, ← RingHom.comp_assoc, hψ]
      rfl
    have hh := congrArg (restrictTensorScalars (B := B) (D := D) (M := M))
      (θ.counit S (cartesianBasePoint e ψ) hbase m)
    rw [← pushforwardTensorEquiv_cartesianLiftMap e θ m,
      restrictTensorScalars_specialize, restrictTensorScalars_tmul] at hh
    exact hh
  coassoc S _ _ ψ₁ ψ₂ ψ₃ h h₃ m := by
    let : Algebra B S := ((algebraMap D S).comp (algebraMap B D)).toAlgebra
    let : IsScalarTower B D S := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hh := congrArg (restrictTensorScalars (B := B) (D := D) (M := M))
      (θ.coassoc S (ψ₁.comp (cartesianBaseMap e))
        (cartesianBasePoint e ψ₂) (cartesianBasePoint e ψ₃)
        (cartesianBasePoint_compat e ht ψ₁ ψ₂ h)
        (cartesianBasePoint_target e ht ψ₁ ψ₃ h₃) m)
    rw [← pushforwardTensorEquiv_cartesianLiftMap e θ m,
      restrictTensorScalars_specialize,
      restrictTensorScalars_lift_compose e ht θ hδ ψ₁ ψ₂ h] at hh
    exact hh

/-- Equality of actual coactions is determined by their additive coaction maps. -/
lemma ext_coaction {θ₁ θ₂ : GroupoidCoaction t M}
    (h : θ₁.coaction = θ₂.coaction) : θ₁ = θ₂ := by
  cases θ₁
  cases θ₂
  cases h
  rfl

@[simp]
lemma pushforward_cartesianLiftCoaction
    (hE : RingEtaleEquivalenceRelation t) (hP : RingEtaleEquivalenceRelation td) :
    pushforward e ht (cartesianLiftCoaction e ht θ hδ) hE hP = θ := by
  apply ext_coaction
  ext m
  exact pushforwardTensorEquiv_cartesianLiftMap e θ m

end Langlands.AlgebraicGeometry.GroupoidCoaction
