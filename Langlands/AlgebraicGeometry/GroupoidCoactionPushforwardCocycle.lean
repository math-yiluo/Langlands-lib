import Langlands.AlgebraicGeometry.GroupoidCoactionPushforward
import Langlands.AlgebraicGeometry.GroupoidCoactionAmitsur

/-! # Degree-one vanishing for source-cartesian pushforward -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

section ScalarRestriction

variable {B D S : Type u} [CommRing B] [CommRing D] [CommRing S]
  [Algebra B D] [Algebra D S] [Algebra B S] [IsScalarTower B D S]
variable {M : Type v} [AddCommGroup M] [Module D M] [Module B M]
  [IsScalarTower B D M]

/-- The canonical map from a tensor over the smaller ring to one over the larger ring. -/
def restrictTensorScalars : S ⊗[B] M →ₗ[S] S ⊗[D] M :=
  TensorProduct.mapOfCompatibleSMul D B S S M

@[simp]
lemma restrictTensorScalars_tmul (s : S) (m : M) :
    restrictTensorScalars (B := B) (D := D) (s ⊗ₜ[B] m) = s ⊗ₜ[D] m := rfl

end ScalarRestriction

variable {B C D P : Type u} [CommRing B] [CommRing C] [CommRing D] [CommRing P]
  [Algebra B C] [Algebra B D] [Algebra D P]
variable (e : P ≃ₐ[D] D ⊗[B] C)

section Points

variable {S : Type u} [CommRing S] [Algebra D S] [Algebra B S]
  [IsScalarTower B D S]

/-- A source-preserving covering point induces a source-preserving base point. -/
def cartesianBasePoint (ψ : P →ₐ[D] S) : C →ₐ[B] S where
  toRingHom := (ψ : P →+* S).comp (cartesianBaseMap e)
  commutes' b := by
    change ψ (cartesianBaseMap e (algebraMap B C b)) = algebraMap B S b
    rw [cartesianBaseMap_source, ψ.commutes, IsScalarTower.algebraMap_apply B D S]

@[simp]
lemma cartesianBasePoint_apply (ψ : P →ₐ[D] S) (c : C) :
    cartesianBasePoint e ψ c = ψ (cartesianBaseMap e c) := rfl

variable {t : B →+* C} {td : D →+* P}
variable (ht : (cartesianBaseMap e).comp t = td.comp (algebraMap B D))

include ht in
/-- Composability of covering points implies composability of the induced base points. -/
lemma cartesianBasePoint_compat (ψ₁ : P →+* S) (ψ₂ : P →ₐ[D] S)
    (h : ψ₁.comp (algebraMap D P) = (ψ₂ : P →+* S).comp td) :
    (ψ₁.comp (cartesianBaseMap e)).comp (algebraMap B C) =
      (cartesianBasePoint e ψ₂ : C →+* S).comp t := by
  change (ψ₁.comp (cartesianBaseMap e)).comp (algebraMap B C) =
    ((ψ₂ : P →+* S).comp (cartesianBaseMap e)).comp t
  rw [RingHom.comp_assoc, cartesianBaseMap_comp_source, ← RingHom.comp_assoc, h,
    RingHom.comp_assoc, ← ht, ← RingHom.comp_assoc]

include ht in
/-- The target equality of a covering composite descends to the base relation. -/
lemma cartesianBasePoint_target (ψ₁ : P →+* S) (ψ₃ : P →ₐ[D] S)
    (h₃ : (ψ₃ : P →+* S).comp td = ψ₁.comp td) :
    (cartesianBasePoint e ψ₃ : C →+* S).comp t =
      (ψ₁.comp (cartesianBaseMap e)).comp t := by
  change ((ψ₃ : P →+* S).comp (cartesianBaseMap e)).comp t =
    (ψ₁.comp (cartesianBaseMap e)).comp t
  rw [RingHom.comp_assoc, ht, ← RingHom.comp_assoc, h₃,
    RingHom.comp_assoc, RingHom.comp_assoc, ht]

end Points

section Cocycles

variable [Algebra B P] [IsScalarTower B D P]
variable {M : Type v} [AddCommGroup M] [Module D M] [Module B M]
  [IsScalarTower B D M]
variable {S : Type u} [CommRing S] [Algebra D S] [Algebra B S]
  [IsScalarTower B D S]

/-- Restricting tensor scalars compares specialization at a covering point and its base point. -/
lemma restrictTensorScalars_specialize (ψ : P →ₐ[D] S) (x : P ⊗[D] M) :
    restrictTensorScalars (B := B) (D := D)
        (LinearMap.rTensor M (cartesianBasePoint e ψ).toLinearMap
          (pushforwardTensorEquiv e x)) =
      LinearMap.rTensor M ψ.toLinearMap x := by
  obtain ⟨y, rfl⟩ := (pushforwardTensorEquiv (M := M) e).symm.surjective x
  induction y using TensorProduct.inductionOn with
  | tmul c m => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

variable {t : B →+* C} {td : D →+* P}
variable (ht : (cartesianBaseMap e).comp t = td.comp (algebraMap B D))
variable (θ : GroupoidCoaction td M)
variable (hE : RingEtaleEquivalenceRelation t) (hP : RingEtaleEquivalenceRelation td)

/-- Tensor restriction also compares the composite coaction maps at covering points. -/
lemma restrictTensorScalars_compose (ψ₁ : P →+* S) (ψ₂ : P →ₐ[D] S)
    (h : ψ₁.comp (algebraMap D P) = (ψ₂ : P →+* S).comp td)
    (x : P ⊗[D] M) :
    restrictTensorScalars (B := B) (D := D)
        (coactionCompose t M (pushforward e ht θ hE hP).coaction
          (pushforward e ht θ hE hP).map_smul
          (ψ₁.comp (cartesianBaseMap e)) (cartesianBasePoint e ψ₂)
          (cartesianBasePoint_compat e ht ψ₁ ψ₂ h) (pushforwardTensorEquiv e x)) =
      coactionCompose td M θ.coaction θ.map_smul ψ₁ ψ₂ h x := by
  obtain ⟨y, rfl⟩ := (pushforwardTensorEquiv (M := M) e).symm.surjective x
  induction y using TensorProduct.inductionOn with
  | tmul c m =>
    rw [pushforwardTensorEquiv_symm_tmul, pushforwardTensorEquiv_base_tmul,
      coactionCompose_tmul, coactionCompose_tmul]
    change restrictTensorScalars (B := B) (D := D)
        (ψ₁ (cartesianBaseMap e c) •
          LinearMap.rTensor M (cartesianBasePoint e ψ₂).toLinearMap
            (pushforwardTensorEquiv e (θ.coaction m))) = _
    rw [(restrictTensorScalars (B := B) (D := D) (S := S) (M := M)).map_smul,
      restrictTensorScalars_specialize]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

include hE hP ht in
/-- A base cocycle becomes a covering cocycle under the inverse tensor comparison. -/
theorem isOneCocycle_of_pushforward {x : C ⊗[B] M}
    (hx : (pushforward e ht θ hE hP).IsOneCocycle x) :
    θ.IsOneCocycle ((pushforwardTensorEquiv e).symm x) := by
  intro S _ _ _ ψ₁ ψ₂ ψ₃ h h₃
  let : Algebra B S := ((algebraMap D S).comp (algebraMap B D)).toAlgebra
  let : IsScalarTower B D S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have he := hx.specialize hE (ψ₁.comp (cartesianBaseMap e))
    (cartesianBasePoint e ψ₂) (cartesianBasePoint e ψ₃)
    (cartesianBasePoint_compat e ht ψ₁ ψ₂ h) (cartesianBasePoint_target e ht ψ₁ ψ₃ h₃)
  have he' := congrArg (restrictTensorScalars (B := B) (D := D) (M := M)) he
  rw [map_add] at he'
  have hs (ψ : P →ₐ[D] S) :
      restrictTensorScalars (B := B) (D := D)
          (LinearMap.rTensor M (cartesianBasePoint e ψ).toLinearMap x) =
        LinearMap.rTensor M ψ.toLinearMap ((pushforwardTensorEquiv e).symm x) := by
    simpa only [LinearEquiv.apply_symm_apply] using
      restrictTensorScalars_specialize e ψ ((pushforwardTensorEquiv e).symm x)
  rw [hs ψ₃, hs ψ₂] at he'
  have hc := restrictTensorScalars_compose e ht θ hE hP ψ₁ ψ₂ h
    ((pushforwardTensorEquiv e).symm x)
  simp only [LinearEquiv.apply_symm_apply] at hc
  rw [hc] at he'
  exact he'

/-- The tensor comparison carries covering coboundaries to pushed coboundaries. -/
@[simp]
lemma pushforward_coboundary (m : M) :
    (pushforward e ht θ hE hP).coboundary m =
      pushforwardTensorEquiv e (θ.coboundary m) := by
  simp only [coboundary_apply, map_sub]
  change pushforwardTensorEquiv e (θ.coaction m) - (1 : C) ⊗ₜ[B] m =
    pushforwardTensorEquiv e (θ.coaction m) -
      pushforwardTensorEquiv e ((1 : P) ⊗ₜ[D] m)
  congr 1
  have h := pushforwardTensorEquiv_base_tmul e (1 : C) m
  simpa only [map_one] using h.symm

include hE hP ht in
/-- Degree-one cocycle vanishing transfers from a covering coaction to its pushforward. -/
theorem pushforward_oneCohomologyVanishes (hθ : θ.OneCohomologyVanishes) :
    (pushforward e ht θ hE hP).OneCohomologyVanishes := by
  intro x hx
  obtain ⟨m, hm⟩ := hθ ((pushforwardTensorEquiv e).symm x)
    (isOneCocycle_of_pushforward e ht θ hE hP hx)
  refine ⟨m, ?_⟩
  rw [pushforward_coboundary, hm, LinearEquiv.apply_symm_apply]

include hE hP ht in
/-- A covering coaction with degree-one vanishing has an acyclic pushforward. -/
theorem pushforward_isAcyclic (hθ : θ.OneCohomologyVanishes) :
    (pushforward e ht θ hE hP).IsAcyclic := by
  let : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  exact isAcyclic_of_oneCohomologyVanishes (pushforward e ht θ hE hP)
    (pushforward_oneCohomologyVanishes e ht θ hE hP hθ)

end Cocycles

section Induced

variable [Algebra B P] [IsScalarTower B D P]
variable {t : B →+* C} {td : D →+* P}
variable (ht : (cartesianBaseMap e).comp t = td.comp (algebraMap B D))
variable (hE : RingEtaleEquivalenceRelation t) (hP : RingEtaleEquivalenceRelation td)
variable (ε : D ⊗[invariantRing td] D ≃ₐ[D] P)
variable (hε : ∀ d : D, ε ((1 : D) ⊗ₜ[invariantRing td] d) = td d)
variable (N : Type v) [AddCommGroup N] [Module (invariantRing td) N]

include hε in
/-- Induced modules on a faithfully flat effective covering relation have vanishing
degree-one cohomology after pushforward. -/
theorem pushforward_induced_oneCohomologyVanishes
    [Module.FaithfullyFlat (invariantRing td) D] :
    (pushforward e ht (induced td N) hE hP).OneCohomologyVanishes :=
  pushforward_oneCohomologyVanishes e ht (induced td N) hE hP
    (induced_oneCohomologyVanishes_of_faithfullyFlat ε hε N hP)

include hε in
/-- The pushforward of such an induced module satisfies invariant lifting. -/
theorem pushforward_induced_isAcyclic
    [Module.FaithfullyFlat (invariantRing td) D] :
    (pushforward e ht (induced td N) hE hP).IsAcyclic :=
  pushforward_isAcyclic e ht (induced td N) hE hP
    (induced_oneCohomologyVanishes_of_faithfullyFlat ε hε N hP)

end Induced

end Langlands.AlgebraicGeometry.GroupoidCoaction
