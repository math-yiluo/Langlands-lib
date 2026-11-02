import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCobar

/-! # Additive cocycles and exact-sequence closure

The flat-test cocycles form an additive subgroup and are functorial in the comodule.
Their vanishing passes to retracts and is closed under extensions when the source
algebra is flat.
-/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M N P : Type v}
variable [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
variable [AddCommGroup P] [Module B P]

theorem isOneCocycle_zero (θ : GroupoidCoaction t M) : θ.IsOneCocycle 0 := by
  intro T _ _ _ φ₁ φ₂ φ₃ h h₃
  simp

theorem isOneCocycle_add (θ : GroupoidCoaction t M) {x y : C ⊗[B] M}
    (hx : θ.IsOneCocycle x) (hy : θ.IsOneCocycle y) : θ.IsOneCocycle (x + y) := by
  intro T _ _ _ φ₁ φ₂ φ₃ h h₃
  simp only [map_add]
  rw [hx T φ₁ φ₂ φ₃ h h₃, hy T φ₁ φ₂ φ₃ h h₃]
  abel

theorem isOneCocycle_neg (θ : GroupoidCoaction t M) {x : C ⊗[B] M}
    (hx : θ.IsOneCocycle x) : θ.IsOneCocycle (-x) := by
  intro T _ _ _ φ₁ φ₂ φ₃ h h₃
  simp only [map_neg]
  rw [hx T φ₁ φ₂ φ₃ h h₃]
  abel

theorem isOneCocycle_sub (θ : GroupoidCoaction t M) {x y : C ⊗[B] M}
    (hx : θ.IsOneCocycle x) (hy : θ.IsOneCocycle y) : θ.IsOneCocycle (x - y) := by
  simpa only [sub_eq_add_neg] using θ.isOneCocycle_add hx (θ.isOneCocycle_neg hy)

/-- The additive subgroup of one-cocycles tested over flat algebras. -/
def oneCocycles (θ : GroupoidCoaction t M) : AddSubgroup (C ⊗[B] M) where
  carrier := θ.IsOneCocycle
  zero_mem' := θ.isOneCocycle_zero
  add_mem' := θ.isOneCocycle_add
  neg_mem' := θ.isOneCocycle_neg

/-- A morphism of coactions sends one-cocycles to one-cocycles. -/
theorem isOneCocycle_map {θM : GroupoidCoaction t M} {θN : GroupoidCoaction t N}
    (f : M →ₗ[B] N) (hf : θM.IsHom θN f) {x : C ⊗[B] M}
    (hx : θM.IsOneCocycle x) : θN.IsOneCocycle (LinearMap.lTensor C f x) := by
  intro T _ _ _ φ₁ φ₂ φ₃ h h₃
  simp only [tensor_naturality, coactionCompose_naturality f hf]
  rw [hx T φ₁ φ₂ φ₃ h h₃, map_add]

/-- Vanishing passes to any retract through morphisms of coactions. -/
theorem oneCohomologyVanishes_of_retract {θM : GroupoidCoaction t M}
    {θN : GroupoidCoaction t N} (i : M →ₗ[B] N) (p : N →ₗ[B] M)
    (hi : θM.IsHom θN i) (hp : θN.IsHom θM p)
    (hpi : p.comp i = LinearMap.id) (hN : θN.OneCohomologyVanishes) :
    θM.OneCohomologyVanishes := by
  intro x hx
  obtain ⟨n, hn⟩ := hN _ (isOneCocycle_map i hi hx)
  refine ⟨p n, ?_⟩
  rw [coboundary_naturality p hp, hn, ← LinearMap.lTensor_comp_apply, hpi,
    LinearMap.lTensor_id_apply]

/-- For a short exact sequence, vanishing for the kernel and quotient implies
vanishing for the middle term. -/
theorem oneCohomologyVanishes_of_shortExact [Module.Flat B C]
    {θM : GroupoidCoaction t M} {θN : GroupoidCoaction t N}
    {θP : GroupoidCoaction t P} (i : M →ₗ[B] N) (p : N →ₗ[B] P)
    (hi : θM.IsHom θN i) (hp : θN.IsHom θP p)
    (hinj : Function.Injective i) (hsurj : Function.Surjective p)
    (hex : LinearMap.range i = LinearMap.ker p)
    (hM : θM.OneCohomologyVanishes) (hP : θP.OneCohomologyVanishes) :
    θN.OneCohomologyVanishes := by
  intro x hx
  obtain ⟨q, hq⟩ := hP _ (isOneCocycle_map p hp hx)
  obtain ⟨n, hn⟩ := hsurj q
  have hzero : LinearMap.lTensor C p (x - θN.coboundary n) = 0 := by
    rw [map_sub, ← coboundary_naturality p hp, hn, hq, sub_self]
  have htex := Module.Flat.lTensor_exact C (LinearMap.exact_iff.mpr hex.symm)
  obtain ⟨z, hz⟩ := (htex (x - θN.coboundary n)).mp hzero
  have hc : θM.IsOneCocycle z :=
    isOneCocycle_of_injective i hi hinj z
      (hz.symm ▸ θN.isOneCocycle_sub hx (θN.isOneCocycle_coboundary n))
  obtain ⟨m, hm⟩ := hM z hc
  refine ⟨n + i m, ?_⟩
  rw [map_add, coboundary_naturality i hi, hm, hz]
  abel

end Langlands.AlgebraicGeometry.GroupoidCoaction
