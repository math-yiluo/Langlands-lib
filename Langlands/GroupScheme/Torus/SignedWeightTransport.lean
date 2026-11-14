import Langlands.GroupScheme.Torus.SignedWeightCount
import Langlands.GroupScheme.Torus.WeightDecomposition

/-! # Transporting signed coordinate weights to actual torus characters -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Module

namespace Langlands.GroupScheme.SignedWeightTransport

variable {K : Type u} [Field K] {I : Type u} [Fintype I]
  {S : CommGroupScheme (Spec (CommRingCat.of K))}

local notation "T" => splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I

/-- Integer coordinate weights give actual characters of an isomorphic torus. -/
def characterEquiv (e : S.toGrp ≅ (splitTorus (Spec (CommRingCat.of K)) I)) : (I → ℤ) ≃ₗ[ℤ] characterLattice S :=
  ((splitTorus.characterLatticeEquiv K I).symm.trans
    (characterLattice.comapIso e)).toIntLinearEquiv

/-- Pullback of characters preserves their pairing with a transported cocharacter. -/
theorem latticePairing_characterEquiv (e : S.toGrp ≅ (splitTorus (Spec (CommRingCat.of K)) I))
    (m : I → ℤ) (ν : cocharacterLattice S) :
    latticePairing S (characterEquiv e m) ν =
      latticePairing T ((splitTorus.characterLatticeEquiv K I).symm m)
        (ν ≫ Additive.ofMul e.hom) := by
  rw [latticePairing_apply, latticePairing_apply]
  apply congrArg (gmEndEquiv K)
  exact Category.assoc ν (Additive.ofMul e.hom)
    ((splitTorus.characterLatticeEquiv K I).symm m)

/-- Pairing with a cocharacter, read as an integer functional on coordinate weights. -/
def pairingFunctional (e : S.toGrp ≅ (splitTorus (Spec (CommRingCat.of K)) I)) (ν : cocharacterLattice S) :
    (I → ℤ) →ₗ[ℤ] ℤ :=
  ((latticePairing S).flip ν).comp (characterEquiv e).toLinearMap

@[simp] theorem pairingFunctional_apply (e : S.toGrp ≅ (splitTorus (Spec (CommRingCat.of K)) I))
    (ν : cocharacterLattice S) (m : I → ℤ) :
    pairingFunctional e ν m = latticePairing S (characterEquiv e m) ν := rfl

/-- Transport an integral basis of coordinate weights to actual torus characters. -/
def characterBasis {ι : Type*} (e : S.toGrp ≅ (splitTorus (Spec (CommRingCat.of K)) I))
    (b : Basis ι ℤ (I → ℤ)) : Basis ι ℤ (characterLattice S) :=
  b.map (characterEquiv e)

@[simp] theorem characterBasis_apply {ι : Type*} (e : S.toGrp ≅ (splitTorus (Spec (CommRingCat.of K)) I))
    (b : Basis ι ℤ (I → ℤ)) (j : ι) :
    characterBasis e b j = characterEquiv e (b j) := rfl

/-- An integral character basis obtained this way detects every cocharacter. -/
theorem characterBasis_detects_cocharacters {ι : Type*} (e : S.toGrp ≅ (splitTorus (Spec (CommRingCat.of K)) I))
    (b : Basis ι ℤ (I → ℤ)) (ν : cocharacterLattice S)
    (hν : ∀ j, latticePairing S (characterBasis e b j) ν = 0) : ν = 0 := by
  have hf : (latticePairing S).flip ν = 0 := (characterBasis e b).ext hν
  have hz : (ν ≫ Additive.ofMul e.hom : cocharacterLattice T) = 0 := by
    apply (inferInstance : (latticePairing T).IsPerfPair).separatingRight
    intro χ
    have h := LinearMap.congr_fun hf
      (characterEquiv e (splitTorus.characterLatticeEquiv K I χ))
    simpa only [LinearMap.flip_apply, LinearMap.zero_apply,
      latticePairing_characterEquiv, AddEquiv.symm_apply_apply] using h
  have h := congrArg (fun μ : cocharacterLattice T => μ ≫ Additive.ofMul e.inv) hz
  rw [Limits.zero_comp] at h
  change Additive.ofMul ((ν.toMul ≫ e.hom) ≫ e.inv) = 0 at h
  rw [Category.assoc, e.hom_inv_id, Category.comp_id] at h
  exact h

section Dimensions

variable {D V : Type*} [DivisionRing D] [AddCommGroup V] [Module D V]
  [FiniteDimensional D V] {ι : Type*} [Fintype ι]

/-- The signed-pair count for a coordinate decomposition is the actual-character
count on every isomorphic torus, with its residual zero-weight dimension. -/
theorem finrank_eq_signed_card_add_residual (e : S.toGrp ≅ (splitTorus (Spec (CommRingCat.of K)) I))
    (A : Finset (I → ℤ)) (b : Basis ι ℤ (I → ℤ))
    (W : (I → ℤ) → Submodule D V) (hW : iSupIndep W)
    (hspan : (⨆ m ∈ A, W m) = ⊤)
    (hsupport : A.erase 0 = SignedWeightCount.signedWeights b)
    (hzero : 0 ∉ A → W 0 = ⊥)
    (hmult : ∀ p, Module.finrank D (W (SignedWeightCount.signedWeight b p)) = 1)
    (ν : cocharacterLattice S) (c : ℤ) :
    Module.finrank D ↥(⨆ m ∈ A.filter
        (fun m => latticePairing S (characterEquiv e m) ν = c), W m) =
      Nat.card {p : ι × ℤˣ //
        (p.2 : ℤ) * latticePairing S (characterBasis e b p.1) ν = c} +
        if c = 0 then Module.finrank D V - 2 * Fintype.card ι else 0 := by
  have h := SignedWeightCount.finrank_biSup_eq_signed_card_add_zero
    A b W hW hsupport hzero hmult (pairingFunctional e ν) c
  rw [SignedWeightCount.finrank_zero_eq_sub A b W hW hspan hsupport hzero hmult] at h
  simpa only [pairingFunctional_apply, characterBasis_apply] using h

end Dimensions

end Langlands.GroupScheme.SignedWeightTransport
