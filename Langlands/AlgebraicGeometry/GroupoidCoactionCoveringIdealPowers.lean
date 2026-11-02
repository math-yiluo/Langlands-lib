import Langlands.AlgebraicGeometry.GroupoidCoactionCoveringHom
import Langlands.AlgebraicGeometry.GroupoidCoactionEffectiveDescent
import Langlands.AlgebraicGeometry.GroupoidCoactionInvariantIdeal

/-! # Covering ideal powers and their vanishing -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C D P : Type u} [CommRing B] [CommRing C] [CommRing D] [CommRing P]
  [Algebra B C] [Algebra B D] [Algebra D P]
  [Algebra B P] [IsScalarTower B D P]
variable (e : P ≃ₐ[D] D ⊗[B] C)
variable {t : B →+* C} {td : D →+* P}
variable (ht : (cartesianBaseMap e).comp t = td.comp (algebraMap B D))

section Naturality

variable {M N : Type v} [AddCommGroup M] [Module D M] [Module B M]
  [IsScalarTower B D M] [AddCommGroup N] [Module D N] [Module B N]
  [IsScalarTower B D N]

/-- Cartesian tensor cancellation is natural for covering-linear maps. -/
lemma pushforwardTensorEquiv_naturality (f : M →ₗ[D] N) (x : P ⊗[D] M) :
    pushforwardTensorEquiv e (LinearMap.lTensor P f x) =
      LinearMap.lTensor C (f.restrictScalars B) (pushforwardTensorEquiv e x) := by
  obtain ⟨x, rfl⟩ := (pushforwardTensorEquiv (M := M) e).symm.surjective x
  induction x using TensorProduct.inductionOn with
  | tmul c m =>
    simp only [pushforwardTensorEquiv_symm_tmul, LinearMap.lTensor_tmul,
      pushforwardTensorEquiv_base_tmul, LinearMap.restrictScalars_apply]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

variable (hE : RingEtaleEquivalenceRelation t) (hP : RingEtaleEquivalenceRelation td)
variable {ψM : GroupoidCoaction td M} {ψN : GroupoidCoaction td N}

/-- Equivariant covering-linear maps remain equivariant after pushforward. -/
lemma IsHom.pushforward (f : M →ₗ[D] N) (hf : ψM.IsHom ψN f) :
    (pushforward e ht ψM hE hP).IsHom (pushforward e ht ψN hE hP)
      (f.restrictScalars B) := by
  intro m
  change pushforwardTensorEquiv e (ψN.coaction (f m)) =
    LinearMap.lTensor C (f.restrictScalars B) (pushforwardTensorEquiv e (ψM.coaction m))
  rw [hf, pushforwardTensorEquiv_naturality]

/-- Pushforward commutes with restriction to a stable covering submodule. -/
lemma pushforward_submodule (ψ : GroupoidCoaction td M) (N : Submodule D M)
    (hN : ψ.IsStableSubmodule N)
    (hNB : (pushforward e ht ψ hE hP).IsStableSubmodule (N.restrictScalars B)) :
    pushforward e ht (submodule ψ N hP hN) hE hP =
      submodule (pushforward e ht ψ hE hP) (N.restrictScalars B) hE hNB := by
  let : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  have hcover := (submodule_subtype_isHom ψ N hP hN).pushforward e ht hE hP N.subtype
  have hbase := submodule_subtype_isHom (pushforward e ht ψ hE hP)
    (N.restrictScalars B) hE hNB
  apply ext_coaction
  ext n
  apply Module.Flat.lTensor_preserves_injective_linearMap
    (N.restrictScalars B).subtype (N.restrictScalars B).subtype_injective
  exact (hcover n).symm.trans (hbase n)

end Naturality

omit [Algebra B P] [IsScalarTower B D P] in
include e ht in
/-- An invariant base ideal extends to an invariant covering ideal. -/
lemma IsInvariantIdeal.map_cartesian {I : Ideal B} (hI : IsInvariantIdeal t I) :
    IsInvariantIdeal td (I.map (algebraMap B D)) := by
  change (I.map (algebraMap B D)).map td =
    (I.map (algebraMap B D)).map (algebraMap D P)
  rw [Ideal.map_map, ← ht, ← Ideal.map_map, hI, Ideal.map_map,
    cartesianBaseMap_comp_source, ← Ideal.map_map]

variable {M : Type v} [AddCommGroup M] [Module D M] [Module B M]
  [IsScalarTower B D M]

/-- The covering submodule obtained by multiplication by a base ideal power. -/
def coveringIdealPowerSubmodule (I : Ideal B) (n : ℕ) : Submodule D M :=
  (I ^ n).map (algebraMap B D) • ⊤

@[simp]
lemma coveringIdealPowerSubmodule_restrictScalars (I : Ideal B) (n : ℕ) :
    (coveringIdealPowerSubmodule (D := D) (M := M) I n).restrictScalars B =
      I ^ n • (⊤ : Submodule B M) := by
  rw [coveringIdealPowerSubmodule, Submodule.restrictScalars_map_smul_eq,
    Submodule.restrictScalars_top]

section Vanishing

variable {X : Type (max u v)} [AddCommGroup X] [Module D X] [Module B X]
  [IsScalarTower B D X]
variable (hE : RingEtaleEquivalenceRelation t) (hP : RingEtaleEquivalenceRelation td)
variable (ψ : GroupoidCoaction td X)
variable (ε : P ≃ₐ[D] D ⊗[invariantRing td] D)
  (hε : ∀ d : D, ε (td d) = (1 : D) ⊗ₜ[invariantRing td] d)
variable [Module.FaithfullyFlat (invariantRing td) D]

include ε hε in
/-- Stable covering submodules have vanishing after pushforward from an effective
faithfully flat covering presentation. -/
theorem submodule_pushforward_oneCohomologyVanishes
    (N : Submodule D X) (hN : ψ.IsStableSubmodule N)
    (hNB : (pushforward e ht ψ hE hP).IsStableSubmodule (N.restrictScalars B)) :
    (submodule (pushforward e ht ψ hE hP) (N.restrictScalars B) hE hNB).OneCohomologyVanishes := by
  rw [← pushforward_submodule e ht hE hP ψ N hN hNB]
  exact pushforward_oneCohomologyVanishes e ht (submodule ψ N hP hN) hE hP
    (oneCohomologyVanishes_of_faithfullyFlat_presentation hP (submodule ψ N hP hN) ε hε)

include ε hε in
/-- Every invariant base ideal-power submodule of a pushed covering coaction
has vanishing under an effective faithfully flat covering presentation. -/
theorem idealPower_pushforward_oneCohomologyVanishes
    (I : Ideal B) (hI : IsInvariantIdeal t I) (n : ℕ)
    (hstable : (pushforward e ht ψ hE hP).IsStableSubmodule
      (I ^ n • (⊤ : Submodule B X))) :
    (submodule (pushforward e ht ψ hE hP) _ hE hstable).OneCohomologyVanishes := by
  let : Module.Flat D P := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hP.etale_algebraMap).1
  let N := coveringIdealPowerSubmodule (D := D) (M := X) I n
  have hN : ψ.IsStableSubmodule N :=
    ((hI.pow n).map_cartesian e ht).isStableSubmodule_smul_top ψ
  have hvan : ∀ hNB : (pushforward e ht ψ hE hP).IsStableSubmodule
      (N.restrictScalars B),
      (submodule (pushforward e ht ψ hE hP) (N.restrictScalars B) hE hNB).OneCohomologyVanishes :=
    fun hNB => submodule_pushforward_oneCohomologyVanishes e ht hE hP ψ ε hε N hN hNB
  have hNB : N.restrictScalars B = I ^ n • (⊤ : Submodule B X) :=
    coveringIdealPowerSubmodule_restrictScalars I n
  rw [hNB] at hvan
  exact hvan hstable

end Vanishing

section HomVanishing

attribute [local instance 50] homSourceModule homSourceTower

variable {Y H : Type (max u v)} [AddCommGroup Y] [Module D Y] [Module B Y]
  [IsScalarTower B D Y] [AddCommGroup H] [Module B H]
  [Module.FinitePresentation B Y]
variable (hE : RingEtaleEquivalenceRelation t) (hP : RingEtaleEquivalenceRelation td)
variable (ψ : GroupoidCoaction td Y) (θ : GroupoidCoaction t H)
variable (ε : P ≃ₐ[D] D ⊗[invariantRing td] D)
  (hε : ∀ d : D, ε (td d) = (1 : D) ⊗ₜ[invariantRing td] d)
variable [Module.FaithfullyFlat (invariantRing td) D]

include ε hε in
/-- The base Hom coaction with a pushed covering source has degree-one
vanishing when the covering relation is an effective faithfully flat relation. -/
theorem hom_pushforward_oneCohomologyVanishes :
    (hom hE (pushforward e ht ψ hE hP) θ).OneCohomologyVanishes := by
  rw [← pushforward_coveringHom e ht hE hP ψ θ]
  exact pushforward_oneCohomologyVanishes e ht (coveringHom e ht hE hP ψ θ) hE hP
    (oneCohomologyVanishes_of_faithfullyFlat_presentation hP
      (coveringHom e ht hE hP ψ θ) ε hε)

include ε hε in
/-- Every invariant ideal-power restriction of the base Hom coaction has
degree-one vanishing under an effective faithfully flat covering presentation. -/
theorem idealPower_hom_pushforward_oneCohomologyVanishes
    (I : Ideal B) (hI : IsInvariantIdeal t I) (n : ℕ)
    (hstable : (hom hE (pushforward e ht ψ hE hP) θ).IsStableSubmodule
      (I ^ n • (⊤ : Submodule B (Y →ₗ[B] H)))) :
    (submodule (hom hE (pushforward e ht ψ hE hP) θ) _ hE hstable).OneCohomologyVanishes := by
  have hvan := idealPower_pushforward_oneCohomologyVanishes e ht hE hP
    (coveringHom e ht hE hP ψ θ) ε hε I hI n
  simp only [pushforward_coveringHom] at hvan
  exact hvan hstable

end HomVanishing

end Langlands.AlgebraicGeometry.GroupoidCoaction
