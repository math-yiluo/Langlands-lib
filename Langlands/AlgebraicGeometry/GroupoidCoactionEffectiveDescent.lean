import Langlands.AlgebraicGeometry.GroupoidCoactionTensorDescent
import Langlands.AlgebraicGeometry.GroupoidCoactionCounit
import Langlands.AlgebraicGeometry.GroupoidCoactionAmitsur
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationComoduleExactness

/-! # Effective flat descent of actual groupoid coactions -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M N : Type (max u v)} [AddCommGroup M] [Module B M]
  [AddCommGroup N] [Module B N]

section Presentation

variable {A : Type u} [CommRing A] [Algebra A B] [Algebra A C]
  [IsScalarTower A B C] [Module A M] [IsScalarTower A B M]
variable (e : C ≃ₐ[B] B ⊗[A] B)
  (ht : ∀ b : B, e (t b) = (1 : B) ⊗ₜ[A] b)

include ht in
lemma presentationTensorEquiv_target_smul (b : B) (x : C ⊗[B] M) :
    presentationTensorEquiv e (t b • x) =
      b • presentationTensorEquiv e x := by
  obtain ⟨y, rfl⟩ := (presentationTensorEquiv (M := M) e).symm.surjective x
  induction y with
  | tmul d m =>
    rw [presentationTensorEquiv_symm_tmul e ht, smul_tmul', smul_eq_mul, ← map_mul]
    rw [← presentationTensorEquiv_symm_tmul e ht (b * d) m,
      ← presentationTensorEquiv_symm_tmul e ht d m,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rfl
  | add y z hy hz => simp only [map_add, smul_add, hy, hz]

lemma presentationCoaction_smul (θ : GroupoidCoaction t M) (b : B) (m : M) :
    presentationCoaction θ e ht (b • m) =
      b • presentationCoaction θ e ht m := by
  change presentationTensorEquiv e (θ.coaction (b • m)) = _
  rw [θ.map_smul, presentationTensorEquiv_target_smul e ht]
  rfl

end Presentation

variable (hE : RingEtaleEquivalenceRelation t) (θ : GroupoidCoaction t M)
variable (e : C ≃ₐ[B] B ⊗[invariantRing t] B)
  (ht : ∀ b : B, e (t b) = (1 : B) ⊗ₜ[invariantRing t] b)

include ht in
lemma presentationCoaction_invariantCounit
    (x : B ⊗[invariantRing t] θ.invariantSubmodule) :
    presentationCoaction θ e ht (invariantCounit θ x) =
      LinearMap.lTensor B θ.invariantSubmodule.subtype x := by
  induction x with
  | tmul b m =>
    rw [invariantCounit_tmul, presentationCoaction_smul e ht]
    rw [(presentationCoaction_fixed_iff θ e ht m).mpr m.property]
    simp [smul_tmul', smul_eq_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

section Flat

variable [Module.Flat (invariantRing t) B]

include hE e ht in
/-- For an effective relation flat over its invariant ring, the canonical
map from the extension of the invariants is bijective. -/
theorem invariantCounit_bijective_of_flat_presentation :
    Function.Bijective (invariantCounit θ) := by
  let A := invariantRing t
  let δ : M →ₗ[A] B ⊗[A] M := presentationCoaction θ e ht
  let d : M →ₗ[A] B ⊗[A] M := δ - tensorCoactionUnit
  have hker : LinearMap.range θ.invariantSubmodule.subtype = LinearMap.ker d := by
    rw [Submodule.range_subtype]
    ext m
    change m ∈ θ.invariants ↔ δ m - (1 : B) ⊗ₜ[A] m = 0
    rw [sub_eq_zero]
    exact (presentationCoaction_fixed_iff θ e ht m).symm
  have hex := Module.Flat.lTensor_exact B (LinearMap.exact_iff.mpr hker.symm)
  have hδ : Function.Injective δ := presentationCoaction_injective hE θ e ht
  constructor
  · intro x y hxy
    apply Module.Flat.lTensor_preserves_injective_linearMap
      θ.invariantSubmodule.subtype θ.invariantSubmodule.subtype_injective
    rw [← presentationCoaction_invariantCounit θ e ht,
      ← presentationCoaction_invariantCounit θ e ht, hxy]
  · intro m
    have hz : LinearMap.lTensor B d (δ m) = 0 := by
      simpa only [d, LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero]
        using presentationCoaction_coassoc θ e ht m
    obtain ⟨x, hx⟩ := (hex (δ m)).mp hz
    refine ⟨x, hδ ?_⟩
    exact (presentationCoaction_invariantCounit θ e ht x).trans hx

/-- The actual descent equivalence, given by scalar multiplication on invariant
elements. Its hypotheses do not include cohomological vanishing. -/
noncomputable def flatPresentationInvariantEquiv :
    B ⊗[invariantRing t] θ.invariantSubmodule ≃ₗ[B] M :=
  LinearEquiv.ofBijective (invariantCounit θ)
    (invariantCounit_bijective_of_flat_presentation hE θ e ht)

@[simp]
lemma flatPresentationInvariantEquiv_apply
    (x : B ⊗[invariantRing t] θ.invariantSubmodule) :
    flatPresentationInvariantEquiv hE θ e ht x = invariantCounit θ x := rfl

end Flat

/-- The inverse of an equivariant linear equivalence is equivariant. -/
lemma IsHom.linearEquiv_symm {θM : GroupoidCoaction t M} {θN : GroupoidCoaction t N}
    (f : M ≃ₗ[B] N) (hf : θM.IsHom θN f.toLinearMap) :
    θN.IsHom θM f.symm.toLinearMap := by
  intro n
  apply (f.lTensor C).injective
  change LinearMap.lTensor C f.toLinearMap (θM.coaction (f.symm n)) =
    LinearMap.lTensor C f.toLinearMap
      (LinearMap.lTensor C f.symm.toLinearMap (θN.coaction n))
  rw [← hf]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [← LinearMap.lTensor_comp_apply]
  simp

include hE e ht in
/-- Every actual coaction for a faithfully flat effective presentation has
degree-one vanishing. -/
theorem oneCohomologyVanishes_of_faithfullyFlat_presentation
    [Module.FaithfullyFlat (invariantRing t) B] :
    θ.OneCohomologyVanishes := by
  let f := flatPresentationInvariantEquiv hE θ e ht
  have hf : (induced t θ.invariantSubmodule).IsHom θ f.toLinearMap :=
    invariantCounit_isHom θ
  apply oneCohomologyVanishes_of_retract f.symm.toLinearMap f.toLinearMap
    (hf.linearEquiv_symm f) hf
  · ext m
    exact f.apply_symm_apply m
  · exact induced_oneCohomologyVanishes_of_faithfullyFlat e.symm
      (fun b => by rw [← ht b, e.symm_apply_apply]) θ.invariantSubmodule hE

include hE e ht in
/-- The invariant-lifting acyclicity predicate for an arbitrary coaction of a
faithfully flat effective relation. -/
theorem isAcyclic_of_faithfullyFlat_presentation
    [Module.FaithfullyFlat (invariantRing t) B] :
    θ.IsAcyclic := by
  let : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  exact isAcyclic_of_oneCohomologyVanishes θ
    (oneCohomologyVanishes_of_faithfullyFlat_presentation hE θ e ht)

end Langlands.AlgebraicGeometry.GroupoidCoaction
