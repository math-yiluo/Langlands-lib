import Langlands.GroupScheme.IntegralModel.CongruencePowers
import Langlands.GroupScheme.IntegralModel.HenselianReduction
import Langlands.GroupScheme.IntegralModel.LieLattice
import Langlands.GroupScheme.Lie.SquareZeroKernelTensorAction
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Basic

/-! # The congruence homomorphism to the Lie lattice quotient -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 120000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Pointwise

namespace Langlands.GroupScheme.IntegralModel

section Coefficients

variable (R : Type u) [CommRing R] [IsLocalRing R]

local notation "𝔪" => IsLocalRing.maximalIdeal R

/-- The actual coefficient ideal of the transition from level `m` to level `n`. -/
abbrev congruenceTransitionIdeal {n m : ℕ+} (h : n ≤ m) : Ideal (congruenceRing R m) :=
  RingHom.ker (congruenceTransitionAlgHom R h)

/-- The image of the shallower maximal-ideal power in the deeper coefficient quotient. -/
def congruenceIdealReduction {n m : ℕ+} (h : n ≤ m) :
    (𝔪 ^ (n : ℕ) : Ideal R) →ₗ[R] congruenceTransitionIdeal R h :=
  LinearMap.codRestrict ((congruenceTransitionIdeal R h : Submodule _ _).restrictScalars R)
    ((Algebra.linearMap R (congruenceRing R m)).comp (𝔪 ^ (n : ℕ) : Ideal R).subtype) (by
      intro a
      change Ideal.Quotient.mk (𝔪 ^ (n : ℕ)) (a : R) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr a.property)

private theorem congruenceIdealReduction_surjective {n m : ℕ+} (h : n ≤ m) :
    Function.Surjective (congruenceIdealReduction R h) := by
  rintro ⟨b, hb⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  change Ideal.Quotient.mk (𝔪 ^ (n : ℕ)) a = 0 at hb
  exact ⟨⟨a, Ideal.Quotient.eq_zero_iff_mem.mp hb⟩, rfl⟩

private theorem congruenceIdealReduction_ker {n m : ℕ+} (h : n ≤ m) :
    LinearMap.ker (congruenceIdealReduction R h) =
      Submodule.comap (𝔪 ^ (n : ℕ) : Ideal R).subtype (𝔪 ^ (m : ℕ) : Ideal R) := by
  ext a
  rw [LinearMap.mem_ker, Submodule.mem_comap]
  change (congruenceIdealReduction R h a = 0) ↔ (a : R) ∈ 𝔪 ^ (m : ℕ)
  rw [Subtype.ext_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The maximal-ideal-power quotient identified with the actual transition ideal. -/
def congruenceIdealQuotientEquiv {n m : ℕ+} (h : n ≤ m) :
    ((𝔪 ^ (n : ℕ) : Ideal R) ⧸
      Submodule.comap (𝔪 ^ (n : ℕ) : Ideal R).subtype (𝔪 ^ (m : ℕ) : Ideal R))
      ≃ₗ[R] congruenceTransitionIdeal R h :=
  (Submodule.quotEquivOfEq _ _ (congruenceIdealReduction_ker R h).symm).trans
    ((congruenceIdealReduction R h).quotKerEquivOfSurjective
      (congruenceIdealReduction_surjective R h))

@[simp] theorem congruenceIdealQuotientEquiv_mk {n m : ℕ+} (h : n ≤ m)
    (a : (𝔪 ^ (n : ℕ) : Ideal R)) :
    congruenceIdealQuotientEquiv R h (Submodule.Quotient.mk a) =
      congruenceIdealReduction R h a := rfl

private def congruenceTransitionQuotientEquiv {n m : ℕ+} (h : n ≤ m) :
    (congruenceRing R m ⧸ congruenceTransitionIdeal R h)
      ≃ₐ[CommRingCat.of R] congruenceRing R n :=
  Ideal.quotientKerAlgEquivOfSurjective (f := congruenceTransitionAlgHom R h)
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (show (n : ℕ) ≤ (m : ℕ) from h)))

end Coefficients

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)

local notation "𝔪" => IsLocalRing.maximalIdeal R

/-- Integral sections in the actual congruence kernel, identified with their generic image. -/
def congruenceSubgroupEquiv (n : ℕ+) :
    M.congruenceKernelAt n ≃* M.congruenceSubgroupAt n :=
  (M.congruenceKernelAt n).equivMapOfInjective M.integralPointMap M.integralPointMap_injective

@[simp] theorem congruenceSubgroupEquiv_val (n : ℕ+) (x : M.congruenceKernelAt n) :
    (M.congruenceSubgroupEquiv n x).val = M.integralPointMap x.val := rfl

/-- Under the affine point comparison, the transition kernel is the existing
ideal reduction kernel of the model. -/
theorem congruenceAffinePointsEquiv_mem_squareZeroKernel_iff {n m : ℕ+} (h : n ≤ m)
    (x : rationalPoints (M.congruenceFibre m)) :
    M.congruenceAffinePointsEquiv m x ∈
      Lie.SquareZero.kernel M.group (congruenceTransitionIdeal R h) ↔
      M.congruenceTransition h x = 1 := by
  let e := congruenceTransitionQuotientEquiv R h
  have he : e.toAlgHom.comp (Ideal.Quotient.mkₐ (CommRingCat.of R)
      (congruenceTransitionIdeal R h)) = congruenceTransitionAlgHom R h := by
    ext a
    exact Ideal.quotientKerAlgEquivOfSurjective_mk
      (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (show (n : ℕ) ≤ (m : ℕ) from h))) a
  have hinj : Function.Injective (Lie.affineMap M.group e.toAlgHom) := by
    intro a b hab
    exact Lie.affineMap_jointly_injective M.group e.toAlgHom e.toAlgHom
      (fun _ _ hab => e.injective (congrArg Prod.fst hab)) hab hab
  change Lie.SquareZero.reduction M.group (congruenceTransitionIdeal R h)
    (M.congruenceAffinePointsEquiv m x) = 1 ↔ _
  rw [← hinj.eq_iff, ← (M.congruenceAffinePointsEquiv n).injective.eq_iff,
    map_one, map_one, Lie.SquareZero.reduction, ← Lie.affineMap_comp, he,
    M.congruenceAffinePointsEquiv_transition]

/-- Reduce a level-`n` point to level `m`, landing in the Library's reduction kernel. -/
def congruenceReductionToKernel {n m : ℕ+} (h : n ≤ m) :
    M.congruenceSubgroupAt n →* Lie.SquareZero.kernel M.group (congruenceTransitionIdeal R h) :=
  (((M.congruenceAffinePointsEquiv m).toMonoidHom.comp (M.reductionAt m)).comp
      ((M.congruenceKernelAt n).subtype.comp (M.congruenceSubgroupEquiv n).symm.toMonoidHom)).codRestrict
    _ (fun g => by
      let x := (M.congruenceSubgroupEquiv n).symm g
      change M.congruenceAffinePointsEquiv m (M.reductionAt m x.val) ∈ _
      rw [M.congruenceAffinePointsEquiv_mem_squareZeroKernel_iff,
        M.congruenceTransition_reductionAt]
      exact x.property)

@[simp] theorem congruenceReductionToKernel_section {n m : ℕ+} (h : n ≤ m)
    (x : M.congruenceKernelAt n) :
    (M.congruenceReductionToKernel h (M.congruenceSubgroupEquiv n x)).val =
      M.congruenceAffinePointsEquiv m (M.reductionAt m x.val) := by
  change M.congruenceAffinePointsEquiv m (M.reductionAt m
    ((M.congruenceSubgroupEquiv n).symm (M.congruenceSubgroupEquiv n x)).val) = _
  rw [MulEquiv.symm_apply_apply]

/-- Level `m` inside the level-`n` rational congruence subgroup is normal. -/
instance congruenceSubgroupAt_normal_in_congruenceSubgroupAt (n m : ℕ+) :
    ((M.congruenceSubgroupAt m).subgroupOf (M.congruenceSubgroupAt n)).Normal := by
  let i := Subgroup.inclusion (M.congruenceSubgroupAt_le_integralPoints n)
  change (((M.congruenceSubgroupAt m).subgroupOf M.integralPoints).comap i).Normal
  infer_instance

variable [IsAffineHom G.X.hom]

/-- The actual Lie lattice multiplied by the `n`th maximal-ideal power. -/
abbrev lieLatticeAt (n : ℕ+) : Submodule R (GenericLie R G) :=
  (𝔪 ^ (n : ℕ) : Ideal R) • M.lieLattice

theorem lieLatticeAt_antitone : Antitone M.lieLatticeAt :=
  fun _ _ h => Submodule.smul_mono_left (Ideal.pow_le_pow_right (show (_ : ℕ) ≤ _ from h))

/-- The Lie-lattice quotient between positive levels. The denominator is viewed
inside the numerator by the inclusion of the latter into the generic Lie algebra. -/
abbrev congruenceLieQuotient (n m : ℕ+) :=
  M.lieLatticeAt n ⧸ (M.lieLatticeAt m).comap (M.lieLatticeAt n).subtype

section IdealTensor

omit [IsLocalRing R]

private def idealLieLatticeTensorMap (J : Ideal R) :
    J ⊗[R] M.LieModule →ₗ[R] GenericLie R G :=
  M.lieLattice.subtype.comp (M.lieLatticeEquiv.toLinearMap.comp
    ((TensorProduct.lid R M.LieModule).toLinearMap.comp (J.subtype.rTensor M.LieModule)))

private theorem idealLieLatticeTensorMap_tmul (J : Ideal R) (a : J) (X : M.LieModule) :
    M.idealLieLatticeTensorMap J (a ⊗ₜ[R] X) = (a : R) • M.lieMap X := by
  simp only [idealLieLatticeTensorMap, LinearMap.comp_apply, LinearMap.rTensor_tmul,
    Submodule.subtype_apply, LinearEquiv.coe_coe, TensorProduct.lid_tmul, LinearEquiv.map_smul,
    Submodule.coe_smul_of_tower]
  rfl

private theorem idealLieLatticeTensorMap_range (J : Ideal R) :
    LinearMap.range (M.idealLieLatticeTensorMap J) = J • M.lieLattice := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul a X =>
      rw [M.idealLieLatticeTensorMap_tmul]
      exact Submodule.smul_mem_smul a.property ⟨X, rfl⟩
    | add z w hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw
  · refine Submodule.smul_le.mpr (fun a ha Y hY => ?_)
    obtain ⟨X, rfl⟩ := hY
    exact ⟨(⟨a, ha⟩ : J) ⊗ₜ[R] X, M.idealLieLatticeTensorMap_tmul J _ X⟩

/-- Multiplication identifies the ideal tensor the smooth model Lie module with the
ideal times its image in the generic Lie algebra. Smoothness gives flatness of the Lie module. -/
def idealLieLatticeTensorEquiv (hM : M.IsSmooth) (J : Ideal R) :
    J ⊗[R] M.LieModule ≃ₗ[R] (J • M.lieLattice : Submodule R (GenericLie R G)) := by
  letI : Smooth M.group.X.hom := hM
  haveI : Module.Projective R M.LieModule := Lie.projective_lieKernel_of_smooth M.group
  have hJ := Module.Flat.rTensor_preserves_injective_linearMap (M := M.LieModule)
    J.subtype J.injective_subtype
  exact (LinearEquiv.ofInjective (M.idealLieLatticeTensorMap J)
    (M.lieLattice.injective_subtype.comp (M.lieLatticeEquiv.injective.comp
      ((TensorProduct.lid R M.LieModule).injective.comp hJ)))).trans
    (LinearEquiv.ofEq _ _ (M.idealLieLatticeTensorMap_range J))

@[simp] theorem idealLieLatticeTensorEquiv_tmul (hM : M.IsSmooth) (J : Ideal R) (a : J)
    (X : M.LieModule) :
    (M.idealLieLatticeTensorEquiv hM J (a ⊗ₜ[R] X)).val = (a : R) • M.lieMap X :=
  M.idealLieLatticeTensorMap_tmul J a X

private theorem idealLieLatticeTensorEquiv_map (hM : M.IsSmooth) {J I : Ideal R} (h : J ≤ I) :
    (LinearMap.range (TensorProduct.map (Submodule.comap I.subtype J).subtype
      (LinearMap.id : M.LieModule →ₗ[R] M.LieModule))).map
        (M.idealLieLatticeTensorEquiv hM I).toLinearMap =
      (J • M.lieLattice).comap (I • M.lieLattice).subtype := by
  have hJI : J • M.lieLattice ≤ I • M.lieLattice := Submodule.smul_mono_left h
  let e := TensorProduct.congr (Submodule.comapSubtypeEquivOfLe h)
    (LinearEquiv.refl R M.LieModule)
  have hcomp : (M.idealLieLatticeTensorEquiv hM I).toLinearMap.comp
        (TensorProduct.map (Submodule.comap I.subtype J).subtype (LinearMap.id : M.LieModule →ₗ[R] M.LieModule)) =
      (Submodule.inclusion hJI).comp (e.trans (M.idealLieLatticeTensorEquiv hM J)).toLinearMap := by
    apply TensorProduct.ext'
    intro a X
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearEquiv.trans_apply,
      Submodule.inclusion_apply, Subtype.coe_mk, e, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, M.idealLieLatticeTensorEquiv_tmul]
    rfl
  rw [← LinearMap.range_comp, hcomp, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, Submodule.range_inclusion]

end IdealTensor

/-- The actual coefficient ideal tensor the model Lie module identifies with the
quotient of the two Lie-lattice powers. -/
def congruenceLieTensorEquiv (hM : M.IsSmooth) {n m : ℕ+} (h : n ≤ m) :
    congruenceTransitionIdeal R h ⊗[R] M.LieModule ≃ₗ[R] M.congruenceLieQuotient n m :=
  (TensorProduct.congr (congruenceIdealQuotientEquiv R h).symm
    (LinearEquiv.refl R M.LieModule)).trans
    ((TensorProduct.quotientTensorEquiv M.LieModule _).trans
      (Submodule.Quotient.equiv _ _ (M.idealLieLatticeTensorEquiv hM (𝔪 ^ (n : ℕ)))
        (M.idealLieLatticeTensorEquiv_map hM
          (Ideal.pow_le_pow_right (show (n : ℕ) ≤ (m : ℕ) from h)))))

/-- The tensor comparison sends the reduced scalar tensored with a model tangent
vector to the class of their product in the generic Lie lattice. -/
theorem congruenceLieTensorEquiv_tmul (hM : M.IsSmooth) {n m : ℕ+} (h : n ≤ m)
    (a : (𝔪 ^ (n : ℕ) : Ideal R)) (X : M.LieModule) :
    M.congruenceLieTensorEquiv hM h (congruenceIdealReduction R h a ⊗ₜ[R] X) =
      Submodule.Quotient.mk ⟨(a : R) • M.lieMap X, Submodule.smul_mem_smul a.property ⟨X, rfl⟩⟩ := by
  have ha := (congruenceIdealQuotientEquiv R h).symm_apply_apply (Submodule.Quotient.mk a)
  rw [congruenceIdealQuotientEquiv_mk] at ha
  simp only [congruenceLieTensorEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    ha, LinearEquiv.refl_apply, TensorProduct.quotientTensorEquiv_apply_tmul_mk,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  exact congrArg Submodule.Quotient.mk
    (Subtype.ext (M.idealLieLatticeTensorEquiv_tmul hM _ a X))

/-- The congruence–Lie homomorphism of KP Proposition A.5.19(3) and Remark A.5.20,
prior to quotienting by the deeper subgroup. -/
def congruenceLieHom (hM : M.IsSmooth) {n m : ℕ+} (h : n ≤ m)
    (hm : (m : ℕ) ≤ 2 * (n : ℕ)) :
    M.congruenceSubgroupAt n →* Multiplicative (M.congruenceLieQuotient n m) :=
  haveI : Smooth M.group.X.hom := hM
  let e := Lie.SquareZero.kernelTensorAddEquiv M.group (congruenceTransitionIdeal R h)
    (congruenceTransitionAlgHom_ker_sq R h (by omega))
  ((e.trans (M.congruenceLieTensorEquiv hM h).toAddEquiv).toMultiplicativeRight.toMonoidHom).comp
    (M.congruenceReductionToKernel h)

/-- The deeper congruence subgroup is sent to the identity. -/
theorem congruenceLieHom_deeper_le_ker (hM : M.IsSmooth) {n m : ℕ+} (h : n ≤ m)
    (hm : (m : ℕ) ≤ 2 * (n : ℕ)) :
    (M.congruenceSubgroupAt m).subgroupOf (M.congruenceSubgroupAt n) ≤
      (M.congruenceLieHom hM h hm).ker := by
  intro g hg
  obtain ⟨x, hx, hxg⟩ := M.mem_congruenceSubgroupAt m g.val |>.mp hg
  let y : M.congruenceKernelAt n := ⟨x, M.congruenceKernelAt_antitone h hx⟩
  have hy : M.congruenceSubgroupEquiv n y = g := Subtype.ext hxg
  have hred : M.congruenceReductionToKernel h g = 1 := by
    apply Subtype.ext
    rw [← hy, M.congruenceReductionToKernel_section]
    change M.congruenceAffinePointsEquiv m (M.reductionAt m x) = 1
    rw [hx, map_one]
  change M.congruenceLieHom hM h hm g = 1
  rw [congruenceLieHom, MonoidHom.comp_apply, hred, map_one]

/-- The congruence–Lie homomorphism on the actual quotient `G_n/G_m`. -/
def congruenceLieQuotientHom (hM : M.IsSmooth) {n m : ℕ+} (h : n ≤ m)
    (hm : (m : ℕ) ≤ 2 * (n : ℕ)) :
    ((M.congruenceSubgroupAt n) ⧸ (M.congruenceSubgroupAt m).subgroupOf (M.congruenceSubgroupAt n)) →*
      Multiplicative (M.congruenceLieQuotient n m) :=
  QuotientGroup.lift _ (M.congruenceLieHom hM h hm) (M.congruenceLieHom_deeper_le_ker hM h hm)

@[simp] theorem congruenceLieQuotientHom_mk (hM : M.IsSmooth) {n m : ℕ+} (h : n ≤ m)
    (hm : (m : ℕ) ≤ 2 * (n : ℕ)) (g : M.congruenceSubgroupAt n) :
    M.congruenceLieQuotientHom hM h hm (QuotientGroup.mk g) = M.congruenceLieHom hM h hm g := rfl

end Langlands.GroupScheme.IntegralModel
