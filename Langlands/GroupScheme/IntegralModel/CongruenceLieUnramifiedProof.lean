import Langlands.GroupScheme.IntegralModel.CongruenceLieUnramified
import Langlands.GroupScheme.IntegralModel.CongruenceLieFunctorialityProof

/-! # The congruence–Lie homomorphism under local coefficient extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 120000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.IntegralModel

open GaloisPointComparison

section LocalExtension

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)
  (A B : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [Field B]
  [Algebra R A] [Algebra A B] [IsFractionRing A B]
  [Algebra K B] [Algebra R B] [IsScalarTower R A B] [IsScalarTower R K B]
  [IsLocalHom (algebraMap R A)]

omit [IsDomain R] [IsDomain A] in
/-- The local coefficient map on congruence rings, as a map of algebras over the
original base. -/
def congruenceRingAlgHom (m : ℕ+) :
    congruenceRing R m →ₐ[CommRingCat.of R] congruenceRing A m :=
  { congruenceRingMap (algebraMap R A) m with
    commutes' := fun _ => rfl }

omit [IsDomain R] [IsDomain A] in
@[simp] theorem congruenceRingAlgHom_apply (m : ℕ+) (c : congruenceRing R m) :
    congruenceRingAlgHom A m c = congruenceRingMap (algebraMap R A) m c := rfl

omit [IsDomain R] [IsDomain A] in
/-- The coefficient map carries the transition ideal into the transition ideal. -/
theorem congruenceRingAlgHom_mem {n m : ℕ+} (h : n ≤ m) {c : congruenceRing R m}
    (hc : c ∈ congruenceTransitionIdeal R h) :
    congruenceRingAlgHom A m c ∈ congruenceTransitionIdeal A h := by
  rw [RingHom.mem_ker] at hc ⊢
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hc' : congruenceRingMap (algebraMap R A) n
      (congruenceTransitionAlgHom R h (Ideal.Quotient.mk _ r)) = 0 := by
    rw [hc, map_zero]
  exact hc'

omit [IsDomain R] [IsDomain A] in
theorem algebraMap_mem_maximalIdeal_pow (n : ℕ) {a : R}
    (ha : a ∈ IsLocalRing.maximalIdeal R ^ n) :
    algebraMap R A a ∈ IsLocalRing.maximalIdeal A ^ n := by
  have hle : (IsLocalRing.maximalIdeal R ^ n).map (algebraMap R A) ≤
      IsLocalRing.maximalIdeal A ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le _) _
  exact hle (Ideal.mem_map_of_mem _ ha)

omit [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)] in
/-- The pullback comparison of coefficient points commutes with coefficient maps,
stated for the group of the base-changed model. -/
theorem affineBaseChangeEquiv_baseChange_naturality {C D : Type u} [CommRing C] [CommRing D]
    [Algebra A C] [Algebra A D] [Algebra R C] [Algebra R D]
    [IsScalarTower R A C] [IsScalarTower R A D]
    (f : C →ₐ[CommRingCat.of A] D) (x : Lie.AffinePoints (M.baseChange A B).group C) :
    Lie.affineBaseChangeEquiv R A M.group D (Lie.affineMap (M.baseChange A B).group f x) =
      Lie.affineMap M.group (f.restrictScalars (CommRingCat.of R))
        (Lie.affineBaseChangeEquiv R A M.group C x) :=
  Lie.affineBaseChangeEquiv_naturality R A M.group f x

/-- Extension of square-zero reduction-kernel points along the local coefficient
map, landing in the kernel of the base-changed model. -/
def congruenceKernelExtend {n m : ℕ+} (h : n ≤ m) :
    Lie.SquareZero.kernel M.group (congruenceTransitionIdeal R h) →*
      Lie.SquareZero.kernel (M.baseChange A B).group (congruenceTransitionIdeal A h) :=
  (((Lie.affineBaseChangeEquiv R A M.group (congruenceRing A m)).symm.toMonoidHom.comp
      (Lie.affineMap M.group (congruenceRingAlgHom A m))).comp
      (Lie.SquareZero.kernel M.group (congruenceTransitionIdeal R h)).subtype).codRestrict _
    (fun p => by
      rw [MonoidHom.mem_ker]
      apply (Lie.affineBaseChangeEquiv R A M.group
        (congruenceRing A m ⧸ congruenceTransitionIdeal A h)).injective
      rw [map_one]
      change Lie.affineBaseChangeEquiv R A M.group _ (Lie.affineMap _ _
        ((Lie.affineBaseChangeEquiv R A M.group (congruenceRing A m)).symm
          (Lie.affineMap M.group (congruenceRingAlgHom A m) p.val))) = 1
      rw [Lie.affineBaseChangeEquiv_naturality, MulEquiv.apply_symm_apply,
        ← Lie.affineMap_comp]
      have hf : ((Ideal.Quotient.mkₐ (CommRingCat.of A)
          (congruenceTransitionIdeal A h)).restrictScalars (CommRingCat.of R)).comp
            (congruenceRingAlgHom A m) =
          (Ideal.quotientMapₐ (congruenceTransitionIdeal A h) (congruenceRingAlgHom A m)
            (fun _ hc => congruenceRingAlgHom_mem A h hc)).comp
            (Ideal.Quotient.mkₐ (CommRingCat.of R) (congruenceTransitionIdeal R h)) := by
        apply AlgHom.ext
        intro c
        rfl
      rw [hf, Lie.affineMap_comp]
      change Lie.affineMap _ _ (Lie.SquareZero.reduction M.group _ p.val) = 1
      rw [MonoidHom.mem_ker.mp p.property, map_one])

@[simp] theorem congruenceKernelExtend_val {n m : ℕ+} (h : n ≤ m)
    (p : Lie.SquareZero.kernel M.group (congruenceTransitionIdeal R h)) :
    (M.congruenceKernelExtend A B h p).val =
      (Lie.affineBaseChangeEquiv R A M.group (congruenceRing A m)).symm
        (Lie.affineMap M.group (congruenceRingAlgHom A m) p.val) := rfl

/-- Extension of kernel points carries tangent evaluation at an ideal element to
tangent evaluation at its image, on the extended Lie vector. -/
theorem congruenceKernelExtend_tangentPoint {n m : ℕ+} (h : n ≤ m)
    (hI : congruenceTransitionIdeal R h ^ 2 = ⊥) (hJ : congruenceTransitionIdeal A h ^ 2 = ⊥)
    (i : congruenceTransitionIdeal R h) (X : M.LieModule) :
    M.congruenceKernelExtend A B h (Lie.SquareZero.tangentPoint M.group _ hI i
        (lieKernelMap M.group (Algebra.ofId (CommRingCat.of R) (congruenceRing R m)) X.toMul)) =
      Lie.SquareZero.tangentPoint (M.baseChange A B).group _ hJ
        ⟨congruenceRingAlgHom (R := R) A m i, congruenceRingAlgHom_mem (R := R) A h i.property⟩
        (lieKernelMap (M.baseChange A B).group
          (Algebra.ofId (CommRingCat.of A) (congruenceRing A m))
          (M.lieModuleBaseChange (A := A) (B := B) X).toMul) := by
  apply Subtype.ext
  apply (Lie.affineBaseChangeEquiv R A M.group (congruenceRing A m)).injective
  rw [congruenceKernelExtend_val, MulEquiv.apply_symm_apply, Lie.SquareZero.tangentPoint_val,
    Lie.SquareZero.tangentPoint_val, lieKernelMap_val, lieKernelMap_val,
    affineBaseChangeEquiv_baseChange_naturality, affineBaseChangeEquiv_baseChange_naturality]
  have hX : Lie.affineBaseChangeEquiv R A M.group (DualNumber A)
      (M.lieModuleBaseChange (A := A) (B := B) X).toMul.val =
      Lie.affineMap M.group (GeneralLinear.DualNumber.coefficientAlgMap
        (Algebra.ofId (CommRingCat.of R) A)) X.toMul.val := by
    change Lie.affineBaseChangeEquiv R A M.group (DualNumber A)
      ((Lie.affineBaseChangeEquiv R A M.group (DualNumber A)).symm _) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [hX, ← Lie.affineMap_comp, ← Lie.affineMap_comp, ← Lie.affineMap_comp,
    ← Lie.affineMap_comp]
  congr 2
  apply AlgHom.ext
  intro z
  change congruenceRingAlgHom A m
      (Lie.SquareZero.tangentEvaluation (R := CommRingCat.of R) _ hI i
        (GeneralLinear.DualNumber.coefficientAlgMap _ z)) =
    Lie.SquareZero.tangentEvaluation (R := CommRingCat.of A) _ hJ _
      (GeneralLinear.DualNumber.coefficientAlgMap _
        (GeneralLinear.DualNumber.coefficientAlgMap _ z))
  rw [Lie.SquareZero.tangentEvaluation_apply, Lie.SquareZero.tangentEvaluation_apply]
  change congruenceRingAlgHom A m (algebraMap R (congruenceRing R m) z.fst +
      algebraMap R (congruenceRing R m) z.snd * (i : congruenceRing R m)) =
    algebraMap A (congruenceRing A m) (algebraMap R A z.fst) +
      algebraMap A (congruenceRing A m) (algebraMap R A z.snd) *
        congruenceRingAlgHom A m (i : congruenceRing R m)
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

/-- Local coefficient extension commutes with the reduction of level-`n` points to
the transition kernel. -/
theorem congruenceReductionToKernel_extend {n m : ℕ+} (h : n ≤ m)
    (g : M.congruenceSubgroupAt n) :
    (M.baseChange A B).congruenceReductionToKernel h (M.congruenceSubgroupExtend A B n g) =
      M.congruenceKernelExtend A B h (M.congruenceReductionToKernel h g) := by
  obtain ⟨x, rfl⟩ := (M.congruenceSubgroupEquiv n).surjective g
  have hx : M.congruenceSubgroupExtend A B n (M.congruenceSubgroupEquiv n x) =
      (M.baseChange A B).congruenceSubgroupEquiv n
        ⟨baseChangeSectionHom (Spec.algebraMap R A) M.group x.val,
          M.baseChange_mem_congruenceKernelAt A B n x.property⟩ := by
    apply Subtype.ext
    rw [congruenceSubgroupExtend_val, congruenceSubgroupEquiv_val, congruenceSubgroupEquiv_val,
      M.baseChange_integralPointMap A B, ← rationalExtend_hom_eq_baseChangeSectionHom]
  apply Subtype.ext
  rw [hx, congruenceReductionToKernel_section, congruenceKernelExtend_val,
    congruenceReductionToKernel_section]
  apply (Lie.affineBaseChangeEquiv R A M.group (congruenceRing A m)).injective
  rw [MulEquiv.apply_symm_apply]
  apply Over.OverMorphism.ext
  rw [Lie.affineBaseChangeEquiv_left, Lie.affineMap_apply, Over.comp_left]
  change ((baseChangeBasePointsEquiv (congruenceBaseMap A m) _
      ((M.baseChange A B).reductionAt m _)).left ≫ _) =
    _ ≫ (baseChangeBasePointsEquiv (congruenceBaseMap R m) M.group (M.reductionAt m x.val)).left
  rw [baseChangeBasePointsEquiv_left, baseChangeBasePointsEquiv_left]
  change ((baseChangeSectionHom (congruenceBaseMap A m)
      ((GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group)
      (baseChangeSectionHom (Spec.algebraMap R A) M.group x.val)).left ≫
        pullback.fst ((GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group).X.hom
          (congruenceBaseMap A m)) ≫ pullback.fst M.group.X.hom (Spec.algebraMap R A) =
    _ ≫ ((baseChangeSectionHom (congruenceBaseMap R m) M.group x.val).left ≫
      pullback.fst M.group.X.hom (congruenceBaseMap R m))
  rw [baseChangeSectionHom_fst, baseChangeSectionHom_fst, Category.assoc,
    baseChangeSectionHom_fst, ← Category.assoc, ← Category.assoc]
  congr 1
  change _ = Spec.map (CommRingCat.ofHom (congruenceRingAlgHom A m).toRingHom) ≫ _
  simp only [congruenceBaseMap, Spec.algebraMap, ← Spec.map_comp]
  congr 1

variable [IsAffineHom G.X.hom]

local instance congruenceLieBaseChangeAffineHom :
    IsAffineHom ((GroupScheme.baseChange (Spec.algebraMap K B)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (Spec.algebraMap K B))
  infer_instance

/-- Under the ideal–Lie tensor comparisons, extension of reduction-kernel points
along the local coefficient map is the generic tangent extension on Lie-lattice
quotients. -/
theorem congruenceLieTensorEquiv_extend (hM : M.IsSmooth) {n m : ℕ+} (h : n ≤ m)
    (hI : congruenceTransitionIdeal R h ^ 2 = ⊥) (hJ : congruenceTransitionIdeal A h ^ 2 = ⊥)
    [Smooth M.group.X.hom] [Smooth (M.baseChange A B).group.X.hom]
    (z : congruenceTransitionIdeal R h ⊗[R] M.LieModule) :
    ((Lie.SquareZero.kernelTensorAddEquiv (M.baseChange A B).group _ hJ).trans
        ((M.baseChange A B).congruenceLieTensorEquiv (M.isSmooth_baseChange A B hM) h).toAddEquiv)
        (Additive.ofMul (M.congruenceKernelExtend A B h
          ((Lie.SquareZero.kernelTensorAddEquiv M.group _ hI).symm z).toMul)) =
      M.lieLatticeQuotientMap (M.baseChange A B) (GenericLie.baseChange R A G)
        (fun _ hX => M.baseChange_mem_lieLattice hX)
        (IsLocalRing.map_maximalIdeal_le _) n m (M.congruenceLieTensorEquiv hM h z) := by
  induction z using TensorProduct.inductionOn with
  | tmul i X =>
    obtain ⟨a, rfl⟩ := congruenceIdealReduction_surjective R h i
    show (M.baseChange A B).congruenceLieTensorEquiv (M.isSmooth_baseChange A B hM) h
      (Lie.SquareZero.kernelTensorAddEquiv (M.baseChange A B).group _ hJ _) = _
    rw [Lie.SquareZero.kernelTensorAddEquiv_symm_tmul, toMul_ofMul,
      congruenceKernelExtend_tangentPoint M A B h hI hJ,
      ← toMul_ofMul (Lie.SquareZero.tangentPoint _ _ _ _ _),
      ← Lie.SquareZero.kernelTensorAddEquiv_symm_tmul, ofMul_toMul, AddEquiv.apply_symm_apply]
    have hred : (⟨congruenceRingAlgHom (R := R) A m (congruenceIdealReduction R h a),
        congruenceRingAlgHom_mem (R := R) A h (congruenceIdealReduction R h a).property⟩ :
          congruenceTransitionIdeal A h) =
        congruenceIdealReduction A h ⟨algebraMap R A a,
          algebraMap_mem_maximalIdeal_pow A _ a.property⟩ := Subtype.ext rfl
    rw [hred, congruenceLieTensorEquiv_tmul, congruenceLieTensorEquiv_tmul]
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    change algebraMap R A (a : R) • (M.baseChange A B).lieMap
        (M.lieModuleBaseChange (A := A) (B := B) X) =
      GenericLie.baseChange R A G ((a : R) • M.lieMap X)
    rw [M.lieMap_baseChange, LinearMap.map_smulₛₗ]
  | add z w hz hw =>
    rw [(Lie.SquareZero.kernelTensorAddEquiv M.group _ hI).symm.map_add, toMul_add,
      (M.congruenceKernelExtend A B h).map_mul, ofMul_mul, AddEquiv.map_add]
    exact (congrArg₂ (· + ·) hz hw).trans
      (((M.lieLatticeQuotientMap (M.baseChange A B) (GenericLie.baseChange R A G)
        (fun _ hX => M.baseChange_mem_lieLattice hX)
        (IsLocalRing.map_maximalIdeal_le _) n m).map_add _ _).symm.trans
        (congrArg _ ((M.congruenceLieTensorEquiv hM h).map_add z w).symm))

/-- The congruence–Lie homomorphism commutes with local coefficient extension:
on congruence subgroups by generic base change, and on Lie-lattice quotients by
the generic tangent extension. -/
theorem congruenceLieHom_baseChange (hM : M.IsSmooth) {n m : ℕ+} (h : n ≤ m)
    (hm : (m : ℕ) ≤ 2 * (n : ℕ)) :
    ((M.baseChange A B).congruenceLieHom (M.isSmooth_baseChange A B hM) h hm).comp
        (M.congruenceSubgroupExtend A B n) =
      ((M.lieLatticeQuotientMap (M.baseChange A B) (GenericLie.baseChange R A G)
        (fun _ hX => M.baseChange_mem_lieLattice hX)
        (IsLocalRing.map_maximalIdeal_le _) n m).toAddMonoidHom.toMultiplicative).comp
        (M.congruenceLieHom hM h hm) := by
  have : Smooth M.group.X.hom := hM
  have : Smooth (M.baseChange A B).group.X.hom := M.isSmooth_baseChange A B hM
  have hI := congruenceTransitionAlgHom_ker_sq R h (by omega)
  have hJ := congruenceTransitionAlgHom_ker_sq A h (by omega)
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, congruenceLieHom_apply,
    congruenceLieHom_apply, congruenceReductionToKernel_extend]
  set r := M.congruenceReductionToKernel h g
  obtain ⟨z, hz⟩ := (Lie.SquareZero.kernelTensorAddEquiv M.group
    (congruenceTransitionIdeal R h) hI).symm.surjective (Additive.ofMul r)
  have hr : r = ((Lie.SquareZero.kernelTensorAddEquiv M.group
      (congruenceTransitionIdeal R h) hI).symm z).toMul := by rw [hz]; rfl
  rw [hr, ofMul_toMul, AddEquiv.apply_symm_apply]
  exact congrArg Multiplicative.ofAdd (M.congruenceLieTensorEquiv_extend A B hM h hI hJ z)

end LocalExtension

section MaximalUnramified

open Langlands.LocalGalois.Separable

attribute [local instance] congruenceLieFixedFieldIntegerAlgebra
  congruenceLieFixedFieldScalarTower congruenceLieFixedFieldLocalHom
  congruenceLieBaseChangedAffineHom

/-- **KP Proposition A.5.19(3), compatibility with maximal unramified extension.** -/
theorem congruenceLieUnramifiedCompatibility :
    CongruenceLieUnramifiedCompatibilityStatement.{u} := by
  intro F _ _ _ _ G _ M hM n m h hm
  exact M.congruenceLieHom_baseChange (fixedFieldIntegers F) (inertiaFixedField F) hM h hm

end MaximalUnramified

end Langlands.GroupScheme.IntegralModel
