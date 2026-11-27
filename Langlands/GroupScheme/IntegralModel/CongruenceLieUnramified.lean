import Langlands.GroupScheme.IntegralModel.CongruenceLieStatements
import Langlands.GroupScheme.IntegralModel.LieLatticeBaseChange
import Langlands.GroupScheme.IntegralModel.CongruenceBaseChange

/-! # The congruence–Lie homomorphism under maximal unramified extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 650000
set_option synthInstance.maxHeartbeats 120000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.GroupScheme.IntegralModel

open GaloisPointComparison

section CoefficientQuotients

variable {R A : Type u} [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]

/-- A local coefficient map descends to each of the actual congruence rings. -/
def congruenceRingMap (f : R →+* A) [IsLocalHom f] (n : ℕ+) :
    congruenceRing R n →+* congruenceRing A n :=
  Ideal.quotientMap _ f (Ideal.map_le_iff_le_comap.mp (by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le f) _))

@[simp] theorem congruenceRingMap_quotient (f : R →+* A) [IsLocalHom f] (n : ℕ+) (r : R) :
    congruenceRingMap f n (congruenceQuotient R n r) = congruenceQuotient A n (f r) := rfl

end CoefficientQuotients

section LocalExtension

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)
  (A B : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [Field B]
  [Algebra R A] [Algebra A B] [IsFractionRing A B]
  [Algebra K B] [Algebra R B] [IsScalarTower R A B] [IsScalarTower R K B]
  [IsLocalHom (algebraMap R A)]

/-- Extension of an integral section along a local coefficient map preserves
its congruence to the unit at each positive level. -/
theorem baseChange_mem_congruenceKernelAt (n : ℕ+) {x : M.integralSections}
    (hx : x ∈ M.congruenceKernelAt n) :
    baseChangeSectionHom (Spec.algebraMap R A) M.group x ∈
      (M.baseChange A B).congruenceKernelAt n := by
  have hs : congruenceBaseMap A n ≫ Spec.algebraMap R A =
      Spec.map (CommRingCat.ofHom (congruenceRingMap (algebraMap R A) n)) ≫
        congruenceBaseMap R n := by
    simp only [congruenceBaseMap, Spec.algebraMap, ← Spec.map_comp]
    rfl
  have hx' : congruenceBaseMap R n ≫ x.left =
      congruenceBaseMap R n ≫ (1 : M.integralSections).left := by
    apply (baseChangeSectionHom_eq_iff (congruenceBaseMap R n) M.group x 1).mp
    exact hx.trans (map_one (M.reductionAt n)).symm
  change baseChangeSectionHom (congruenceBaseMap A n) _
    (baseChangeSectionHom (Spec.algebraMap R A) M.group x) = 1
  rw [← map_one (baseChangeSectionHom (congruenceBaseMap A n) _),
    ← map_one (baseChangeSectionHom (Spec.algebraMap R A) M.group),
    baseChangeSectionHom_eq_iff]
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeSectionHom_fst]
    rw [← Category.assoc, hs, Category.assoc, hx', ← Category.assoc, ← hs, Category.assoc]
  · simp only [baseChangeSectionHom_left, Category.assoc, pullback.lift_snd]

/-- The actual generic field extension restricted to the positive congruence subgroups. -/
def congruenceSubgroupExtend (n : ℕ+) :
    M.congruenceSubgroupAt n →* (M.baseChange A B).congruenceSubgroupAt n :=
  ((rationalExtend K B G).comp (M.congruenceSubgroupAt n).subtype).codRestrict _ (fun g => by
    obtain ⟨x, hx, hxg⟩ := g.property
    refine ⟨baseChangeSectionHom (Spec.algebraMap R A) M.group x,
      M.baseChange_mem_congruenceKernelAt A B n hx, ?_⟩
    rw [M.baseChange_integralPointMap A B, ← rationalExtend_hom_eq_baseChangeSectionHom, hxg]
    rfl)

@[simp] theorem congruenceSubgroupExtend_val (n : ℕ+) (g : M.congruenceSubgroupAt n) :
    (M.congruenceSubgroupExtend A B n g).val = rationalExtend K B G g.val := rfl

end LocalExtension

section MaximalUnramified

open Langlands.LocalGalois.Separable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} (M : IntegralModel ↥𝒪[F] F G)

local notation "K" => inertiaFixedField F
local notation "A" => fixedFieldIntegers F

local instance congruenceLieFixedFieldIntegerAlgebra : Algebra ↥𝒪[F] A :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance congruenceLieFixedFieldScalarTower : IsScalarTower ↥𝒪[F] A K :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance congruenceLieFixedFieldLocalHom : IsLocalHom (algebraMap ↥𝒪[F] A) := integerToFixedField_isLocalHom F

/-- Extension to the separable inertia fixed field on the actual congruence subgroups. -/
def unramifiedCongruenceSubgroupExtend (n : ℕ+) :
    M.congruenceSubgroupAt n →* M.baseChangeUnramified.congruenceSubgroupAt n :=
  M.congruenceSubgroupExtend A K n

variable [IsAffineHom G.X.hom]

local instance congruenceLieBaseChangedAffineHom : IsAffineHom (baseChanged F K G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (baseMap F K))
  infer_instance

/-- The actual generic tangent extension on the Lie-lattice power quotients
for the maximal unramified extension. -/
def unramifiedCongruenceLieQuotientMap (n m : ℕ+) :
    M.congruenceLieQuotient n m →ₛₗ[algebraMap ↥𝒪[F] A]
      M.baseChangeUnramified.congruenceLieQuotient n m :=
  M.lieLatticeQuotientMap M.baseChangeUnramified (GenericLie.baseChange ↥𝒪[F] A G)
    (fun _ hX => M.baseChange_mem_lieLattice hX)
    (IsLocalRing.map_maximalIdeal_le _) n m

/-- KP A.5.19(3), compatibility of the canonical congruence–Lie homomorphism
with extension to the separable inertia fixed field. -/
def CongruenceLieUnramifiedCompatibilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (M : IntegralModel ↥𝒪[F] F G) (hM : M.IsSmooth) (n m : ℕ+) (h : n ≤ m)
    (hm : (m : ℕ) ≤ 2 * (n : ℕ)),
    (M.baseChangeUnramified.congruenceLieHom
      (M.isSmooth_baseChange (fixedFieldIntegers F) (inertiaFixedField F) hM) h hm).comp
        (M.unramifiedCongruenceSubgroupExtend n) =
      ((M.unramifiedCongruenceLieQuotientMap n m).toAddMonoidHom.toMultiplicative).comp
        (M.congruenceLieHom hM h hm)

end MaximalUnramified

end Langlands.GroupScheme.IntegralModel
