import Langlands.Geometry.Building.Kottwitz.InducedCocharacterBasis
import Langlands.Geometry.Building.Kottwitz.TorusKottwitzLaw
import Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelReduction
import Langlands.Geometry.Building.Kottwitz.TorusMapProof
import Langlands.Geometry.Building.Kottwitz.PermutationCoinvariants

/-! # The norm law on rational points built from a permuted cocharacter basis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.TorusPointsTensorGalois

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.Kottwitz

namespace InducedCocharacterBasis

section Generic

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
  {Λ : Type u} (s : Finset Λ)

omit [IsAffine T.X.left] in
/-- Extension of coefficients of a finite sum of pure cocharacter evaluations. -/
theorem relativeExtend_coefficientEvaluation_sum (x : Λ → Additive Lˣ)
    (ν : Λ → cocharacterLattice (baseChanged k L T)) :
    GaloisPoint.relativeExtend k L M T.toGrp
        (coefficientEvaluation k L T (∑ i ∈ s, x i ⊗ₜ[ULift.{u} ℤ] ν i)).toMul =
      (coefficientEvaluation k M T
        (∑ i ∈ s, Additive.ofMul (Units.map (algebraMap L M).toMonoidHom (x i).toMul) ⊗ₜ[ULift.{u} ℤ]
          extendGeometricCocharacters k L M T (ν i))).toMul := by
  apply Additive.ofMul.injective
  change (GaloisPoint.relativeExtend k L M T.toGrp).toAdditive
      (coefficientEvaluation k L T (∑ i ∈ s, x i ⊗ₜ[ULift.{u} ℤ] ν i)) =
    coefficientEvaluation k M T
      (∑ i ∈ s, Additive.ofMul (Units.map (algebraMap L M).toMonoidHom (x i).toMul) ⊗ₜ[ULift.{u} ℤ]
        extendGeometricCocharacters k L M T (ν i))
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg Additive.ofMul (relativeExtend_coefficientEvaluation_tmul k L M T (x i) (ν i))

end Generic

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E] [IsGalois F E]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine T.X.left]
  (hE : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap F E)).obj T).toGrp)
  {J : Type u} [Fintype J] [DecidableEq J]
  (b : Module.Basis J ℤ
    (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F E)).obj T)))
  (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  (hL : IsSplitTorus ((CommGroupScheme.baseChange (baseMap F L)).obj T).toGrp)
  (hEL : ∀ x ∈ E, x ∈ L)

/-- The inclusion of `E` into `L` inside `F^sep`, as a monoid map. -/
def inclusionHom : E →* L where
  toFun x := ⟨(x : SeparableClosure F), hEL x x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [FiniteDimensional F E] [IsGalois F E] in
theorem coe_inclusionHom (x : E) :
    ((inclusionHom F E L hEL x : L) : SeparableClosure F) = (x : SeparableClosure F) := rfl

/-- The geometric basis vectors, as cocharacters of `T_L`. -/
def splitBasis (j : J) : cocharacterLattice ((CommGroupScheme.baseChange (baseMap F L)).obj T) :=
  (AddEquiv.ofBijective (extendGeometricCocharacters F L (SeparableClosure F) T)
    (extendGeometricCocharacters_bijective F L (SeparableClosure F) T hL)).symm
      (geometricBasis F E T hE b j)

omit [FiniteDimensional F E] [IsGalois F E] [IsAffine T.X.left] in
theorem extendGeometricCocharacters_splitBasis (j : J) :
    extendGeometricCocharacters F L (SeparableClosure F) T (splitBasis F E T hE b L hL j) =
      geometricBasis F E T hE b j :=
  (AddEquiv.ofBijective (extendGeometricCocharacters F L (SeparableClosure F) T)
    (extendGeometricCocharacters_bijective F L (SeparableClosure F) T hL)).apply_symm_apply _

omit [FiniteDimensional F E] [IsGalois F E] in
/-- The extension of a rational point with a cocharacter expansion over `E` has the
corresponding expansion over `L`. -/
theorem extend_eq_of_extend_eq (x : J → Eˣ) (x0 : affinePoints T.toGrp (CommAlgCat.of F F))
    (hx0 : GaloisPoint.extend F E T.toGrp x0 =
      (coefficientEvaluation F E T
        (∑ j, Additive.ofMul (x j) ⊗ₜ[ULift.{u} ℤ] dualBasis T hE b j)).toMul) :
    GaloisPoint.extend F L T.toGrp x0 =
      (coefficientEvaluation F L T
        (∑ j, Additive.ofMul (Units.map (inclusionHom F E L hEL) (x j)) ⊗ₜ[ULift.{u} ℤ]
          splitBasis F E T hE b L hL j)).toMul := by
  apply GaloisPoint.relativeExtend_injective F L (SeparableClosure F) T.toGrp
  rw [GaloisPoint.relativeExtend_extend,
    ← GaloisPoint.relativeExtend_extend F E (SeparableClosure F), hx0,
    relativeExtend_coefficientEvaluation_sum, relativeExtend_coefficientEvaluation_sum]
  have hu : ∀ j, Units.map (algebraMap L (SeparableClosure F)).toMonoidHom
      (Units.map (inclusionHom F E L hEL) (x j)) =
      Units.map (algebraMap E (SeparableClosure F)).toMonoidHom (x j) :=
    fun j => Units.ext rfl
  simp only [toMul_ofMul, hu, extendGeometricCocharacters_splitBasis, geometricBasis_apply]

variable [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]

omit [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L] in
omit [IsAffine T.X.left] [DecidableEq J] in
/-- The norm-square value of a finite sum of pure cocharacter evaluations. -/
theorem normLawValue_sum (w : J → Lˣ)
    (ν : J → cocharacterLattice ((CommGroupScheme.baseChange (baseMap F L)).obj T)) :
    normLawValue F F T L hL (coefficientEvaluation F L T
        (∑ j, Additive.ofMul (w j) ⊗ₜ[ULift.{u} ℤ] ν j)) =
      inertiaProjection F (UnramifiedClosure F) (SeparableClosure F)
        (cocharacterLattice.galoisRepresentation F (SeparableClosure F) T)
        (∑ j, (IntegerValuation.orderUnits (normalizedIntermediateValuation F L) (w j)).toAdd •
          extendGeometricCocharacters F L (SeparableClosure F) T (ν j)) := by
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [normLawValue_tmul, map_zsmul, map_zsmul, toMul_ofMul, map_zsmul]

include hL in
omit [FiniteDimensional F E] [IsGalois F E] in
/-- The norm law computes a multiple of the Kottwitz value of a rational point whose
extension to `E` is a cocharacter expansion. -/
theorem card_smul_torusKottwitz (hT : IsTorus T.toGrp) (x : J → Eˣ)
    (x0 : affinePoints T.toGrp (CommAlgCat.of F F))
    (hx0 : GaloisPoint.extend F E T.toGrp x0 =
      (coefficientEvaluation F E T
        (∑ j, Additive.ofMul (x j) ⊗ₜ[ULift.{u} ℤ] dualBasis T hE b j)).toMul) :
    Fintype.card (L ≃ₐ[UnramifiedClosure F] L) •
        (torusKottwitz F F T hT (GaloisPoint.extend F (UnramifiedClosure F) T.toGrp x0)).toAdd =
      inertiaProjection F (UnramifiedClosure F) (SeparableClosure F)
        (cocharacterLattice.galoisRepresentation F (SeparableClosure F) T)
        (∑ j, (IntegerValuation.orderUnits (normalizedIntermediateValuation F L)
            (Units.map (inclusionHom F E L hEL) (x j))).toAdd •
          geometricBasis F E T hE b j) := by
  have hspec := (torusKottwitzExistence F F T hT).2.1 L hL
  have h := (torusNormLawAt_iff F F T L hL _).mp hspec
    (GaloisPoint.relativeExtend F (UnramifiedClosure F) L T.toGrp
      (GaloisPoint.extend F (UnramifiedClosure F) T.toGrp x0))
  rw [relativeNorm_relativeExtend, map_pow, GaloisPoint.relativeExtend_extend,
    extend_eq_of_extend_eq F E T hE b L hL hEL x x0 hx0, ofMul_toMul,
    normLawValue_sum] at h
  have h' := congrArg Multiplicative.toAdd h
  rw [toAdd_pow, toAdd_ofAdd] at h'
  rw [h']
  simp only [extendGeometricCocharacters_splitBasis]

omit [FiniteDimensional F E] [IsGalois F E] [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L] in
/-- The integer order of an integral power of a unit of `E`, viewed in `L`. -/
theorem orderUnits_inclusionHom_zpow (w : Eˣ) (m : ℤ) :
    (IntegerValuation.orderUnits (normalizedIntermediateValuation F L)
      (Units.map (inclusionHom F E L hEL) (w ^ m))).toAdd =
      m * (IntegerValuation.orderUnits (normalizedIntermediateValuation F L)
        (Units.map (inclusionHom F E L hEL) w)).toAdd := by
  rw [map_zpow, map_zpow, toAdd_zpow, smul_eq_mul]

section Orbit

variable (hb : ∀ (σ : E ≃ₐ[F] E) (i : J), ∃ j,
    characterLattice.galoisRepresentation F E T σ (b i) = b j)
  [MulAction (SeparableClosure F ≃ₐ[F] SeparableClosure F) J]
  (hact : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (j : J),
    σ • j = indexHom T b hb (σ.restrictNormal E) j)

include hact in
omit [FiniteDimensional F E] in
/-- The geometric basis is permuted through the action on indices. -/
theorem galoisRepresentation_geometricBasis_smul
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (j : J) :
    cocharacterLattice.galoisRepresentation F (SeparableClosure F) T σ
        (geometricBasis F E T hE b j) = geometricBasis F E T hE b (σ • j) := by
  rw [hact]
  exact galoisRepresentation_geometricBasis F E T hE b hb σ j

include hact in
omit [FiniteDimensional F E] in
/-- The norm-law value of the constructed point is `[L : K]` times the target class. -/
theorem mk_sum_eq_card_smul (u : J → Eˣ)
    (hsum : ∀ j, PermutationCoinvariants.orbitFunSum
      (relativeInertia F (UnramifiedClosure F) (SeparableClosure F))
      (fun i => (IntegerValuation.orderUnits (normalizedIntermediateValuation F L)
        (Units.map (inclusionHom F E L hEL) (u i))).toAdd) j =
      Module.finrank (UnramifiedClosure F) L)
    (ν : geometricCocharacters F (SeparableClosure F) T)
    (hn : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (j : J),
      PermutationCoinvariants.orbitSum (geometricBasis F E T hE b)
          (relativeInertia F (UnramifiedClosure F) (SeparableClosure F)) ν (σ • j) =
        PermutationCoinvariants.orbitSum (geometricBasis F E T hE b)
          (relativeInertia F (UnramifiedClosure F) (SeparableClosure F)) ν j) :
    inertiaProjection F (UnramifiedClosure F) (SeparableClosure F)
        (cocharacterLattice.galoisRepresentation F (SeparableClosure F) T)
        (∑ j, (IntegerValuation.orderUnits (normalizedIntermediateValuation F L)
          (Units.map (inclusionHom F E L hEL)
            (u j ^ PermutationCoinvariants.orbitSum (geometricBasis F E T hE b)
              (relativeInertia F (UnramifiedClosure F) (SeparableClosure F)) ν j))).toAdd •
          geometricBasis F E T hE b j) =
      inertiaProjection F (UnramifiedClosure F) (SeparableClosure F)
        (cocharacterLattice.galoisRepresentation F (SeparableClosure F) T)
        ((Fintype.card (L ≃ₐ[UnramifiedClosure F] L) : ℤ) • ν) := by
  rw [PermutationCoinvariants.mk_eq_mk_iff _ _ _
    (galoisRepresentation_geometricBasis_smul F E T hE b hb hact)]
  intro j
  rw [PermutationCoinvariants.orbitSum_smul]
  unfold PermutationCoinvariants.orbitSum
  rw [Module.Basis.repr_sum_self]
  simp_rw [orderUnits_inclusionHom_zpow]
  rw [PermutationCoinvariants.orbitFunSum_mul_const _
    (fun i => PermutationCoinvariants.orbitFunSum
      (relativeInertia F (UnramifiedClosure F) (SeparableClosure F))
      ((geometricBasis F E T hE b).repr ν) i) _ j (fun i hi => by
        obtain ⟨h, -, rfl⟩ := (PermutationCoinvariants.orbitClass_eq_iff _).mp hi
        exact hn h j), hsum j, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  ring

include hact hL in
omit [FiniteDimensional F E] in
/-- The Kottwitz value of the rational point built from the family is the target class. -/
theorem torusKottwitz_eq_of_family (hT : IsTorus T.toGrp) (u : J → Eˣ)
    (hsum : ∀ j, PermutationCoinvariants.orbitFunSum
      (relativeInertia F (UnramifiedClosure F) (SeparableClosure F))
      (fun i => (IntegerValuation.orderUnits (normalizedIntermediateValuation F L)
        (Units.map (inclusionHom F E L hEL) (u i))).toAdd) j =
      Module.finrank (UnramifiedClosure F) L)
    (ν : geometricCocharacters F (SeparableClosure F) T)
    (hn : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (j : J),
      PermutationCoinvariants.orbitSum (geometricBasis F E T hE b)
          (relativeInertia F (UnramifiedClosure F) (SeparableClosure F)) ν (σ • j) =
        PermutationCoinvariants.orbitSum (geometricBasis F E T hE b)
          (relativeInertia F (UnramifiedClosure F) (SeparableClosure F)) ν j)
    (x0 : affinePoints T.toGrp (CommAlgCat.of F F))
    (hx0 : GaloisPoint.extend F E T.toGrp x0 =
      (coefficientEvaluation F E T
        (∑ j, Additive.ofMul (u j ^ PermutationCoinvariants.orbitSum (geometricBasis F E T hE b)
          (relativeInertia F (UnramifiedClosure F) (SeparableClosure F)) ν j) ⊗ₜ[ULift.{u} ℤ]
            dualBasis T hE b j)).toMul) :
    (torusKottwitz F F T hT (GaloisPoint.extend F (UnramifiedClosure F) T.toGrp x0)).toAdd =
      inertiaProjection F (UnramifiedClosure F) (SeparableClosure F)
        (cocharacterLattice.galoisRepresentation F (SeparableClosure F) T) ν := by
  have hcard := card_smul_torusKottwitz F E T hE b L hL hEL hT
    (fun j => u j ^ PermutationCoinvariants.orbitSum (geometricBasis F E T hE b)
      (relativeInertia F (UnramifiedClosure F) (SeparableClosure F)) ν j) x0 hx0
  beta_reduce at hcard
  have hkey := mk_sum_eq_card_smul F E T hE b L hEL hb hact u hsum ν hn
  have hd0 : (Fintype.card (L ≃ₐ[UnramifiedClosure F] L) : ℤ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := L ≃ₐ[UnramifiedClosure F] L)).ne'
  apply PermutationCoinvariants.zsmul_cancel _ _ _
    (galoisRepresentation_geometricBasis_smul F E T hE b hb hact) hd0
  rw [natCast_zsmul, hcard, hkey]
  exact map_zsmul _ _ _

end Orbit

end InducedCocharacterBasis

end Langlands.Geometry.Building.Kottwitz
