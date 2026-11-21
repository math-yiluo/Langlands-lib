import Langlands.AbelianScheme.Tate.WeilRationalAlongHom
import Langlands.AbelianScheme.Tate.FullEvaluationKernel
import Langlands.AbelianScheme.Tate.ConnectedIntegralLatticeReflectionProof
import Langlands.AbelianScheme.Tate.WeilFiniteGeometricNondegeneracyProof

/-! # Integral perfectness of the Weil pairing at algebraically closed points -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.TateTwist.Divisibility

variable (R : Type u) [CommRing R]

/-- Every positive integer acts injectively on the full integral Tate twist. -/
theorem full_eq_zero_of_nsmul_eq_zero {k : ℕ} (hk : 0 < k) {x : Full R}
    (h : k • x = 0) : x = 0 := by
  apply Subtype.ext
  funext n
  let m : GroupScheme.Tate.Index (fun _ => True) :=
    ⟨n.val * k, Nat.mul_pos n.property.1 hk, trivial⟩
  have hx := congrArg (evaluation R (fun _ => True) m) h
  rw [map_nsmul, map_zero] at hx
  change evaluation R (fun _ => True) n x = evaluation R (fun _ => True) n 0
  rw [map_zero, ← evaluation_transition R (fun _ => True) n m (dvd_mul_right _ _) x]
  apply toUnit_injective R n.val
  have hm : (Additive.toMul (evaluation R (fun _ => True) m x)).val ^ k = 1 := by
    have := congrArg (fun y => (Additive.toMul y : rootsOfUnity m.val R).val) hx
    simpa using this
  change (Additive.toMul (evaluation R (fun _ => True) m x)).val ^ (n.val * k / n.val) = 1
  rw [Nat.mul_div_cancel_left _ n.property.1, hm]

/-- The full integral Tate twist embeds in its rationalization. -/
theorem full_toRational_injective :
    Function.Injective (toRational R (fun _ => True)) := by
  let : IsLocalizedModule (nonZeroDivisors ℤ) (toRational R (fun _ => True)) :=
    IsLocalization.tensorProduct_isLocalizedModule (nonZeroDivisors ℤ) ℚ
  intro x y hxy
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors ℤ) hxy
  rw [← sub_eq_zero]
  have hc' : (c : ℤ) • (x - y) = 0 := by
    rw [smul_sub, sub_eq_zero]
    simpa only [Submonoid.smul_def] using hc
  have hk : 0 < (c : ℤ).natAbs := Int.natAbs_pos.mpr (nonZeroDivisors.coe_ne_zero c)
  exact full_eq_zero_of_nsmul_eq_zero R hk ((natAbs_nsmul_eq_zero).mpr hc')

end Langlands.TateTwist.Divisibility

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme Langlands.AlgebraicGeometry.FiniteEtale

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})

local notation "GD" => Langlands.CommGroupScheme.toGrp
  (dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA stability
    composition unitCoherence associativity comparison symmetry)
local notation "integralPair" => integralWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA MA evaluationA compatibility
local notation "rationalPairing" => rationalWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA MA evaluationA compatibility

/-- The rational dual Tate vectors whose Weil pairing with every integral Tate vector of
`A` is integral. -/
def weilIntegralDual (T : Over S) : AddSubgroup (GroupScheme.Tate.RationalFull GD T) where
  carrier := {y | ∀ x : GroupScheme.Tate.Full A.toGrp T,
    rationalPairing T (fun _ => True) (GroupScheme.Tate.toRational A.toGrp T (fun _ => True) x) y ∈
      LinearMap.range (TateTwist.Divisibility.toRational Γ(T.left, ⊤) (fun _ => True))}
  zero_mem' := fun x => ⟨0, by rw [map_zero, map_zero]⟩
  add_mem' := by
    rintro y y' hy hy' x
    obtain ⟨z, hz⟩ := hy x
    obtain ⟨z', hz'⟩ := hy' x
    exact ⟨z + z', by rw [map_add, map_add, hz, hz']⟩
  neg_mem' := by
    rintro y hy x
    obtain ⟨z, hz⟩ := hy x
    exact ⟨-z, by rw [map_neg, map_neg, hz]⟩

theorem mem_weilIntegralDual (T : Over S) (y : GroupScheme.Tate.RationalFull GD T) :
    y ∈ weilIntegralDual preservation composition unitCoherence associativity comparison
      symmetry stability hA MA evaluationA compatibility T ↔
    ∀ x : GroupScheme.Tate.Full A.toGrp T,
      rationalPairing T (fun _ => True) (GroupScheme.Tate.toRational A.toGrp T (fun _ => True) x) y ∈
        LinearMap.range (TateTwist.Divisibility.toRational Γ(T.left, ⊤) (fun _ => True)) :=
  Iff.rfl

variable (square : MumfordBundlePicardZeroStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  (geometryA : DualSchemeGeometry A hA)

include square universality geometryA in
/-- Integral form of perfectness: a dual integral Tate vector whose pairing with every
integral Tate vector of `A` is divisible by `N` is itself divisible by `N`. -/
theorem integralWeil_exists_nsmul_of_forall
    (hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (s : Spec (.of K) ⟶ S)
    (N : GroupScheme.Tate.Index (fun _ => True)) (y : GroupScheme.Tate.Full GD (Over.mk s))
    (hy : ∀ x : GroupScheme.Tate.Full A.toGrp (Over.mk s),
      ∃ z, integralPair (Over.mk s) (fun _ => True) x y = N.val • z) :
    ∃ y' : GroupScheme.Tate.Full GD (Over.mk s), N.val • y' = y := by
  apply GroupScheme.Tate.full_exists_nsmul_of_evaluation_eq_zero GD (Over.mk s) N y
  have hN : (N.val : K) ≠ 0 := Nat.cast_ne_zero.mpr N.property.1.ne'
  refine (geometricFiniteWeilNondegeneracy preservation square universality composition
    unitCoherence associativity comparison symmetry stability compatibility S A hA geometryA
    MA evaluationA K s N.val hN).2 _ ?_
  intro x'
  obtain ⟨x, rfl⟩ := Tate.full_evaluation_surjective_at hu A s N x'
  obtain ⟨z, hz⟩ := hy x
  have he := evaluation_integralWeilValue preservation composition unitCoherence
    associativity comparison symmetry stability hA MA evaluationA compatibility (Over.mk s)
    (fun _ => True) N x y
  rw [← he]
  change TateTwist.Divisibility.evaluation Γ((Over.mk s).left, ⊤) (fun _ => True) N
    (integralPair (Over.mk s) (fun _ => True) x y) = 0
  rw [hz, map_nsmul]
  exact TateTwist.level_nsmul_eq_zero _ N.val _

include square universality geometryA in
/-- At an algebraically closed point of characteristic zero, the rational dual Tate
vectors pairing integrally with the integral Tate group of `A` are exactly the integral
dual Tate vectors. -/
theorem weilIntegralDual_eq_range
    (hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (s : Spec (.of K) ⟶ S) :
    weilIntegralDual preservation composition unitCoherence associativity comparison
      symmetry stability hA MA evaluationA compatibility (Over.mk s) =
      (LinearMap.range (GroupScheme.Tate.toRational GD (Over.mk s) (fun _ => True))).toAddSubgroup := by
  ext y
  constructor
  · intro hy
    let : IsLocalizedModule (nonZeroDivisors ℤ)
        (GroupScheme.Tate.toRational GD (Over.mk s) (fun _ => True)) :=
      IsLocalization.tensorProduct_isLocalizedModule (nonZeroDivisors ℤ) ℚ
    obtain ⟨⟨y0, c⟩, hc⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ)
      (GroupScheme.Tate.toRational GD (Over.mk s) (fun _ => True)) y
    simp only [Submonoid.smul_def] at hc
    have hc0 : (c : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    let N : GroupScheme.Tate.Index (fun _ => True) :=
      ⟨(c : ℤ).natAbs, Int.natAbs_pos.mpr hc0, trivial⟩
    have hdiv : ∀ x : GroupScheme.Tate.Full A.toGrp (Over.mk s),
        ∃ z, integralPair (Over.mk s) (fun _ => True) x y0 = N.val • z := by
      intro x
      obtain ⟨z, hz⟩ := hy x
      refine ⟨Int.sign (c : ℤ) • z, ?_⟩
      apply TateTwist.Divisibility.full_toRational_injective
      rw [← rationalWeilBilinearMap_toRational, ← hc, map_zsmul, ← hz, map_nsmul, map_zsmul,
        ← natCast_zsmul, smul_smul]
      congr 1
      change (c : ℤ) = ((c : ℤ).natAbs : ℤ) * Int.sign (c : ℤ)
      rw [mul_comm, Int.sign_mul_natAbs]
    obtain ⟨y1, hy1⟩ := integralWeil_exists_nsmul_of_forall preservation composition
      unitCoherence associativity comparison symmetry stability hA MA evaluationA compatibility
      square universality geometryA hu s N y0 hdiv
    refine ⟨Int.sign (c : ℤ) • y1, ?_⟩
    have hq : ((c : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc0
    have hinj : ∀ a b : GroupScheme.Tate.RationalFull GD (Over.mk s),
        (c : ℤ) • a = (c : ℤ) • b → a = b := by
      intro a b hab
      have hab' : ((c : ℤ) : ℚ) • a = ((c : ℤ) : ℚ) • b := by
        rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, hab]
      calc a = (((c : ℤ) : ℚ)⁻¹ * ((c : ℤ) : ℚ)) • a := by rw [inv_mul_cancel₀ hq, one_smul]
        _ = (((c : ℤ) : ℚ)⁻¹ * ((c : ℤ) : ℚ)) • b := by rw [mul_smul, mul_smul, hab']
        _ = b := by rw [inv_mul_cancel₀ hq, one_smul]
    apply hinj
    change (c : ℤ) • GroupScheme.Tate.toRational GD (Over.mk s) (fun _ => True)
      (Int.sign (c : ℤ) • y1) = (c : ℤ) • y
    rw [hc, ← map_zsmul, smul_smul, Int.mul_sign_self, natCast_zsmul]
    exact congrArg _ hy1
  · rintro ⟨y0, rfl⟩ x
    exact ⟨integralPair (Over.mk s) (fun _ => True) x y0,
      (rationalWeilBilinearMap_toRational preservation composition unitCoherence associativity
        comparison symmetry stability hA MA evaluationA compatibility (Over.mk s)
        (fun _ => True) x y0).symm⟩

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

include square universality in
/-- A rational dual-valued homomorphism whose Weil pairing is integral on the integral Tate
group, at one algebraically closed point of characteristic zero of a connected locally
noetherian base, is an actual homomorphism. -/
theorem exists_ofHom_eq_of_weilIntegral (htor : TorsionFiniteEtaleStatement.{u})
    [IsLocallyNoetherian S] [ConnectedSpace S]
    (hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (s : Spec (.of K) ⟶ S)
    (r : Rationalization.Hom A DA)
    (hr : ∀ x x' : GroupScheme.Tate.Full A.toGrp (Over.mk s),
      rationalPairing (Over.mk s) (fun _ => True)
          (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True) x)
          (Tate.rationalHomMap (Over.mk s) (fun _ => True) r
            (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True) x')) ∈
        LinearMap.range
          (TateTwist.Divisibility.toRational Γ((Over.mk s).left, ⊤) (fun _ => True))) :
    ∃ g : A ⟶ DA, Rationalization.ofHom g = r := by
  apply Tate.exists_ofHom_eq_of_full_image htor hu s r
  intro x'
  have hmem : Tate.rationalHomMap (Over.mk s) (fun _ => True) r
      (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True) x') ∈
      weilIntegralDual preservation composition unitCoherence associativity comparison
        symmetry stability hA MA evaluationA compatibility (Over.mk s) := fun x => hr x x'
  rw [weilIntegralDual_eq_range preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA compatibility square universality
    geometryA hu s] at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, hy.symm⟩

end Langlands.AbelianScheme
