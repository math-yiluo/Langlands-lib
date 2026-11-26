import Langlands.GroupScheme.Rational.NumberFieldScalarSpinCoverHasse
import Langlands.GroupScheme.Rational.NumberFieldHasseKernelTypeReduction
import Langlands.GroupScheme.Rational.AdjointHasseCenterReduction
import Langlands.GroupScheme.SimplyConnected.TypeBOddQuadraticPresentationProof
import Langlands.GroupScheme.OddOrthogonalMatrix.InnerAutomorphismEquiv
import Langlands.GroupScheme.Reductive.GeometricAdjoint
import Langlands.GroupScheme.SimplyConnected.CenterCharacterCartan
import Langlands.GroupScheme.Torus.AbsoluteCharacterIsomorphism
import Langlands.GroupScheme.HomScheme.FiniteDiagonalizableHom
import Langlands.LinearAlgebra.ClassicalCartanDeterminants

/-! # The Hasse kernel of simply connected type B groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open OddOrthogonalForm Quaternionic Langlands.LinearAlgebra
open Quaternionic.FirstKindInvolution (scalar)
open Quaternionic.ScalarNormOnePoints (reindexForm reindexGroupIso finrank_polarKer_reindexForm)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 950000
set_option synthInstance.maxHeartbeats 100000

private theorem natCard_affinePoints_of_absoluteCharacter_two {F K : Type u}
    [Field F] [CharZero F] [Field K] [Algebra F K]
    (Z : CommGroupScheme (Spec (CommRingCat.of F))) (hZ : IsMultiplicativeType Z.toGrp)
    (hchar : Nat.card (characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap F (SeparableClosure F))).obj Z)) = 2) :
    Nat.card (affinePoints Z.toGrp (CommAlgCat.of F K)) = 2 := by
  let Ω := SeparableClosure F
  let X := characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F Ω)).obj Z)
  let I := PUnit.{u+1}
  let A := CommAlgCat.of F K
  let T := (algSpec (CommRingCat.of F)).obj (op A)
  let ρ := characterLattice.galoisRepresentation F Ω Z
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsAddCyclic X := isAddCyclic_of_prime_card hchar
  let e : ZMod 2 ≃+ X := addEquivOfAddCyclicCardEq ((Nat.card_zmod 2).trans hchar.symm)
  have hfix (σ : Ω ≃ₐ[F] Ω) (x : X) : ρ σ x = x := by
    obtain ⟨a, _, ha⟩ := (Nat.card_eq_two_iff' (0 : X)).mp hchar
    by_cases hx : x = 0
    · rw [hx, map_zero]
    have hne : ρ σ x ≠ 0 := by
      intro h
      apply hx
      have he := congrArg (ρ σ⁻¹) h
      rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply, map_zero] at he
    exact (ha _ hne).trans (ha _ hx).symm
  let eI : (I → ZMod 2) ≃+ X := (AddEquiv.piUnique (fun _ : I => ZMod 2)).trans e
  let eZ := characterLattice.isoOfConstantAbsoluteEquiv hZ eI (fun σ i => hfix σ (eI i))
  let g := MultiplicativeTypeGaloisExactness.grpIso eZ ≪≫
    HomScheme.FiniteDiagonalizable.diagonalizableIso F I 2
  let p := (((yonedaGrp.mapIso g).app (op T)).groupIsoToMulEquiv).toEquiv.trans
    (piPointsEquiv (fun _ : I => (mu (Spec (CommRingCat.of F)) 2).toGrp) T).toEquiv
  let m := (Equiv.piUnique (fun _ : I => affinePoints (mu (Spec (CommRingCat.of F)) 2).toGrp A)).trans
    (mu.affinePointsEquiv 2 (Spec.algebraMap F K)).toEquiv
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  exact (Nat.card_congr (p.trans m)).trans ((IsPrimitiveRoot.neg_one (R := K) 0 (by decide)).card_rootsOfUnity)

/-- The odd quadratic presentation has an adjoint target and its full kernel has
order two, so the simply connected scalar spin Hasse theorem applies. -/
theorem numberFieldTypeBSimplyConnectedGaloisHasseKernel :
    NumberFieldTypeBSimplyConnectedGaloisHasseKernelStatement.{u} := by
  classical
  intro F _ _ G _ _ d n e hn hsc _ hB L _ _ _ _ ξ hξ
  have hn₂ : 2 ≤ n := by omega
  let R := d.typeBVectorQuotientRecovery n e hn₂ hsc hB
  let : IsAffine R.obj.X.left := R.isAffine
  let : IsAffineHom R.obj.X.hom := inferInstance
  have hR : IsAdjoint R.obj := IsAdjoint.of_fieldExtension
    ((OddOrthogonalMatrix.TypeBNumbering.isAdjoint_groupScheme (K := SeparableClosure F) hn₂).of_iso R.iso)
  obtain ⟨N, _, _, _, _, ⟨φ⟩⟩ := exists_galois_localIso F R.obj n R.iso
  let a : OddOrthogonalMatrix.Index (Fin n) ≃ Fin (2 * n + 1) :=
    Fintype.equivFinOfCardEq (by
      simp only [OddOrthogonalMatrix.Index, Fintype.card_sum, Fintype.card_unique, Fintype.card_fin]
      omega)
  let D := descendedMatrix φ hn₂
  let q := reindexForm a D
  have hpolar : Module.finrank F (LinearMap.ker ((scalar F).polar q).vecMulLinear) = 0 := by
    have h := (finrank_polarKer_reindexForm a D).trans (finrank_polarKer_descendedForm φ hn₂)
    rw [ite_eq_right two_ne_zero] at h
    exact h
  have hq : (scalar F).IsNondegenerateQuadratic q := Matrix.vecMul_injective_iff_isUnit.mp
    (LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hpolar))
  let c := descendedGroupIso φ hn₂ ≪≫ reindexGroupIso a D
  let p := R.hom ≫ c.hom
  have hAdj : IsAdjoint ((scalar F).normOneIsometryGroup q) := hR.of_iso c.symm
  have hp : IsCentralIsogeny p := R.isCentralIsogeny.comp_iso c
  let Z := d.toralCenter.group
  let Ω := AlgebraicClosure F
  let T := (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F Ω))
  let j := d.isoToralCenter (hp.isSchemeTheoreticCenter_kernelι_of_isAdjoint hAdj)
  have hchar := d.natCard_centerCharacter_eq_cartanDet hsc e (CartanMatrix.B n) hB
  rw [cartan_B_det (by omega)] at hchar
  have hker : Nat.card (affinePoints (kernel p) (CommAlgCat.of F Ω)) = 2 :=
    (Nat.card_congr (((yonedaGrp.mapIso j).app (op T)).groupIsoToMulEquiv).toEquiv).trans
      (natCard_affinePoints_of_absoluteCharacter_two Z d.toralCenter_isMultiplicativeType hchar)
  exact numberFieldScalarSpinCoverHasse F Ω (2 * n + 1) q hq (by omega) hAdj.isSemisimple G p hsc hp hker L ξ hξ

end Langlands.GroupScheme
