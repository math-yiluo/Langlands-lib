import Langlands.GroupScheme.Rational.NumberFieldQuaternionicSpinKernelReduction
import Langlands.GroupScheme.Rational.NumberFieldScalarEvenSpinHasse
import Langlands.GroupScheme.Quaternionic.NormOneIsometryConnectedness
import Langlands.GroupScheme.Torus.AbsoluteCharacterIsomorphism
import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisExactnessProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeSplitCategory
import Langlands.GroupScheme.HomScheme.FiniteDiagonalizableHom
import Langlands.GroupScheme.KernelSquareTransport
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry

/-! # The kernel of a quaternionic spin cover is `μ₂` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace HomScheme.FiniteDiagonalizable

variable (R : Type u) [CommRing R] (m : ℕ)

/-- The one-factor power `μ_m^{PUnit}` is `μ_m`. -/
def muPowerPUnitIso : muPower R PUnit.{u+1} m ≅ (mu (Spec (CommRingCat.of R)) m).toGrp :=
  isoOfPointModels (fun T : Over (Spec (CommRingCat.of R)) => rootsOfUnity m Γ(T.left, ⊤))
    (fun a => restrictRootsOfUnity a.left.appTop.hom m)
    (fun T => (muPowerPointsEquiv R PUnit.{u+1} m T).trans (MulEquiv.piUnique _))
    (fun T => mu.pointsEquiv (Spec (CommRingCat.of R)) m T)
    (fun a x => by
      change (muPowerPointsEquiv R PUnit.{u+1} m _ (a ≫ x)) PUnit.unit = _
      rw [muPowerPointsEquiv_naturality]
      rfl)
    (fun a y => mu.pointsEquiv_naturality _ m a y)

end HomScheme.FiniteDiagonalizable

open Quaternionic Quaternionic.FirstKindInvolution

/-- In characteristic zero, the kernel of a central isogeny from a simply connected group onto
the reduced-norm-one isometry group of a nondegenerate quadratic form of rank at least three
over a central quaternion division algebra with an orthogonal involution is `μ₂`. -/
theorem quaternionicSpinKernelMu : QuaternionicSpinKernelMuStatement.{u} := by
  intro F _ _ D _ _ _ _ hD σ hσ n _ hn q hq G p hG hp
  classical
  let Ω := SeparableClosure F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := inferInstance
  obtain ⟨e₀⟩ := CentralSimple.exists_matrix_chart_reducedDegree F D Ω
  let e : Ω ⊗[F] D ≃ₐ[Ω] Matrix (Fin 2) (Fin 2) Ω :=
    e₀.trans (Matrix.reindexAlgEquiv Ω Ω (finCongr (FirstKindInvolution.reducedDegree_eq_two hD)))
  let b := algebraBaseMap F Ω
  let B := GroupScheme.baseChange b
  let Q := NormOneSplit.gramQ e σ q
  have hQ : (scalar Ω).IsNondegenerateQuadratic Q :=
    MoritaIsometry.isNondegenerateQuadratic_gramN e σ n hσ q _ (Quotient.out_eq q) hq
  let s := NormOneSplit.splitIso e σ q hσ
  let r := B.map p ≫ s.hom
  have hr : IsCentralIsogeny r := (hp.baseChange b).comp_iso s
  have hGΩ : IsSimplyConnected (B.obj G) := isSimplyConnectedFieldExtension F Ω G hG
  -- The geometric kernel is the Clifford kernel `μ₂`.
  let : Invertible (2 : Ω) := invertibleOfNonzero two_ne_zero
  let : NeZero (2 * n) := ⟨by omega⟩
  obtain ⟨hsm, habs⟩ := ordinaryOrthogonalGeometry Ω n hn Q hQ
  let e₁ := scalarConnectedIsometryIso_normOne Q hQ habs.1.isSemisimple
  have hSO : IsSemisimple ((scalar Ω).normOneIsometryGroup Q) :=
    IsSemisimple.of_iso e₁.symm habs.1.isSemisimple
  let p' := r ≫ e₁.inv
  have hp' : IsCentralIsogeny p' := hr.comp_iso e₁.symm
  let k₀ : kernel p' ≅ kernel r := kernelSquareIso p' r (Iso.refl _) e₁ (by simp [p'])
  let K := AlgebraicClosure Ω
  have hker : Nat.card (affinePoints (kernel r) (CommAlgCat.of Ω K)) = 2 :=
    (Nat.card_congr ((Grp.forget _).mapIso k₀).homToEquiv).symm.trans
      (natCard_scalarEvenSpinKernel Q hn hQ p' hGΩ hp')
  obtain ⟨c, hc⟩ := CliffordSpin.exists_iso_of_simplyConnected_scalarCover (K := K) Q hQ
    (by omega) hSO r hGΩ hr hker
  let k₁ : kernel r ≅ kernel (CliffordSpin.projection Q) :=
    kernelSquareIso r _ c (Iso.refl _) (by simpa using hc)
  let Λ := PUnit.{u+1} → ZMod 2
  let iD : B.obj (kernel p) ≅ (Diagonalizable.groupScheme (CommRingCat.of Ω) Λ).toGrp :=
    kernelBaseChangeIso b p ≪≫
      kernelSquareIso (B.map p) r (Iso.refl _) s (by simp [r]) ≪≫ k₁ ≪≫
      CliffordSpin.kernelIso Q hQ ≪≫ (HomScheme.FiniteDiagonalizable.muPowerPUnitIso Ω 2).symm ≪≫
      (HomScheme.FiniteDiagonalizable.diagonalizableIso Ω PUnit.{u+1} 2).symm
  -- Descent through the absolute characters.
  let Z : CommGroupScheme (Spec (CommRingCat.of F)) := hp.isCentral_kernelι.commGroupScheme
  have hZ : IsMultiplicativeType Z.toGrp :=
    ⟨Ω, inferInstance, inferInstance, Λ, inferInstance, inferInstance, ⟨iD⟩⟩
  let BC := CommGroupScheme.baseChange (algebraBaseMap F Ω)
  let iC : (BC).obj Z ≅ Diagonalizable.groupScheme (CommRingCat.of Ω) Λ :=
    CommGroupScheme.isoOfGroupIso iD
  let eX : Λ ≃+ characterLattice ((BC).obj Z) :=
    (DiagonalizableCharacter.evalCharacterEquiv Ω Λ).trans (characterLattice.congr iC).symm
  let ρ := characterLattice.galoisRepresentation F Ω Z
  have hcard : Nat.card (characterLattice ((BC).obj Z)) = 2 := by
    rw [← Nat.card_congr eX.toEquiv]
    simp [Λ]
  have hfix (σ' : Ω ≃ₐ[F] Ω) (m : Λ) : ρ σ' (eX m) = eX m := by
    obtain ⟨a, _, ha⟩ := (Nat.card_eq_two_iff' (0 : characterLattice ((BC).obj Z))).mp hcard
    by_cases hx : eX m = 0
    · rw [hx, _root_.map_zero]
    have hne : ρ σ' (eX m) ≠ 0 := by
      intro h
      apply hx
      have he := congrArg (ρ σ'⁻¹) h
      rwa [← Module.End.mul_apply, ← _root_.map_mul, inv_mul_cancel, _root_.map_one,
        Module.End.one_apply, _root_.map_zero] at he
    exact (ha _ hne).trans (ha _ hx).symm
  let eZ := characterLattice.isoOfConstantAbsoluteEquiv hZ eX hfix
  exact ⟨MultiplicativeTypeGaloisExactness.grpIso eZ ≪≫
    HomScheme.FiniteDiagonalizable.diagonalizableIso F PUnit.{u+1} 2 ≪≫
    HomScheme.FiniteDiagonalizable.muPowerPUnitIso F 2⟩

end Langlands.GroupScheme
