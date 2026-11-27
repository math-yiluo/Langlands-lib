import Langlands.Correspondence.HenniartCandidateBaseChangeCompatibilityReductionStatement
import Langlands.Correspondence.HenniartCandidateStableTransport
import Langlands.Correspondence.HenniartGaloisPullback
import Langlands.Weil.Local.FiniteGaloisEquivariance
import Langlands.ClassFieldTheory.Local.CommonClosureExistenceProof

/-! # Galois equivariance of Henniart's candidate in each rank where it is defined -/

noncomputable section

namespace Langlands.Henniart

open Langlands.Correspondence Langlands.VirtualRepresentation Langlands.Weil.Local StableMap Numerical

universe uK uW uV

section WeilConjugation

variable {p : ℕ} [Fact p.Prime] (S : CyclicPrimeStep.{uK} p) (w : localWeilGroup S.base)

local notation "g" => padicGaloisEquiv S.base S.top S.embedding S.isGalois w
local notation "c" => finiteGaloisWeilConjugation S.base S.top S.embedding S.isGalois w
local notation "φ" => extensionWeilEquiv S.top S.top (AlgEquiv.symm g)

/-- The chosen lift and the lift given by the Weil element differ by an automorphism
fixing the field. Its action intertwines the conjugations of absolute Galois images. -/
private theorem exists_galois_intertwiner :
    ∃ κ : Field.absoluteGaloisGroup S.top.Carrier, ∀ y : localWeilGroup S.top,
      κ * localProjection S.top (φ y) = localProjection S.top (c y) * κ := by
  let lift := extensionClosureEquiv S.top S.top (g).symm.toAlgHom
  let θ := closureConjugation S.base S.top S.embedding w
  have hfix (x : S.top.Carrier) :
      (lift.trans θ) (algebraMap S.top.Carrier _ x) = algebraMap S.top.Carrier _ x := by
    change θ (extensionClosureEquiv S.top S.top (g).symm.toAlgHom (algebraMap S.top.Carrier _ x)) = _
    rw [extensionClosureEquiv_apply, extensionClosureLift_algebraMap]
    change closureConjugation S.base S.top S.embedding w (algebraMap S.top.Carrier _ ((g).symm x)) = _
    rw [closureConjugation_algebraMap S.base S.top S.embedding S.isGalois]
    change algebraMap S.top.Carrier _ (g ((g).symm x)) = _
    rw [AlgEquiv.apply_symm_apply]
  refine ⟨AlgEquiv.ofRingEquiv (f := lift.trans θ) hfix, fun y => ?_⟩
  apply AlgEquiv.ext
  intro x
  change θ (lift (AlgEquiv.toAlgHom (localProjection S.top (φ y)) x)) =
    AlgEquiv.toAlgHom (localProjection S.top (c y)) (θ (lift x))
  rw [localProjection_finiteGaloisWeilConjugation_closure, extensionWeilEquiv_apply,
    localProjection_extensionWeilMap]
  exact congrArg θ (extensionClosureLift_galoisMap S.top S.top (g).symm.toAlgHom _ x)

private theorem restrictUnitaryBasisEquiv_conjugation
    (b : LocalWeil.UnitaryBasis.{uK, uW} S.top) (hb : IsFiniteFactoring S.top b) :
    Weil.restrictUnitaryBasisEquiv φ b = Weil.restrictUnitaryBasisEquiv c b := by
  obtain ⟨Q, _, _, q, hq⟩ := hb
  have hfact : Weil.FactorsThrough _ (q.comp (localProjection S.top).toMonoidHom) b.val := by
    simp only [LocalWeil.unitaryFiniteFactoringSupported, Weil.unitaryFactoringSupported, supported,
      Finsupp.mem_supported] at hq
    exact hq (Finsupp.mem_support_iff.mpr (by simp [generator]))
  obtain ⟨R, hR⟩ := hfact
  obtain ⟨κ, hκ⟩ := exists_galois_intertwiner S w
  apply Subtype.ext
  apply LocalNumerical.underlyingClass_injective
  rw [Weil.restrictUnitaryBasisEquiv_val, Weil.restrictUnitaryBasisEquiv_val,
    Weil.underlyingClass_restrictBasisEquiv, Weil.underlyingClass_restrictBasisEquiv, ← hR]
  apply (FiniteRepresentation.classOf_eq_iff _ _).mpr
  refine ⟨Representation.Equiv.mk
    (LinearMap.GeneralLinearGroup.toLinearEquiv (R.representation.asGroupHom (q κ))) fun y => ?_⟩
  change R.representation (q κ) * R.representation (q (localProjection S.top (φ y))) =
    R.representation (q (localProjection S.top (c y))) * R.representation (q κ)
  simpa only [MonoidHom.comp_apply, map_mul] using congrArg (R.representation.comp q) (hκ y)

private theorem conjugation_unramifiedCharacter (z : ℂˣ) :
    (localUnramifiedCharacter S.top z).comp (c : _ →ₜ* _) = localUnramifiedCharacter S.top z := by
  apply ContinuousMonoidHom.ext
  intro y
  change unramifiedCharacter (localDegree S.top) z (c y) =
    unramifiedCharacter (localDegree S.top) z y
  simp only [unramifiedCharacter_apply, localDegree_finiteGaloisWeilConjugation]

end WeilConjugation

section SupercuspidalTwist

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
  (f : K.Carrier ≃ₐ[Padic p] K.Carrier)

private def supercuspidalBasisPullback : PadicSupercuspidal.Basis.{uK, uV} K ≃
    PadicSupercuspidal.Basis.{uK, uV} K :=
  letI := K.canonicalTopologicalData.topology
  Supercuspidal.fieldBasisEquiv f.toRingEquiv (PadicSupercuspidal.continuous_algEquiv K K f)
    (PadicSupercuspidal.continuous_algEquiv K K f.symm)

private theorem supercuspidalBasisPullback_unramified (z : ℂˣ)
    (b : PadicSupercuspidal.Basis.{uK, uV} K) :
    supercuspidalBasisPullback K f (PadicSupercuspidal.unramifiedTwistBasisEquiv K z b) =
      PadicSupercuspidal.unramifiedTwistBasisEquiv K z (supercuspidalBasisPullback K f b) := by
  let := K.canonicalTopologicalData.topology
  unfold supercuspidalBasisPullback PadicSupercuspidal.unramifiedTwistBasisEquiv
  apply Supercuspidal.fieldBasisEquiv_twistBasisEquiv
  intro n x
  simp only [PadicField.TopologicalData.determinantUnramifiedCharacter_apply]
  have hdet := GeneralLinear.determinant_fieldEquiv f.toRingEquiv
    (PadicSupercuspidal.continuous_algEquiv K K f)
    (PadicSupercuspidal.continuous_algEquiv K K f.symm) x
  exact congrArg (fun i : ℤ => z ^ i)
    ((PadicField.CanonicalTransport.ord_map K K f _).symm.trans
      (congrArg K.canonicalTopologicalData.ord hdet.symm))

end SupercuspidalTwist

/-- Candidate existence implies equivariance of the rank extension for the paired
Weil conjugation and finite Galois automorphism of each cyclic prime-degree step. -/
theorem candidateGaloisEquivarianceReduction :
    CandidateGaloisEquivarianceReductionStatement.{uK, uW, uV} := by
  intro hCE p _ S k hM w τ
  let f := padicGaloisEquiv S.base S.top S.embedding S.isGalois w
  let c := finiteGaloisWeilConjugation S.base S.top S.embedding S.isGalois w
  obtain ⟨z, π, b, hb, hval⟩ := Extension.rankExtensionBasis_spec S.top hM τ
  have hS : StableExistsAt.{uK, uW, uV, uW} S.top b.val.1 := by
    have hr : b.val.1 = k.succPNat := congrArg Sigma.fst hb.1
    rw [hr]
    exact hM
  have hstable := hb.2.fieldPullback S.top f hCE hS
  rw [PadicSupercuspidal.unitaryLatticeEquiv_generator] at hstable
  have hcompare := restrictUnitaryBasisEquiv_conjugation S w b (hb.2.isFiniteFactoring S.top)
  have hdecomp : Extension.IsStableDecomposition.{uK, uW, uV, uW} S.top
      ⟨k.succPNat, weilConjugate S w τ⟩ z
      (Weil.restrictUnitaryBasisEquiv (extensionWeilEquiv S.top S.top f.symm) b)
      (PadicSupercuspidal.unitaryBasisEquiv S.top S.top f π) := by
    refine ⟨?_, hstable⟩
    have h := congrArg (Weil.restrictBasisEquiv c) hb.1
    rw [Weil.restrictBasisEquiv_twistBasisEquiv, conjugation_unramifiedCharacter S w z,
      ← Weil.restrictUnitaryBasisEquiv_val, ← hcompare] at h
    exact h
  have hUTI := Extension.unramifiedTwistIndependence_of_reciprocity hCE
    LocalClassField.commonClosureReciprocityExistence
  have hconjValue := Extension.rankExtensionBasis_eq S.top hM hUTI hdecomp
  have hsigma :
      (⟨k.succPNat, Extension.rankExtension S.top hM (weilConjugate S w τ)⟩ :
        PadicSupercuspidal.Basis.{uK, uV} S.top) =
        supercuspidalBasisPullback S.top f ⟨k.succPNat, Extension.rankExtension S.top hM τ⟩ := by
    rw [Extension.sigma_rankExtension, Extension.sigma_rankExtension, hconjValue, hval,
      supercuspidalBasisPullback_unramified]
    rfl
  change _ = (⟨k.succPNat, S.galoisConjugate
    (finiteGaloisQuotient S.base S.top S.embedding S.isGalois w) k
      (Extension.rankExtension S.top hM τ)⟩ : PadicSupercuspidal.Basis.{uK, uV} S.top) at hsigma
  exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2

end Langlands.Henniart
