import Langlands.Correspondence.HenniartCandidateFieldTransport
import Langlands.Correspondence.HenniartStableImage

/-! # Transport of stable images through a p-adic field automorphism -/

noncomputable section

namespace Langlands.Henniart.StableMap

open Langlands.Correspondence Langlands.VirtualRepresentation Langlands.Weil.Local

universe uK uW uV uC uQ uG uH

private theorem factorsThrough_restrictBasisEquiv_iff {G : Type uG} {H : Type uH}
    [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] {Q : Type uQ} [Group Q]
    (φ : G ≃ₜ* H) (q : H →* Q) (b : Weil.IrreducibleBasis.{uH, uW} H) :
    Weil.FactorsThrough G (q.comp (φ : G →ₜ* H).toMonoidHom) (Weil.restrictBasisEquiv φ b) ↔
      Weil.FactorsThrough H q b := by
  open FiniteRepresentation in
  let restrict : IsomorphismClasses.{0, uH, uW} ℂ H → IsomorphismClasses.{0, uG, uW} ℂ G :=
    restrictClass (φ : G →ₜ* H).toMonoidHom
  open FiniteRepresentation in
  have hleft : Function.LeftInverse (restrictClass (φ.symm : H →ₜ* G).toMonoidHom) restrict := by
    intro c
    induction c using Quotient.inductionOn with
    | h A => exact Quotient.sound ⟨restrictSymmRestrictEquiv φ A⟩
  unfold Weil.FactorsThrough
  rw [Weil.underlyingClass_restrictBasisEquiv]
  exact ⟨fun ⟨R, hR⟩ => ⟨R, hleft.injective hR⟩, fun ⟨R, hR⟩ => ⟨R, congrArg restrict hR⟩⟩

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
  (f : K.Carrier ≃ₐ[Padic p] K.Carrier)

local notation "φ" => extensionWeilEquiv K K f.symm

private def absoluteGaloisPullback : Field.absoluteGaloisGroup K.Carrier ≃*
    Field.absoluteGaloisGroup K.Carrier :=
  let a := extensionGaloisMap K K f.symm.toAlgHom
  MulEquiv.ofBijective a.toMonoidHom ⟨extensionGaloisMap_injective K K f.symm.toAlgHom, by
    apply (MonoidHom.range_eq_top (f := a.toMonoidHom)).mp
    apply Subgroup.index_eq_one.mp
    rw [extensionGaloisMap_range_index, extensionDegree_algEquiv]⟩

local notation "α" => absoluteGaloisPullback K f
local notation "wPull" => Weil.restrictUnitaryLatticeEquiv φ
local notation "aPull" => PadicSupercuspidal.unitaryLatticeEquiv K K f

private theorem finiteFactoring_pullback_iff {Q : Type uQ} [Group Q] [Finite Q]
    (q : Field.absoluteGaloisGroup K.Carrier →* Q) (x : LocalWeil.UnitaryLattice.{uK, uW} K) :
    wPull x ∈ LocalWeil.unitaryFiniteFactoringSupported K (q.comp (α).toMonoidHom) ↔
      x ∈ LocalWeil.unitaryFiniteFactoringSupported K q := by
  have hproj : (q.comp (α).toMonoidHom).comp (localProjection K).toMonoidHom =
      (q.comp (localProjection K).toMonoidHom).comp (φ : _ →ₜ* _).toMonoidHom := by
    ext w
    exact congrArg q (localProjection_extensionWeilMap K K f.symm.toAlgHom w).symm
  simp only [LocalWeil.unitaryFiniteFactoringSupported, Weil.unitaryFactoringSupported, supported,
    Finsupp.mem_supported, hproj]
  constructor
  · intro h b hb
    have hmem := (LocalWeil.restrictUnitaryBasisEquiv_mem_support_iff φ x b).2 hb
    exact (factorsThrough_restrictBasisEquiv_iff φ _ b.val).1 (h hmem)
  · intro h b hb
    obtain ⟨b, rfl⟩ := (Weil.restrictUnitaryBasisEquiv φ).surjective b
    have hmem := (LocalWeil.restrictUnitaryBasisEquiv_mem_support_iff φ x b).1 hb
    exact (factorsThrough_restrictBasisEquiv_iff φ _ b.val).2 (h hmem)

private theorem isCandidate_fieldPullback {Q : Type uQ} [Group Q] [Finite Q]
    (q : Field.absoluteGaloisGroup K.Carrier →* Q)
    {W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K)}
    {A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)} {T : W ≃ₗ[ℤ] A}
    (hT : IsCandidate.{uK, uW, uV, uC, uQ} K q T) :
    IsCandidate.{uK, uW, uV, uC, uQ} K (q.comp (α).toMonoidHom)
      (LatticeMap.fieldPullback K K f T) := by
  refine ⟨?_, LatticeMap.henniartProperties_fieldPullback K K f T hT.2⟩
  intro x hx
  obtain ⟨y, rfl⟩ := (wPull).surjective x
  exact Submodule.mem_map_of_mem (hT.1 ((finiteFactoring_pullback_iff K f q y).1 hx))

/-- If stable images exist in the given rank, the stable image of the Weil
pullback is the field pullback of the original stable image. -/
theorem IsStableImage.fieldPullback
    (hCE : CandidateExistenceStatement.{uK, uW, uV, uC, uK})
    {b : LocalWeil.UnitaryBasis.{uK, uW} K} {y : PadicSupercuspidal.UnitaryLattice.{uK, uV} K}
    (h : IsStableImage.{uK, uW, uV, uC} K b y)
    (hS : StableExistsAt.{uK, uW, uV, uC} K b.val.1) :
    IsStableImage.{uK, uW, uV, uC} K (Weil.restrictUnitaryBasisEquiv φ b) (aPull y) := by
  obtain ⟨Q, _, _, q, hq, hall⟩ := h.exists_quotient K
  have hq' : IsFiniteFactoring K (Weil.restrictUnitaryBasisEquiv φ b) := by
    refine ⟨Q, inferInstance, inferInstance, q.comp (α).toMonoidHom, ?_⟩
    rw [← Weil.restrictUnitaryLatticeEquiv_generator]
    exact (finiteFactoring_pullback_iff K f q _).2 hq
  obtain ⟨y', hy'⟩ := hS (Weil.restrictUnitaryBasisEquiv φ b) rfl hq'
  obtain ⟨R, _, _, r, -, hrall⟩ := hy'.exists_quotient K
  let s := q.prod (r.comp (α).symm.toMonoidHom)
  obtain ⟨W, A, T, hT⟩ := hCE p K (Q × R) s
  obtain ⟨x, hx, hTx⟩ := hall s (MonoidHom.fst Q R) rfl W A T hT
  have hr : (MonoidHom.snd Q R).comp (s.comp (α).toMonoidHom) = r :=
    MonoidHom.ext fun g => congrArg r ((α).symm_apply_apply g)
  obtain ⟨x', hx', hTx'⟩ := hrall _ (MonoidHom.snd Q R) hr _ _ _
    (isCandidate_fieldPullback K f s hT)
  have hxEq : x' = ((wPull).submoduleMap W) x := by
    apply Subtype.ext
    change x'.val = wPull x.val
    rw [hx', hx, Weil.restrictUnitaryLatticeEquiv_generator]
  have hyEq : y' = aPull y := by
    rw [← hTx', hxEq, LatticeMap.fieldPullback_apply, hTx]
  exact hyEq ▸ hy'

end Langlands.Henniart.StableMap
