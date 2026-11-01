import Langlands.Representation.Exponents.SquareIntegrableActualJacquetConeStatement
import Langlands.Representation.Exponents.AdmissibleCentralSubquotientProof
import Langlands.Representation.Exponents.AdmissibleCentralDualToPrimalProof
import Langlands.Representation.Exponents.JacquetEigenvectorProof
import Langlands.Representation.Exponents.NormalizedJacquetScalarCompatibilityProof
import Langlands.Representation.Classification.SquareIntegrableExponentProof
import Langlands.Group.GL.CompactOpen

/-! # Strict cones for actual scalar upper Jacquet subquotients -/

noncomputable section

open CategoryTheory

namespace Langlands

universe uF uV

/-- The real part of any nonzero actual scalar upper Jacquet subquotient of an
analytically square-integrable representation lies in the strict root cone. -/
theorem squareIntegrableActualJacquetCone :
    SquareIntegrableActualJacquetConeStatement.{uF,uV} := by
  intro p _ F T
  let := T.topology
  intro n hn π hsq B S _ hsub χ hscalar x hx
  let := T.valuativeRel
  let := T.localField
  let := T.leviTopologicalGroup B
  have := T.generalLinearTopologicalGroup n
  have hcofinal : ∀ H : OpenSubgroup (B.Levi F.Carrier),
      ∃ K : OpenSubgroup (B.Levi F.Carrier),
        IsCompact (K : Set (B.Levi F.Carrier)) ∧ K ≤ H := by
    intro H
    obtain ⟨K, hK, hKH⟩ := T.leviCompactOpen B H (H.isOpen.mem_nhds H.one_mem)
    exact ⟨K, hK, fun _ hv => hKH hv⟩
  let c : (Fin B.length → F.Carrierˣ) →* Subgroup.center (B.Levi F.Carrier) :=
    (B.blockScalarLevi F.Carrier).codRestrict _ (B.blockScalarLevi_mem_center F.Carrier)
  have hcont : Continuous (B.blockScalarLevi F.Carrier) := by
    change Continuous fun a : Fin B.length → F.Carrierˣ =>
      fun k => GeneralLinear.scalar (n := B.size k) (a k)
    exact continuous_pi fun k =>
      GeneralLinear.scalarContinuous.continuous.comp (continuous_apply k)
  have hc : Continuous c := hcont.subtype_mk _
  let J := (T.normalizedJacquetFunctor B).obj π
  obtain ⟨U, W, ⟨e⟩⟩ := hsub
  let q := SmoothRep.hom (SmoothRep.mkQ (SmoothRep.subrepresentation J U) W ≫ e.inv)
  have he : Function.Surjective (SmoothRep.hom e.inv) := by
    intro v
    refine ⟨SmoothRep.hom e.hom v, ?_⟩
    have hv := congrArg (fun f => SmoothRep.hom f v) e.hom_inv_id
    simpa only [SmoothRep.hom_comp, SmoothRep.hom_id,
      Representation.IntertwiningMap.comp_apply,
      Representation.IntertwiningMap.id_apply] using hv
  have hq : Function.Surjective q :=
    he.comp (SmoothRep.mkQ_surjective (SmoothRep.subrepresentation J U) W)
  have hadm := hsq.isAdmissible
  have hJadm := Parabolic.isAdmissible_normalizedJacquet F T B π.representation hadm
  obtain ⟨hopen, hdual⟩ := admissibleCentralSubquotient
    (B.Levi F.Carrier) hcofinal (Fin B.length → F.Carrierˣ)
    J J.representation c hc hJadm χ U S q.toLinearMap hq
    (fun a u => (Representation.IntertwiningMap.isIntertwining _ _ q _ u).trans
      (hscalar a (q u)))
  have hgen : IsGeneralizedEigencharacter (T.splitCentreJacquet B π.representation) χ :=
    admissibleCentralDualToPrimal
      (B.Levi F.Carrier) hcofinal (Fin B.length → F.Carrierˣ)
      J J.representation c hJadm χ hdual
  obtain ⟨k, w, hw, _⟩ := (isGeneralizedEigencharacter_iff _ _).mp hgen
  obtain ⟨v, hv⟩ := B.jacquetMk_surjective π.representation w
  have hvne : v ≠ 0 := by
    intro h
    apply hw
    rw [← hv, h, map_zero]
  let : Nontrivial π := ⟨⟨v, 0, hvne⟩⟩
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_centralQuotient n
  let := hμ
  obtain ⟨z, _⟩ := (hsq μ).2
  let ω : F.Carrierˣ →* ℂˣ := z.character.comp GeneralLinear.scalarToCenter
  have hω : Classification.HasScalarCharacter π.representation GeneralLinear.scalar ω :=
    fun a v => z.acts (GeneralLinear.scalarToCenter a) v
  obtain ⟨hunit, hstrict⟩ :=
    (glSquareIntegrableExponentCriterion p F T n hn π π.representation ω hadm hω).mp hsq
  apply hx.isPositiveRootCone_iff.mpr
  refine ⟨?_, hstrict B χ ⟨hopen, hgen⟩⟩
  intro a
  have heq := congrArg (fun ψ : F.Carrierˣ →* ℂˣ => ψ a)
    (T.jacquetExponent_comp_const_eq B hω hgen)
  change χ (fun _ => a) = ω a at heq
  rw [heq]
  exact hunit a

end Langlands
