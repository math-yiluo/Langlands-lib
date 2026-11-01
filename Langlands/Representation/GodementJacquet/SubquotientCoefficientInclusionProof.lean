import Langlands.Representation.GodementJacquet.SubquotientCoefficientInclusionStatement
import Langlands.Representation.Smooth.Contragredient.ExactProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Group.GL.CompactOpen

/-! # Bi-smooth coefficients of actual subquotients -/

namespace Langlands.GodementJacquet

universe uG uF uV uW

/-- Bi-smooth coefficient spaces decrease under actual subquotients of a smooth
complex representation when compact open subgroups are cofinal. -/
theorem subquotientCoefficientInclusion :
    SubquotientCoefficientInclusionStatement.{uG, uV, uW} := by
  intro G _ _ _ hcof V _ _ W _ _ σ τ hσ A q hq
  let i : A.toRepresentation.IntertwiningMap σ :=
    { toLinearMap := A.toSubmodule.subtype
      isIntertwining' _ := by ext; rfl }
  have hi : Function.Injective i := Subtype.val_injective
  have hA : IsSmooth A.toRepresentation := isSmooth_of_injective i hi hσ
  apply Submodule.span_le.mpr
  rintro f ⟨ℓ, v, rfl⟩
  obtain ⟨m, hm⟩ :=
    contragredientMap_surjective_of_injective_of_compact_cofinal
      hcof hA hσ i hi (contragredientMap q ℓ)
  obtain ⟨w, hw⟩ := hq v.val
  refine Submodule.subset_span ⟨m, ⟨(w : V), hσ (w : V)⟩, ?_⟩
  funext g
  have hext := congrArg
    (fun φ : SmoothDual A.toRepresentation => φ.val (A.toRepresentation g w)) hm
  change m.val (σ g (w : V)) = ℓ.val (τ g v.val)
  change m.val (σ g (w : V)) = ℓ.val (q (A.toRepresentation g w)) at hext
  rw [q.isIntertwining, hw] at hext
  exact hext

namespace Padic

/-- The coefficient inclusion for every canonical p-adic general linear group,
including rank one. -/
theorem subquotientCoefficientInclusion :
    SubquotientCoefficientInclusionStatement.{uF, uV, uW} := by
  intro p _ F
  let : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
  intro n V _ _ W _ _ σ τ hσ A q hq
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
  have hcof : ∀ K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
      ∃ L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
        IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hL, hLK⟩ :=
      F.canonicalTopologicalData.generalLinearCompactOpen (n + 1)
        (K : Set _) (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L, hL, hLK⟩
  exact GodementJacquet.subquotientCoefficientInclusion
    (Langlands.GeneralLinear (n + 1) F.Carrier) hcof V W σ τ hσ A q hq

end Padic

end Langlands.GodementJacquet
