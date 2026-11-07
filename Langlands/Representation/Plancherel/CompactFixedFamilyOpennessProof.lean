import Langlands.Representation.Plancherel.CompactFixedFamilyOpennessStatement
import Langlands.Representation.Plancherel.FiniteMatrixOpennessProof
import Langlands.Representation.Smooth.FixedVectors.DetectionConsequencesProof

noncomputable section

namespace Langlands.Plancherel.CompactFixedFamilyOpenness

open MeasureTheory CategoryTheory

universe uG uV un

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  (A : SmoothRep.{0, uG, uV} ℂ G) (K : OpenSubgroup G)
  (hK : IsCompact (K : Set G))

/-- The normalized fixed projection preserves actual invariant submodules. -/
theorem fixedProjection_mem (S : Subrepresentation A.representation)
    {v : A} (hv : v ∈ S) :
    (Hecke.fixedProjection μ A.representation A.isSmooth K hK v : A) ∈ S := by
  let C := SmoothRep.subrepresentation A S
  let i := SmoothRep.hom (SmoothRep.subtype A S)
  have h := Hecke.fixedProjection_intertwiner μ C.representation C.isSmooth K hK
    A.isSmooth i (⟨v, hv⟩ : C)
  have heq := congrArg Subtype.val h
  exact heq ▸ (Hecke.fixedProjection μ C.representation C.isSmooth K hK
    (⟨v, hv⟩ : C)).val.property

/-- Irreducibility of the actual compressed matrices detects irreducibility
of the representation when every irreducible subquotient is detected. -/
theorem isIrreducible_of_fixedMatrix [Nontrivial A]
    {n : Type un} [Fintype n]
    (e : Module.Basis n ℂ (fixedVectors A.representation K.toSubgroup))
    (hdet : ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      D.IsIrreducible → SmoothRep.IsSubquotient D A →
        ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0)
    (hirr : UnitarizabilityContinuation.IsIrreducibleFamily
      (UnitarizabilityContinuation.fixedMatrix μ A.isSmooth hK e A.representation)) :
    A.IsIrreducible := by
  classical
  have hall := SmoothRep.fixedVector_of_irreducible_subquotient_detection A K hK hdet
  have hgen := SmoothRep.fixedVectors_generate_subquotients_of_detection A K hK hall
  have hAA : SmoothRep.IsSubquotient A A :=
    SmoothRep.IsQuotient.isSubquotient ⟨𝟙 A, fun v => ⟨v, rfl⟩⟩
  refine { exists_pair_ne := ⟨⊥, ⊤, fun he => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · obtain ⟨v, hv⟩ := exists_ne (0 : A)
    apply hv
    have hmem : v ∈ (⊤ : Subrepresentation A.representation) := trivial
    rw [← he] at hmem
    exact hmem
  · by_cases hS : S = ⊥
    · exact Or.inl hS
    right
    let U : Submodule ℂ (n → ℂ) := S.toSubmodule.comap
      ((fixedVectors A.representation K.toSubgroup).subtype ∘ₗ e.equivFun.symm.toLinearMap)
    have hU : ∀ g v, v ∈ U →
        (UnitarizabilityContinuation.fixedMatrix μ A.isSmooth hK e A.representation g).mulVec v ∈ U := by
      intro g v hv
      change (e.equivFun.symm
        ((UnitarizabilityContinuation.fixedMatrix μ A.isSmooth hK e A.representation g).mulVec v) : A) ∈ S
      rw [← UnitarizabilityContinuation.coe_fixedProjection_symm]
      exact fixedProjection_mem μ A K hK S (S.apply_mem_toSubmodule g hv)
    rcases hirr U hU with h | h
    · exfalso
      have hSmod : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.toSubmodule_injective h)
      obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSmod
      let C := SmoothRep.subrepresentation A S
      have hC : Nontrivial C := ⟨⟨⟨s, hs⟩, 0, fun hz => hs0 (congrArg Subtype.val hz)⟩⟩
      have hCA : SmoothRep.IsSubquotient C A :=
        (SmoothRep.subrepresentation_isSubrepresentation (A := A) S).isSubquotient
      obtain ⟨w, hw, hw0⟩ := hall C hCA hC
      let i := SmoothRep.hom (SmoothRep.subtype A S)
      let v : fixedVectors A.representation K.toSubgroup := ⟨i w, map_mem_fixedVectors i hw⟩
      have hv : e.equivFun v ∈ U := by
        change (e.equivFun.symm (e.equivFun v) : A) ∈ S
        rw [LinearEquiv.symm_apply_apply]
        exact w.property
      have hv0 : e.equivFun v = 0 := by simpa only [h, Submodule.mem_bot] using hv
      have hv0' : v = 0 := e.equivFun.injective (hv0.trans (map_zero e.equivFun).symm)
      apply hw0
      apply Subtype.ext
      exact congrArg
        (fun z : fixedVectors A.representation K.toSubgroup => (z : A)) hv0'
    · apply hgen A hAA S
      intro v hv
      have hvU : e.equivFun ⟨v, hv⟩ ∈ U := h ▸ Submodule.mem_top
      change (e.equivFun.symm (e.equivFun ⟨v, hv⟩) : A) ∈ S at hvU
      change v ∈ S
      rw [LinearEquiv.symm_apply_apply] at hvU
      exact hvU

/-- Under detection, actual irreducibility and compressed-matrix
irreducibility are equivalent. -/
theorem isIrreducible_iff_fixedMatrix [Nontrivial A]
    {n : Type un} [Fintype n]
    (e : Module.Basis n ℂ (fixedVectors A.representation K.toSubgroup))
    (hdet : ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      D.IsIrreducible → SmoothRep.IsSubquotient D A →
        ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0) :
    A.IsIrreducible ↔ UnitarizabilityContinuation.IsIrreducibleFamily
      (UnitarizabilityContinuation.fixedMatrix μ A.isSmooth hK e A.representation) :=
  ⟨fun h => UnitarizabilityContinuation.fixedMatrix_isIrreducible μ e h,
    isIrreducible_of_fixedMatrix μ A K hK e hdet⟩

end Langlands.Plancherel.CompactFixedFamilyOpenness

namespace Langlands.Plancherel

/-- The exact compact-fixed family openness proposition. -/
theorem compactFixedFamilyOpenness.{uX,uG,uV,un} :
    CompactFixedFamilyOpennessStatement.{uX,uG,uV,un} := by
  intro X _ G _ _ _ _ _ μ _ A K hK n _ e hN hdet hcont
  let (x : X) : Nontrivial (A x) := hN x
  have h := finiteMatrixIrreducibilityOpenness X G n
    (fun x => UnitarizabilityContinuation.fixedMatrix μ (A x).isSmooth hK (e x)
      (A x).representation) hcont
  have heq : {x | (A x).IsIrreducible} =
      {x | UnitarizabilityContinuation.IsIrreducibleFamily
        (UnitarizabilityContinuation.fixedMatrix μ (A x).isSmooth hK (e x)
          (A x).representation)} := by
    ext x
    exact CompactFixedFamilyOpenness.isIrreducible_iff_fixedMatrix μ (A x) K hK (e x) (hdet x)
  rwa [← heq] at h

end Langlands.Plancherel
