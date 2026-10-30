import Langlands.Representation.Classification.TemperedExponentStatement
import Langlands.Representation.Classification.TemperedExponentEdgeProof
import Langlands.Representation.Classification.TemperedOppositeJacquetScalarLayerAssembly
import Langlands.Representation.Classification.ProductLeviTemperedExponentNecessityProof
import Langlands.Representation.Classification.OneBlockUpperExponentProof

/-!
# The analytic tempered exponent criterion for `GL_n`

The published general product-Levi necessity and sufficiency theorems are
transported through the one-block Levi equivalence. The edge theorem handles
zero carriers and constructs the unitary central-character datum.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal

namespace Langlands

open GeneralLinear Geometric ProductLeviChamber ProductLeviNecessity

universe uF uV

section Necessity

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (C : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The published necessity helpers do not require irreducibility. -/
private theorem upperExponentHypothesis_of_tempered :
    letI := T.topology
    ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      (μ : MeasureTheory.Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
      [μ.IsHaarMeasure] (σ : Representation ℂ (C.Levi F.Carrier) V),
      IsTemperedModCenter σ μ → UpperExponentHypothesis T C σ := by
  let := T.topology
  intro _ _ μ _ σ htemp D ψ hψ hgen a ha
  exact norm_le_one_of_test T C D ψ hψ
    (fun j k _ _ => norm_le_one_of_diagonal T C μ σ htemp D ψ hgen _
      (testScalars_isWeaklyContracting T C D j k) j _
      (testScalars_blockScalar_same T C D j k)
      (testScalars_refinedLeviModulus T C D j k))
    (fun j => norm_le_one_of_mem_center T C μ σ htemp D ψ hgen _
      (testScalars_full_isWeaklyContracting T C D j (-1))
      (testScalars_full_mem_center T C D j (-1))
      (testScalars_full_refinedLeviModulus T C D j (-1)))
    a ha

/-- General GL necessity, using the one-block product Levi and the public factor adapter. -/
private theorem jacquet_bound_of_tempered [Nontrivial V] (hn : 0 < n)
    (π : Representation ℂ (GeneralLinear n F.Carrier) V)
    (htemp : T.IsTempered π) (B : BlockShape n)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ) (hχ : T.IsJacquetExponent B π χ)
    (a : Fin B.length → F.Carrierˣ)
    (ha : Monotone (fun i => T.normalizedAbs (a i : F.Carrier))) :
    ‖(χ a : ℂ)‖ ≤ 1 := by
  let := T.topology
  let C := CuspidalSupport.LeviAdmissibility.oneBlock n hn
  have := T.generalLinearTopologicalGroup n
  have := T.leviTopologicalGroup C
  let e := ScalarLayer.oneBlockLeviEquiv T hn
  let σ : Representation ℂ (C.Levi F.Carrier) V := π.comp e.toMonoidHom
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  obtain ⟨ν, hν⟩ := T.exists_isHaarMeasure_centralQuotient n
  let mQ : MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) :=
    borel _
  have bQ : BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) := ⟨rfl⟩
  let μ := ν.map (centralQuotientCongr e).symm
  have hσtemp : IsTemperedModCenter σ μ :=
    isTemperedModCenter_comp_continuousMulEquiv π e μ (htemp _)
  have hcore := upperExponentHypothesis_of_tempered T C μ σ hσtemp
  obtain ⟨hσadm, c, -⟩ := hσtemp
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  have hωopen : IsOpen ((ScalarLayer.blockScalarCharacter C c).ker :
      Set (Fin C.length → F.Carrierˣ)) :=
    Classification.HasScalarCharacter.isOpen_ker
      (ScalarLayer.hasScalarCharacter_blockScalarCharacter C c)
      (ProductLeviTemperedFactorization.continuous_blockScalarLevi C F.Carrier) hσadm.1
  let i : Fin C.length := ⟨0, Nat.one_pos⟩
  have hD : ∀ j, j ≠ i → ((fun _ => B : BlockRefinement C) j).length = 1 :=
    fun j hj => absurd (Fin.ext (Nat.lt_one_iff.mp j.isLt)) hj
  exact ProductLeviTemperedFactorization.jacquetExponent_bound_of_core T C σ
    (ScalarLayer.blockScalarCharacter C c)
    (ScalarLayer.hasScalarCharacter_blockScalarCharacter C c)
    (ScalarLayer.norm_blockScalarCharacter C c) hωopen hcore i π LinearMap.id LinearMap.id
    (fun _ => rfl)
    (fun h x => by
      change π h x = π ((Pi.mulSingle i h : C.Levi F.Carrier) i) x
      rw [Pi.mulSingle_eq_same])
    (fun _ _ _ => rfl) (fun _ => B) hD χ hχ a ha

end Necessity

/-- Analytic temperedness is equivalent to the weak upper Jacquet-exponent
bounds for an admissible scalar-character representation of `GL_n(F)`. -/
theorem glTemperedExponentCriterion : GLTemperedExponentCriterionStatement.{uF, uV} := by
  intro p _ F T n hn V _ _ π ω hadm hω
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · let := hV
    obtain ⟨htemp, hnone⟩ := glTemperedExponentEdge.1 p F T n V π
    exact ⟨fun _ B χ hχ => (hnone B χ hχ).elim, fun _ => htemp⟩
  · let := hV
    constructor
    · intro htemp B χ hχ a ha
      exact jacquet_bound_of_tempered T hn π htemp B χ hχ a ha
    · intro hbound
      let := T.topology
      have := T.generalLinearTopologicalGroup n
      let C := CuspidalSupport.LeviAdmissibility.oneBlock n hn
      have := T.leviTopologicalGroup C
      let e := ScalarLayer.oneBlockLeviEquiv T hn
      let σ : Representation ℂ (C.Levi F.Carrier) V := π.comp e.toMonoidHom
      obtain ⟨-, -, ⟨c⟩⟩ := glTemperedExponentEdge.2 p F T n hn V π ω hadm.1 hω hbound
      have hσadm : IsAdmissible σ := isAdmissible_comp_continuousMulEquiv π e hadm
      have hcore : UpperExponentHypothesis T C σ :=
        glOneBlockUpperExponent p F T n hn V π hadm hbound
      let mC : MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) :=
        borel _
      have bC : BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) :=
        ⟨rfl⟩
      let := T.centralQuotientMeasurableSpace n
      have := T.centralQuotientBorelSpace n
      intro μ hμ
      have hσtemp := ScalarLayer.tempered_of_upperExponentHypothesis T C σ hσadm
        (c.compContinuousMulEquiv e) hcore (μ.map (centralQuotientCongr e.symm))
      have hπtemp := isTemperedModCenter_comp_continuousMulEquiv σ e.symm μ hσtemp
      have heq : σ.comp e.symm.toMonoidHom = π := by
        ext g v
        change π (e (e.symm g)) v = π g v
        rw [e.apply_symm_apply]
      rwa [heq] at hπtemp

end Langlands
