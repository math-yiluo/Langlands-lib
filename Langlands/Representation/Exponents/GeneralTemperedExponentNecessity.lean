import Langlands.Representation.Classification.ProductLeviTemperedExponentNecessityProof
import Langlands.Representation.Classification.ProductLeviTemperedFactorizationAdapter
import Langlands.Representation.Classification.InverseTransposeAnalyticProof
import Langlands.Representation.Classification.TemperedOppositeJacquetScalarLayerAssembly
import Langlands.Group.GL.OneBlockShape

noncomputable section

namespace Langlands.GeneralTemperedExponentNecessity

open GeneralLinear Geometric ProductLeviNecessity

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The published analytic helper lemmas bound a general tempered source. -/
theorem upperBound {n : ℕ} (hn : 0 < n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F.Carrier) V)
    (htemp : T.IsTempered π) (B : BlockShape n)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (hχ : T.IsJacquetExponent B π χ)
    (a : Fin B.length → F.Carrierˣ)
    (ha : Monotone fun i => T.normalizedAbs (a i : F.Carrier)) :
    ‖(χ a : ℂ)‖ ≤ 1 := by
  let := T.topology
  let C := CuspidalSupport.LeviAdmissibility.oneBlock n hn
  have := T.generalLinearTopologicalGroup n
  have := T.leviTopologicalGroup C
  let e := ScalarLayer.oneBlockLeviEquiv T hn
  let σ : Representation ℂ (C.Levi F.Carrier) V := π.comp e.toMonoidHom
  have hVne : Nontrivial V := by
    obtain ⟨k, y, hy, -⟩ := (isGeneralizedEigencharacter_iff _ _).mp hχ.2
    obtain ⟨x, hx⟩ := B.jacquetMk_surjective π y
    refine ⟨⟨x, 0, ?_⟩⟩
    intro h
    apply hy
    rw [← hx, h, map_zero]
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  obtain ⟨ν, hν⟩ := T.exists_isHaarMeasure_centralQuotient n
  let mQ : MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) := borel _
  have bQ : BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) := ⟨rfl⟩
  let μ := ν.map (centralQuotientCongr e).symm
  have hσtemp : IsTemperedModCenter σ μ :=
    isTemperedModCenter_comp_continuousMulEquiv π e μ (htemp _)
  have hcore :
      ∀ (D : BlockRefinement C)
        (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
        IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) →
        IsGeneralizedEigencharacter
          ((T.normalizedRefinedJacquet C D σ).comp
            ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
              ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
        ∀ b : Fin (C.flatten D).length → F.Carrierˣ,
          (∀ j : Fin C.length, Monotone (fun i : Fin (D j).length =>
            T.normalizedAbs (b (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier))) →
          ‖(ψ b : ℂ)‖ ≤ 1 := by
    intro D ψ hopen hgen b hb
    exact norm_le_one_of_test T C D ψ hopen
      (fun j k _ _ => norm_le_one_of_diagonal T C μ σ hσtemp D ψ hgen _
        (testScalars_isWeaklyContracting T C D j k) j _
        (testScalars_blockScalar_same T C D j k)
        (testScalars_refinedLeviModulus T C D j k))
      (fun j => norm_le_one_of_mem_center T C μ σ hσtemp D ψ hgen _
        (testScalars_full_isWeaklyContracting T C D j (-1))
        (testScalars_full_mem_center T C D j (-1))
        (testScalars_full_refinedLeviModulus T C D j (-1)))
      b hb
  obtain ⟨hσadm, c, -⟩ := hσtemp
  let ω : (Fin C.length → F.Carrierˣ) →* ℂˣ :=
    c.character.comp (C.blockScalarToCenter F.Carrier)
  have hω : Classification.HasScalarCharacter σ (C.blockScalarLevi F.Carrier) ω :=
    fun b x => c.acts (C.blockScalarToCenter F.Carrier b) x
  have hunit : ∀ b, ‖(ω b : ℂ)‖ = 1 := fun b => c.norm_eq_one _
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  have hωopen : IsOpen (ω.ker : Set (Fin C.length → F.Carrierˣ)) :=
    Classification.HasScalarCharacter.isOpen_ker hω
      (ProductLeviTemperedFactorization.continuous_blockScalarLevi C F.Carrier) hσadm.1
  let i : Fin C.length := ⟨0, Nat.one_pos⟩
  have hD : ∀ j, j ≠ i → ((fun _ => B : BlockRefinement C) j).length = 1 :=
    fun j hj => absurd (Fin.ext (Nat.lt_one_iff.mp j.isLt)) hj
  exact ProductLeviTemperedFactorization.jacquetExponent_bound_of_core T C σ
    ω hω hunit hωopen hcore i π LinearMap.id LinearMap.id
    (fun _ => rfl)
    (fun h x => by
      change π h x = π ((Pi.mulSingle i h : C.Levi F.Carrier) i) x
      rw [Pi.mulSingle_eq_same])
    (fun _ _ _ => rfl) (fun _ => B) hD χ hχ a ha

end Langlands.GeneralTemperedExponentNecessity
