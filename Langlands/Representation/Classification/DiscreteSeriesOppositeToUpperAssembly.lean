import Langlands.Representation.Classification.DiscreteSeriesOppositeToUpperStatement
import Langlands.Representation.Classification.OppositeReversalSemisimple
import Langlands.Representation.Classification.OppositeJacquetReciprocity
import Langlands.Representation.Classification.LeviDiscreteSeriesTemperedProof
import Langlands.Representation.Classification.TemperedDiscreteSeriesIsotypicStatement
import Langlands.Representation.Classification.TemperedOppositeJacquetScalarLayerStatement
import Langlands.Representation.Parabolic.SecondAdjointnessStatement
import Langlands.Representation.Parabolic.IrreducibleOppositeJacquetFiniteLengthStatement
import Langlands.Representation.ScalarSubReduction

/-!
# Conditional assembly of the same-sigma opposite-to-upper comparison

The target proposition follows from five separately stated propositions:
tempered upper induction, standard second adjointness, the discrete-series
isotypic projector, temperedness of scalar layers of the opposite Jacquet
module, and finite length of that Jacquet module. All five are explicit
hypotheses of the theorem below; none of them is proved here.
-/

noncomputable section

namespace Langlands

universe uF uV uW

/-- The same-sigma opposite-to-upper comparison, conditional on the five named
propositions. -/
theorem glTemperedDiscreteSeriesOppositeToUpper_of
    (h1 : GLTemperedInductionStatement.{uF, uW})
    (h2 : Parabolic.StandardSecondAdjointnessClause.{uF, uW, uV})
    (h3 : GLTemperedDiscreteSeriesIsotypicStatement.{uF, uV, uW})
    (h4 : GLTemperedOppositeJacquetScalarLayerStatement.{uF, uV, uV})
    (h5 : Parabolic.IrreducibleOppositeJacquetFiniteLengthStatement.{uF, uV}) :
    GLTemperedDiscreteSeriesOppositeToUpperStatement.{uF, uV, uW} := by
  intro p _ F T
  let := T.topology
  intro n hn B
  let := T.leviTopologicalGroup B
  intro M Q _ _ μ _ V _ _ W _ _ π σ hπ hπt hσ hσSI hj
  have hσt : IsTemperedModCenter σ μ :=
    glLeviDiscreteSeriesTempered p F T n hn B μ W σ hσ hσSI
  refine ⟨isSemisimple_normalizedOppositeParabolicInduced_of_temperedInduction
    h1 T hn B μ σ hσ hσt, ?_⟩
  let := T.generalLinearTopologicalGroup n
  have hπadm : IsAdmissible π := hπt.isAdmissible
  have hσadm : IsAdmissible σ := hσSI.1
  obtain ⟨cσ, -⟩ := hσSI.2
  let J := OppositeSupport.jacquetAction T B π
  -- The embedding into opposite induction gives an irreducible quotient of `J`.
  have hA : ∃ A : J.IntertwiningMap σ, Function.Surjective A :=
    (OppositeSupport.quotient_iff_embedding T B π σ hπadm.1 hπ hσ).mpr hj
  have hfin : IsFiniteLength (MonoidAlgebra ℂ M) J.asModule :=
    h5 p F T n hn B V π hπ hπadm
  -- On a subrepresentation of `J` with the central character of `σ`, the
  -- isotypic projector turns a quotient `σ` into a subrepresentation.
  have hscalar : ∀ {U : Type uV} [AddCommGroup U] [Module ℂ U]
      (τ : Representation ℂ M U) (i : τ.IntertwiningMap J),
      Function.Injective i →
      (∀ (z : Subgroup.center M) u, τ z u = (cσ.character z : ℂ) • u) →
      (∃ q : τ.IntertwiningMap σ, Function.Surjective q) →
      ∃ f : σ.IntertwiningMap τ, Function.Injective f := by
    intro U _ _ τ i hi hτχ hq
    obtain ⟨q, hqs⟩ := hq
    let cτ : UnitaryCentralCharacter τ :=
      { character := cσ.character
        isOpen_ker := cσ.isOpen_ker
        norm_eq_one := cσ.norm_eq_one
        acts := hτχ }
    let e : U ≃ₗ[ℂ] i.range.toSubmodule := LinearEquiv.ofInjective i.toLinearMap hi
    let q' : i.range.toRepresentation.IntertwiningMap τ :=
      { toLinearMap := e.symm.toLinearMap
        isIntertwining' g := by
          ext x
          obtain ⟨y, rfl⟩ := e.surjective x
          apply e.injective
          apply Subtype.ext
          change ((e (e.symm (i.range.toRepresentation g (e y))) : _) :
              Jacquet.Coinvariants π (B.oppositeUnipotentSubgroup F.Carrier)) =
            ((e (τ g (e.symm (e y))) : _) :
              Jacquet.Coinvariants π (B.oppositeUnipotentSubgroup F.Carrier))
          rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
          change J g (i y) = i (τ g y)
          exact (Representation.IntertwiningMap.isIntertwining _ _ i g y).symm }
    have hτt : IsTemperedModCenter τ μ :=
      h4 p F T n hn B V U π τ hπ hπt cτ ⟨i.range, q', e.symm.surjective⟩ μ
    obtain ⟨P, hPP, hrange, hker⟩ :=
      h3 p F T n hn B μ U W τ σ cτ cσ hτt hσ hσSI rfl
    exact ScalarSubReduction.exists_injective_of_isotypicProjector hσ P hPP hrange hker q hqs
  obtain ⟨f, hf⟩ := exists_injective_of_scalarCentralSubs J σ
    (fun z => (cσ.character z : ℂ)) hfin hσ cσ.acts hscalar hA
  -- Second adjointness turns `σ ↪ J` into a nonzero map from upper induction.
  obtain ⟨E, -, -⟩ := h2 p F T n hn B
  let E0 := E (Rep.of σ) (Rep.of π) hσadm hπadm
  let g : (T.normalizedParabolicInduced B σ).IntertwiningMap π := E0.symm f
  have hW : Nontrivial W := by
    let := hσ
    have : IsSimpleModule (MonoidAlgebra ℂ M) σ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
    have : Nontrivial σ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ M) σ.asModule
    exact σ.asModuleEquiv.toEquiv.symm.nontrivial
  have hg0 : g ≠ 0 := by
    intro hg
    have hf0 : f = 0 := by
      have h := congrArg E0 hg
      rw [map_zero] at h
      exact (E0.apply_symm_apply f).symm.trans h
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    apply hw
    apply hf
    rw [hf0, map_zero]
    rfl
  have hgs : Function.Surjective g := by
    let := hπ
    exact (Representation.IsIrreducible.surjective_or_eq_zero g).resolve_right hg0
  -- Semisimplicity of upper induction splits the surjection.
  have hss := (h1 p F T n hn B μ W σ hσ hσt).2.1
  let : IsSemisimpleModule (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      (T.normalizedParabolicInduced B σ).asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp hss
  let G := Representation.IntertwiningMap.equivLinearMapAsModule _ _ g
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property G hgs
    (LinearMap.id : π.asModule →ₗ[MonoidAlgebra ℂ (GeneralLinear n F.Carrier)] π.asModule)
  let s' : π.IntertwiningMap (T.normalizedParabolicInduced B σ) :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm s
  refine ⟨s', fun v v' hvv' => ?_⟩
  have h (x : V) : g (s' x) = x :=
    congrArg (fun k : π.asModule →ₗ[MonoidAlgebra ℂ (GeneralLinear n F.Carrier)]
      π.asModule => k x) hs
  rw [← h v, ← h v', hvv']

end Langlands
