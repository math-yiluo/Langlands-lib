import Langlands.Representation.Classification.DiscreteSeriesOppositeToUpperStatement
import Langlands.Representation.Classification.DiscreteSeriesInductionForms
import Langlands.Representation.Classification.OppositeJacquetReciprocity
import Langlands.Representation.Classification.TemperedDiscreteSeriesIsotypicProof
import Langlands.Representation.Classification.TemperedOppositeJacquetScalarLayerProof
import Langlands.Representation.Parabolic.SecondAdjointnessProof
import Langlands.Representation.Parabolic.IrreducibleOppositeJacquetFiniteLengthProof
import Langlands.Representation.ScalarSubReduction

/-!
# Same-sigma opposite-to-upper discrete-series induction comparison (proof)

Both normalized inductions of the square-integrable `σ` are semisimple. An
opposite-induction embedding of `π` gives a quotient `σ` of the opposite
Jacquet module `J` of `π`; the isotypic projectors on scalar layers of `J`
turn it into a subrepresentation `σ ↪ J`, second adjointness turns that into a
nonzero map from upper induction onto `π`, and upper semisimplicity splits it.
-/

noncomputable section

namespace Langlands

universe uF uV uW

/-- For the same discrete-series representation of the actual product Levi,
an opposite-induction embedding of an irreducible tempered representation
implies opposite semisimplicity and an upper-induction embedding. -/
theorem glTemperedDiscreteSeriesOppositeToUpper :
    GLTemperedDiscreteSeriesOppositeToUpperStatement.{uF, uV, uW} := by
  intro p _ F T
  let := T.topology
  intro n hn B
  let := T.leviTopologicalGroup B
  intro M Q _ _ μ _ V _ _ W _ _ π σ hπ hπt hσ hσSI hj
  have hboth := isSemisimple_bothInduced_of_squareIntegrable.{uF, uW} T B hn μ σ hσ hσSI
  refine ⟨hboth.2, ?_⟩
  let := T.generalLinearTopologicalGroup n
  have hπadm : IsAdmissible π := hπt.isAdmissible
  have hσadm : IsAdmissible σ := hσSI.1
  obtain ⟨cσ, -⟩ := hσSI.2
  let J := OppositeSupport.jacquetAction T B π
  -- The embedding into opposite induction gives an irreducible quotient of `J`.
  have hA : ∃ A : J.IntertwiningMap σ, Function.Surjective A :=
    (OppositeSupport.quotient_iff_embedding T B π σ hπadm.1 hπ hσ).mpr hj
  have hfin : IsFiniteLength (MonoidAlgebra ℂ M) J.asModule :=
    Parabolic.irreducibleOppositeJacquetFiniteLength.{uF, uV} p F T n hn B V π hπ hπadm
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
      glTemperedOppositeJacquetScalarLayer.{uF, uV, uV}
        p F T n hn B V U π τ hπ hπt cτ ⟨i.range, q', e.symm.surjective⟩ μ
    obtain ⟨P, hPP, hrange, hker⟩ :=
      glTemperedDiscreteSeriesIsotypic.{uF, uV, uW}
        p F T n hn B μ U W τ σ cτ cσ hτt hσ hσSI rfl
    exact ScalarSubReduction.exists_injective_of_isotypicProjector hσ P hPP hrange hker q hqs
  obtain ⟨f, hf⟩ := exists_injective_of_scalarCentralSubs J σ
    (fun z => (cσ.character z : ℂ)) hfin hσ cσ.acts hscalar hA
  -- Second adjointness turns `σ ↪ J` into a nonzero map from upper induction.
  obtain ⟨E, -, -⟩ := Parabolic.normalizedSecondAdjointness.{uF, uW, uV}.1 p F T n hn B
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
  let : IsSemisimpleModule (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      (T.normalizedParabolicInduced B σ).asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp hboth.1
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
