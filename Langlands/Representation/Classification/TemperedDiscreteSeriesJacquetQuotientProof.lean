import Langlands.Representation.Classification.DiscreteSeriesJacquetStatement
import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Langlands.Representation.Classification.TemperedDiscreteSeriesIsotypicProof
import Langlands.Representation.Classification.TemperedOppositeJacquetScalarLayerProof
import Langlands.Representation.Parabolic.IrreducibleOppositeJacquetFiniteLengthProof
import Langlands.Representation.IsotypicQuotient
import Langlands.Representation.ScalarQuotientReduction

/-!
# Discrete-series opposite Jacquet quotient criterion

Finite-length descent reduces to exact scalar-central quotients. Their analytic
temperedness and the discrete-series isotypic projector yield actual quotients.
-/

noncomputable section

namespace Langlands

universe uF uV uW

private def inclusion {G : Type*} [Monoid G] {V : Type*}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (S : Subrepresentation ρ) : S.toRepresentation.IntertwiningMap ρ :=
  { toLinearMap := S.toSubmodule.subtype
    isIntertwining' _ := rfl }

private theorem occurrence_of_surjection {G : Type*} [Monoid G]
    {V : Type*} {W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (p : ρ.IntertwiningMap σ) (hp : Function.Surjective p) :
    ∃ S : Subrepresentation ρ,
      ∃ q : S.toRepresentation.IntertwiningMap σ, Function.Surjective q := by
  refine ⟨⊤, p.comp (inclusion ρ ⊤), fun w => ?_⟩
  obtain ⟨v, hv⟩ := hp w
  exact ⟨⟨v, trivial⟩, hv⟩

/-- An irreducible discrete-series subquotient of the actual opposite normalized
Jacquet module of an irreducible tempered representation is an actual quotient,
and every such quotient is a subquotient. -/
theorem glTemperedDiscreteSeriesJacquetQuotient :
    GLTemperedDiscreteSeriesJacquetQuotientStatement.{uF, uV, uW} := by
  intro p _ F T
  let := T.topology
  intro n hn B
  let := T.leviTopologicalGroup B
  dsimp only
  intro _ _ μ _ V _ _ W _ _ π σ hπ hπtemp hσ hσsq
  let J := (CuspidalJacquetMultiplicity.oppositeJacquet T B (Rep.of π)).ρ
  change
    (∃ S : Subrepresentation J,
      ∃ q : S.toRepresentation.IntertwiningMap σ, Function.Surjective q) ↔
    ∃ q : J.IntertwiningMap σ, Function.Surjective q
  constructor
  · intro hocc
    obtain ⟨cσ, _hcσ⟩ := hσsq.2
    have hfin : IsFiniteLength (MonoidAlgebra ℂ (B.Levi F.Carrier)) J.asModule :=
      Parabolic.irreducibleOppositeJacquetFiniteLength
        p F T n hn B V π hπ hπtemp.isAdmissible
    have hscalar : ∀ {U : Type uV} [AddCommGroup U] [Module ℂ U]
        (τ : Representation ℂ (B.Levi F.Carrier) U) (q : J.IntertwiningMap τ),
        Function.Surjective q →
        (∀ (z : Subgroup.center (B.Levi F.Carrier)) u,
          τ z u = (cσ.character z : ℂ) • u) →
        (∃ S : Subrepresentation τ,
          ∃ r : S.toRepresentation.IntertwiningMap σ, Function.Surjective r) →
        ∃ r : τ.IntertwiningMap σ, Function.Surjective r := by
      intro U _ _ τ q hq hτ hoccτ
      let cτ : UnitaryCentralCharacter τ :=
        { character := cσ.character
          isOpen_ker := cσ.isOpen_ker
          norm_eq_one := cσ.norm_eq_one
          acts := hτ }
      have hτtemp : IsTemperedModCenter τ μ :=
        glTemperedOppositeJacquetScalarLayer.{uF, uV, uV}
          p F T n hn B V U π τ hπ hπtemp cτ
          (occurrence_of_surjection q hq) μ
      obtain ⟨P, _hP, hrange, hker⟩ :=
        glTemperedDiscreteSeriesIsotypic.{uF, uV, uW}
          p F T n hn B μ U W τ σ cτ cσ hτtemp hσ hσsq rfl
      let r := quotientOfIsotypicRange hσ P hrange hker hoccτ
      exact ⟨r.val, r.property⟩
    let q := quotientOfScalarCentralQuotients J σ
      (fun z => (cσ.character z : ℂ)) hfin hσ cσ.acts hscalar hocc
    exact ⟨q.val, q.property⟩
  · rintro ⟨q, hq⟩
    exact occurrence_of_surjection q hq

end Langlands
