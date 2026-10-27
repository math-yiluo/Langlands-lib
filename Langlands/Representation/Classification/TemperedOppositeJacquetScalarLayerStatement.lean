import Langlands.Representation.Classification.DiscreteSeriesJacquetStatement

/-!
# Tempered scalar-character layers of the opposite Jacquet module

A derived GL_n prerequisite from Waldspurger 2003, III.2.2 and Lemma III.3.1.
This is a proposition definition.
-/

namespace Langlands
universe uF uV uW

/-- For an irreducible analytically tempered GL_n representation, every
subquotient of its actual opposite normalized Jacquet representation that has
an exact unitary scalar central character is analytically tempered modulo the
full Levi centre, for every Borel Haar measure. -/
def GLTemperedOppositeJacquetScalarLayerStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ B : GeneralLinear.BlockShape n,
      letI := T.leviTopologicalGroup B
      let M := B.Levi F.Carrier
      let Q := M ⧸ Subgroup.center M
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (W : Type uW) [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (GeneralLinear n F.Carrier) V)
        (ρ : Representation ℂ M W),
        Representation.IsIrreducible π → T.IsTempered π →
        UnitaryCentralCharacter ρ →
          let δ := (T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom
          let J : Representation ℂ M
              (Jacquet.Coinvariants π (B.oppositeUnipotentSubgroup F.Carrier)) :=
            (Jacquet.normalizedActionOfModulus π
            (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
            (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
            δ⁻¹).comp (B.leviEquiv F.Carrier).toMonoidHom
          (∃ S : Subrepresentation J,
            ∃ q : S.toRepresentation.IntertwiningMap ρ, Function.Surjective q) →
          ∀ [MeasurableSpace Q] [BorelSpace Q]
            (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ],
            IsTemperedModCenter ρ μ

end Langlands
