import Langlands.Representation.Classification.RelativeJacquetFiltrationMultiplicityStatement
import Langlands.Representation.Parabolic.OppositeJacquetFiltrationMultiplicityProof
import Langlands.Representation.Parabolic.InductionFiltration
import Langlands.Representation.Filtration.MultiplicityTransportProof

noncomputable section

open scoped BigOperators

namespace Langlands.RelativeJacquetFiltrationMultiplicityProof

open GeneralLinear Geometric Parabolic

universe uF uV uX

/-- Descend an actual ambient equivalence and its inverse to the normalized
composed opposite quotients. -/
def composedOppositeJacquetCongr
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {X : Type uX} [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (GeneralLinear n F.Carrier) X} (e : ρ.Equiv σ) :
    (T.normalizedComposedOppositeJacquet B S ρ).Equiv
      (T.normalizedComposedOppositeJacquet B S σ) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinearMap
      (T.normalizedComposedOppositeJacquetMap B S e.toIntertwiningMap).toLinearMap
      (T.normalizedComposedOppositeJacquetMap B S e.symm.toIntertwiningMap).toLinearMap
      (by
        apply LinearMap.ext
        intro x
        obtain ⟨w, rfl⟩ := composedOppositeJacquetMk_surjective B S σ x
        simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
          PadicField.TopologicalData.normalizedComposedOppositeJacquetMap_mk,
          Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.apply_symm_apply,
          LinearMap.id_apply])
      (by
        apply LinearMap.ext
        intro x
        obtain ⟨v, rfl⟩ := composedOppositeJacquetMk_surjective B S ρ x
        simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
          PadicField.TopologicalData.normalizedComposedOppositeJacquetMap_mk,
          Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.symm_apply_apply,
          LinearMap.id_apply]))
    (T.normalizedComposedOppositeJacquetMap B S e.toIntertwiningMap).isIntertwining'

end Langlands.RelativeJacquetFiltrationMultiplicityProof

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity
  RelativeJacquetFiltrationMultiplicityProof

universe uF uV uW

/-- Construct and decompose actual finite-series multiplicities across a
smooth coarse-Levi filtration for both relative opposite Jacquet functors. -/
theorem glRelativeJacquetFiltrationMultiplicity :
    GLRelativeJacquetFiltrationMultiplicityStatement.{uF, uV, uW} := by
  intro p hp F T n B S
  let := T.topology
  constructor
  · intro A hA l s τ m
    exact
      (Parabolic.normalizedOppositeJacquetFiltrationMultiplicity.{uF, uV, uW}
        p F T n B S).1 A A.ρ hA l s τ m
  · let := T.generalLinearTopologicalGroup n
    intro A hA l s τ m
    let t : ObjectRepFiltration (CuspidalJacquetMultiplicity.induced T B A) l :=
      Parabolic.normalizedInductionFiltration T B A.ρ s
    have hOut : IsSmooth (CuspidalJacquetMultiplicity.induced T B A).ρ :=
      T.isSmooth_normalizedParabolicInduced B A.ρ
    have h :=
      (Parabolic.normalizedOppositeJacquetFiltrationMultiplicity.{uF, max uF uV, uW}
        p F T n B S).2
        (CuspidalJacquetMultiplicity.induced T B A)
        (CuspidalJacquetMultiplicity.induced T B A).ρ hOut l t τ m
    have hGrade : ∀ (i : Fin l) (c : ℕ),
        HasJordanHolderMultiplicity
          (Rep.of (T.normalizedComposedOppositeJacquet B S
            (t.gradedRepresentation i).ρ)) τ c ↔
        HasJordanHolderMultiplicity
          (ambientJacquet T B S (s.gradedRepresentation i)) τ c := by
      intro i c
      let e := Parabolic.normalizedInductionFiltrationGradedEquiv T B A.ρ s i hA
      exact equivJordanHolderMultiplicityTransport ℂ (refinedLevi F.Carrier B S)
        (Rep.of (T.normalizedComposedOppositeJacquet B S
          (t.gradedRepresentation i).ρ))
        (ambientJacquet T B S (s.gradedRepresentation i)) τ τ
        (composedOppositeJacquetCongr T B S e) (Representation.Equiv.refl _) c
    refine h.trans ?_
    constructor
    · rintro ⟨counts, H, hc⟩
      exact ⟨counts, fun i => (hGrade i (counts i)).mp (H i), hc⟩
    · rintro ⟨counts, H, hc⟩
      exact ⟨counts, fun i => (hGrade i (counts i)).mpr (H i), hc⟩

end Langlands
