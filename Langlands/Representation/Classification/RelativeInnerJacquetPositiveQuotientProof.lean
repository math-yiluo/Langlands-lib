import Langlands.Representation.Classification.RelativeInnerJacquetPositiveQuotientStatement
import Langlands.Representation.Classification.FineOppositeJacquetQuotientDetectionProof
import Langlands.Representation.CuspidalSupport.ConstituentUniverse
import Langlands.Representation.Parabolic.OppositeJacquetAdmissibilityProof
import Langlands.Representation.Parabolic.SecondAdjointnessProof
import Langlands.Representation.Filtration.MultiplicityTransportProof
import Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionProof

/-! Positivity of an actual inner Jacquet count detects the actual inner quotient. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW uK uG uH uA uD

namespace RelativeInnerJacquetPositiveQuotientProof

/-- A positive supplied series count gives an actual invariant-subspace quotient. -/
private theorem occurrence_of_positive
    {k : Type uK} [Field k] {G : Type uG} [Monoid G]
    {A : Rep.{uA} k G} {D : Rep.{uD} k G} {m : ℕ}
    (hm : HasJordanHolderMultiplicity A D m) (hpos : 0 < m) :
    ∃ U : Subrepresentation A.ρ,
      ∃ q : U.toRepresentation.IntertwiningMap D.ρ, Function.Surjective q := by
  obtain ⟨l, s, -, hcount⟩ := hm
  have hcard : 0 < Nat.card
      {i : Fin l // Nonempty ((s.gradedRepresentation i).ρ.Equiv D.ρ)} := by
    change 0 < s.factorMultiplicity D
    rw [hcount]
    exact hpos
  obtain ⟨⟨i, ⟨e⟩⟩⟩ := (Nat.card_pos_iff.mp hcard).1
  refine ⟨s.subrepresentation i.succ,
    e.toIntertwiningMap.comp (s.gradedProjection i).hom, ?_⟩
  exact e.surjective.comp (s.gradedProjection_surjective i)

/-- Pulling a map along a group equivalence keeps its underlying linear map. -/
private def pullMap
    {k : Type uK} [Field k] {G : Type uG} [Group G]
    {H : Type uH} [Group H] (e : H ≃* G)
    {A : Rep.{uA} k G} {D : Rep.{uD} k G}
    (f : A.ρ.IntertwiningMap D.ρ) :
    Representation.IntertwiningMap (A.ρ.comp e.toMonoidHom)
      (D.ρ.comp e.toMonoidHom) where
  toLinearMap := f.toLinearMap
  isIntertwining' h := f.isIntertwining' (e h)

/-- The actual pulled Jacquet representation is admissible, so a cuspidal
factor of a supplied positive count embeds into it. -/
private theorem nonzero_map_of_positive
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B)
    (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier))
    (hωirr : Representation.IsIrreducible ω.ρ)
    (hωcusp : letI := T.topology; CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ)
    (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ)
    (μ : Rep.{uW} ℂ (B.Levi F.Carrier))
    (hμ : letI := T.topology; IsAdmissible μ.ρ)
    (m : ℕ)
    (hm : HasJordanHolderMultiplicity (innerJacquet T B S μ)
      (fineTwist T B S ω v₀ t) m)
    (hpos : 0 < m) :
    ∃ f : (fineTwist T B S ω v₀ t).ρ.IntertwiningMap
      (innerJacquet T B S μ).ρ, f ≠ 0 := by
  let := T.topology
  let τ := fineTwist T B S ω v₀ t
  let J := innerJacquet T B S μ
  let e := flattenedLeviEquiv F.Carrier B S
  let A := Rep.of (J.ρ.comp e.toMonoidHom)
  let α := Rep.of (T.leviRealPowerTwist (B.flatten S)
    (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ)
  have hA : IsAdmissible A.ρ :=
    Parabolic.flattenedRefinedOppositeJacquetAdmissibility p F T n B S μ μ.ρ hμ
  have hreg := fineTwistIrreducibleAdmissible p F T n B S ω hωirr hωcusp v₀ t
  have hαirr : Representation.IsIrreducible α.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff (B.flatten S) _ ω.ρ).mpr hωirr
  have hαcusp : CuspidalSupport.IsLeviCuspidal (B.flatten S) α.ρ := hreg.2.2
  have hpull : HasJordanHolderMultiplicity A
      (Rep.of (τ.ρ.comp e.toMonoidHom)) m :=
    (groupEquivJordanHolderMultiplicityTransport ℂ
      (refinedLevi F.Carrier B S) ((B.flatten S).Levi F.Carrier)
      e J τ m).mp hm
  have hαcount : HasJordanHolderMultiplicity A α m :=
    (equivJordanHolderMultiplicityTransport ℂ ((B.flatten S).Levi F.Carrier)
      A A (Rep.of (τ.ρ.comp e.toMonoidHom)) α
      (Representation.Equiv.refl A.ρ)
      (MultiplicityTransportProof.doublePullEquiv e.symm α.ρ) m).mp hpull
  obtain ⟨i, hi⟩ :=
    (CuspidalSupport.leviCuspidalConstituent_maps F T (B.flatten S) A α
      hA hαirr hαcusp (occurrence_of_positive hαcount hpos)).1
  let ip := pullMap e.symm i
  let f : τ.ρ.IntertwiningMap J.ρ :=
    (MultiplicityTransportProof.doublePullEquiv e J.ρ).toIntertwiningMap.comp ip
  have hf : Function.Injective f :=
    (MultiplicityTransportProof.doublePullEquiv e J.ρ).injective.comp hi
  let := hreg.1
  have : Nontrivial τ :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (refinedLevi F.Carrier B S)) τ.ρ.asModule
  refine ⟨f, ?_⟩
  intro hzero
  obtain ⟨x, hx⟩ := exists_ne (0 : τ)
  apply hx
  apply hf
  rw [hzero]
  rfl

end RelativeInnerJacquetPositiveQuotientProof

/-- Every supplied actual inner Jacquet count is positive exactly when the
matching actual inner induction has the specified irreducible quotient. -/
theorem glRelativeInnerJacquetPositiveQuotient :
    GLRelativeInnerJacquetPositiveQuotientStatement.{uF, uV, uW} := by
  intro p _ F T
  let := T.topology
  intro n hn B S ω hωirr hωcusp v₀ t τ μ hμirr hμ m hm
  have hreg := fineTwistIrreducibleAdmissible p F T n B S ω hωirr hωcusp v₀ t
  have hdet := (fineOppositeJacquetQuotientDetection.{uF, uV, uW, uW}
    Parabolic.normalizedSecondAdjointness.1 Parabolic.normalizedSecondAdjointness.2
    p F T n hn B S ω hωirr hωcusp v₀ t).1 μ hμ hμirr
  constructor
  · intro hpos
    exact hdet.mp
      (RelativeInnerJacquetPositiveQuotientProof.nonzero_map_of_positive
        T B S ω hωirr hωcusp v₀ t μ hμ m hm hpos)
  · intro hq
    exact SimpleMapMultiplicityDetectionProof.positive_of_simple_map
      hreg.1 m hm (Or.inl (hdet.mpr hq))

end Langlands
