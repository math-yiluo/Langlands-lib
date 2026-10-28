import Langlands.Representation.Classification.FineOppositeJacquetQuotientDetectionStatement
import Langlands.Representation.Classification.FineTwistRegularityProof
import Langlands.Representation.Parabolic.FlattenedOppositeJacquetComparisonProof

/-! Conditional detection of actual fine induction quotients by nonzero
opposite Jacquet intertwiners, from the two explicit second-adjointness
premises of the target statement. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uG uH uA uB uC uF uV uW uZ

namespace FineOppositeJacquetQuotientDetection

section Algebra

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  {A : Type uA} {B : Type uB} {C : Type uC}
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C]

-- The two transport constructions follow Worker 435's shared assembly draft.
private def homPostcompEquiv (ρ : Representation ℂ G A)
    {σ : Representation ℂ G B} {τ : Representation ℂ G C} (e : σ.Equiv τ) :
    (ρ.IntertwiningMap σ) ≃ₗ[ℂ] (ρ.IntertwiningMap τ) where
  toFun f := e.toIntertwiningMap.comp f
  invFun f := e.symm.toIntertwiningMap.comp f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  left_inv f := by ext x; exact e.symm_apply_apply (f x)
  right_inv f := by ext x; exact e.apply_symm_apply (f x)

private def homChangeGroup (e : G ≃* H) (ρ : Representation ℂ G A)
    (σ : Representation ℂ H B) :
    (ρ.IntertwiningMap (σ.comp e.toMonoidHom)) ≃ₗ[ℂ]
      Representation.IntertwiningMap (ρ.comp e.symm.toMonoidHom) σ where
  toFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' h := by
        simpa using f.isIntertwining' (e.symm h) }
  invFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' g := by
        simpa using f.isIntertwining' (e g) }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

private theorem nonzero_iff_surjective (ρ : Representation ℂ G A)
    (π : Representation ℂ G B) (hπ : Representation.IsIrreducible π) :
    (∃ f : ρ.IntertwiningMap π, f ≠ 0) ↔
      ∃ q : ρ.IntertwiningMap π, Function.Surjective q := by
  let := hπ
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf⟩
  · rintro ⟨q, hq⟩
    have : Nontrivial B :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
    refine ⟨q, ?_⟩
    intro hzero
    obtain ⟨w, hw⟩ := exists_ne (0 : B)
    obtain ⟨v, hv⟩ := hq w
    apply hw
    rw [hzero] at hv
    exact hv.symm

private theorem exists_nonzero_iff_of_equiv
    {X : Type*} {Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (E : X ≃ₗ[ℂ] Y) :
    (∃ x : X, x ≠ 0) ↔ ∃ y : Y, y ≠ 0 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨E x, fun hy => hx (E.map_eq_zero_iff.mp hy)⟩
  · rintro ⟨y, hy⟩
    exact ⟨E.symm y, fun hx => hy (E.symm.map_eq_zero_iff.mp hx)⟩

end Algebra

/-- The ambient criterion: the assumed standard clause on `B.flatten S`,
then the inverse flattened opposite-Jacquet comparison and change of group
along `flattenedLeviEquiv`. -/
private theorem ambientDetection {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (S : BlockRefinement B) (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier))
    (v : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ)
    (J : Rep.{uZ} ℂ (GeneralLinear n F.Carrier))
    (hstandard : Parabolic.StandardSecondAdjointnessClause.{uF, uV, uZ})
    (hω : letI := T.topology; IsAdmissible (T.leviRealPowerTwist (B.flatten S)
      (fun k => -v k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ))
    (hJ : letI := T.topology; IsAdmissible J.ρ)
    (hJirr : Representation.IsIrreducible J.ρ) :
    (∃ f : (fineTwist T B S ω v t).ρ.IntertwiningMap
      (T.normalizedComposedOppositeJacquet B S J.ρ), f ≠ 0) ↔
      ∃ q : (RelativeRecovery.fineAmbientInduced T B S ω v t).ρ.IntertwiningMap J.ρ,
        Function.Surjective q := by
  let := T.topology
  obtain ⟨Eout, -⟩ := hstandard p F T n hn (B.flatten S)
  obtain ⟨φ, -⟩ :=
    Parabolic.flattenedOppositeJacquetComparison.{uF, uF, uZ}.2 p F T n B S J
  let α := Rep.of (T.leviRealPowerTwist (B.flatten S)
    (fun k => -v k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ)
  let e := flattenedLeviEquiv F.Carrier B S
  let Etransport := (homPostcompEquiv α.ρ φ.symm).trans
    (homChangeGroup e α.ρ (T.normalizedComposedOppositeJacquet B S J.ρ))
  let E := (Eout α J hω hJ).trans Etransport
  exact (exists_nonzero_iff_of_equiv E).symm.trans
    (nonzero_iff_surjective _ J.ρ hJirr)

/-- The inner criterion: the assumed refined clause applied directly. -/
private theorem innerDetection {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (S : BlockRefinement B) (τ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
    (π : Rep.{uW} ℂ (B.Levi F.Carrier))
    (hrefined : Parabolic.RefinedSecondAdjointnessClause.{uF, uV, uW})
    (hτ : letI := T.topology; IsAdmissible τ.ρ)
    (hπ : letI := T.topology; IsAdmissible π.ρ)
    (hπirr : Representation.IsIrreducible π.ρ) :
    (∃ f : τ.ρ.IntertwiningMap
      (T.normalizedRefinedOppositeJacquet B S π.ρ), f ≠ 0) ↔
      ∃ q : (innerInduced T B S τ).ρ.IntertwiningMap π.ρ,
        Function.Surjective q := by
  let := T.topology
  obtain ⟨E, -⟩ := hrefined p F T n hn B S
  exact (exists_nonzero_iff_of_equiv (E τ π hτ hπ)).symm.trans
    (nonzero_iff_surjective _ π.ρ hπirr)

end FineOppositeJacquetQuotientDetection

/-- Assuming the standard and refined second-adjointness clauses, nonzero
intertwiners from the actual fine twist into the refined or composed opposite
Jacquet module detect surjections from the matching actual induction. The two
clauses are the statement's premises and are not proved here. -/
theorem fineOppositeJacquetQuotientDetection :
    FineOppositeJacquetQuotientDetectionStatement.{uF, uV, uW, uZ} := by
  intro hstandard hrefined p _ F T
  let := T.topology
  intro n hn B S ω hωirr hωcusp v t
  have hreg := fineTwistIrreducibleAdmissible p F T n B S ω hωirr hωcusp v t
  exact ⟨fun π hπ hπirr =>
    FineOppositeJacquetQuotientDetection.innerDetection T hn B S _ π hrefined
      hreg.2.1 hπ hπirr,
    fun J hJ hJirr =>
    FineOppositeJacquetQuotientDetection.ambientDetection T hn B S ω v t J hstandard
      hreg.2.2.1 hJ hJirr⟩

end Langlands
