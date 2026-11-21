import Langlands.Representation.RankinSelberg.FieldTransport.LocalFieldEpsilon
import Langlands.BaseChange.CuspidalSigmaLiftConductorLocalReduction
import Langlands.BaseChange.TraceAdditiveConductor

/-! # Additive conductors and trace characters under local-field isomorphisms -/

noncomputable section

set_option autoImplicit false

open scoped WithZero

universe u v u' v'

namespace Langlands.LocalFieldData

private theorem mem_additiveLattice_iff_neg_ord_le {K : Type*} [Field K] (T : LocalFieldData K)
    {x : K} (hx : x ≠ 0) (n : ℤ) :
    x ∈ T.additiveLattice n ↔ -T.ord x ≤ n := by
  have h0 : T.discreteValuation x ≠ 0 := T.discreteValuation.ne_zero_iff.mpr hx
  rw [T.mem_additiveLattice, ← WithZero.exp_log h0, WithZero.exp_le_exp, ord, neg_neg]

variable {F : Type u} {E : Type v} [Field F] [Field E]
  (TF : LocalFieldData F) (TE : LocalFieldData E) (σ : F ≃+* E)
  (hσ : @Continuous F E TF.topology TE.topology σ)
  (hσs : @Continuous E F TE.topology TF.topology σ.symm)

include hσ hσs in
/-- A bicontinuous field equivalence identifies the actual fractional ideals
`π^(-n) O` of the two fields. -/
theorem mem_additiveLattice_map_iff (n : ℤ) (x : F) :
    σ x ∈ TE.additiveLattice n ↔ x ∈ TF.additiveLattice n := by
  by_cases hx : x = 0
  · subst hx
    rw [map_zero]
    exact ⟨fun _ => (TF.additiveLattice n).zero_mem, fun _ => (TE.additiveLattice n).zero_mem⟩
  rw [mem_additiveLattice_iff_neg_ord_le TE ((map_ne_zero σ).mpr hx),
    mem_additiveLattice_iff_neg_ord_le TF hx, TF.ord_of_continuous_ringEquiv TE σ hσ hσs]

end Langlands.LocalFieldData

namespace Langlands.BaseChange

open HarmonicAnalysis (UnitaryAdditiveCharacter)

section Conductor

variable {F : Type u} [Field F] [TopologicalSpace F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]
  {F' : Type u'} [Field F'] [TopologicalSpace F'] [ValuativeRel F']
  [IsNonarchimedeanLocalField F']
  (σ : F ≃+* F') (hσ : Continuous σ) (hσs : Continuous σ.symm)

include hσ hσs in
/-- Tate's additive conductor `n(ψ)` is unchanged by pullback along a
bicontinuous field equivalence. -/
theorem additiveConductor_eq_of_continuous_ringEquiv
    (ψ : UnitaryAdditiveCharacter F) (ψ' : UnitaryAdditiveCharacter F')
    (hψ : ∀ x, ψ' (σ x) = ψ x) :
    (LocalFieldData.ofInstances F').additiveConductor ψ' =
      (LocalFieldData.ofInstances F).additiveConductor ψ := by
  let TF := LocalFieldData.ofInstances F
  let TF' := LocalFieldData.ofInstances F'
  have htriv (n : ℤ) : TF'.AdditiveTrivialAt ψ' n ↔ TF.AdditiveTrivialAt ψ n := by
    constructor
    · intro h x hx
      rw [← hψ]
      exact h (σ x) ((TF.mem_additiveLattice_map_iff TF' σ hσ hσs n x).mpr hx)
    · intro h y hy
      obtain ⟨x, rfl⟩ := σ.surjective y
      rw [hψ]
      exact h x ((TF.mem_additiveLattice_map_iff TF' σ hσ hσs n x).mp hy)
  apply le_antisymm
  · exact (TF.additiveTrivialAt_iff_le_conductor ψ _).mp
      ((htriv _).mp ((TF'.additiveTrivialAt_iff_le_conductor ψ' _).mpr le_rfl))
  · exact (TF'.additiveTrivialAt_iff_le_conductor ψ' _).mp
      ((htriv _).mpr ((TF.additiveTrivialAt_iff_le_conductor ψ _).mpr le_rfl))

end Conductor

/-- Traces correspond under field equivalences compatible with the two
algebra maps. -/
theorem trace_map_of_ringEquiv {F : Type u} {E : Type v} {F' : Type u'} {E' : Type v'}
    [Field F] [Field E] [Field F'] [Field E'] [Algebra F E] [Algebra F' E']
    (σF : F ≃+* F') (σE : E ≃+* E')
    (hcomm : ∀ x : F, σE (algebraMap F E x) = algebraMap F' E' (σF x)) (y : E) :
    Algebra.trace F' E' (σE y) = σF (Algebra.trace F E y) := by
  rw [Algebra.trace_eq_of_equiv_equiv σF σE (RingHom.ext fun x => (hcomm x).symm) y,
    RingEquiv.apply_symm_apply]

section Trace

variable {F : Type u} [Field F] [TopologicalSpace F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]
  {E : Type v} [Field E] [TopologicalSpace E] [ValuativeRel E]
  [IsNonarchimedeanLocalField E] [Algebra F E]
  {F' : Type u'} [Field F'] [TopologicalSpace F'] [ValuativeRel F']
  [IsNonarchimedeanLocalField F']
  {E' : Type v'} [Field E'] [Algebra F' E']

/-- Characters pulled back from fields isomorphic to `F` and `E` satisfy the
trace-character condition when the target base character has conductor zero.
Continuity is needed only for the base-field equivalence; the conductor
`d` of the extension character then follows from the trace codifferent. -/
theorem traceEpsilonCharacterCondition_of_ringEquiv [IsModuleTopology F E]
    (σF : F ≃+* F') (hσF : Continuous σF) (hσFs : Continuous σF.symm) (σE : E ≃+* E')
    (hcomm : ∀ x : F, σE (algebraMap F E x) = algebraMap F' E' (σF x))
    {d : ℕ} (hd : IsDifferentExponent F E d)
    (ψF' : UnitaryAdditiveCharacter F')
    (hcond : (LocalFieldData.ofInstances F').additiveConductor ψF' = 0)
    (ψF : UnitaryAdditiveCharacter F) (ψE : UnitaryAdditiveCharacter E)
    (hψF : ∀ x, ψF x = ψF' (σF x))
    (hψE : ∀ y, ψE y = ψF' (Algebra.trace F' E' (σE y))) :
    TraceEpsilonCharacterCondition ψF ψE d := by
  have htrace (y : E) : ψE y = ψF (Algebra.trace F E y) := by
    rw [hψE, hψF, trace_map_of_ringEquiv σF σE hcomm]
  have hF : (LocalFieldData.ofInstances F).additiveConductor ψF = 0 := by
    rw [← additiveConductor_eq_of_continuous_ringEquiv σF hσF hσFs ψF ψF'
      (fun x => (hψF x).symm), hcond]
  exact ⟨htrace, hF, hd.additiveConductor_of_trace ψF ψE hF htrace⟩

end Trace

/-- Pulled back along field equivalences that commute with the algebra maps,
a conductor-zero base character and its trace character satisfy the trace
condition of the local conductor reduction. Only the base-field equivalence is
required to be bicontinuous. -/
def TraceCharacterTransportStatement : Prop :=
  ∀ (F : Type u) [Field F] [TopologicalSpace F] [ValuativeRel F]
    [IsNonarchimedeanLocalField F]
    (E : Type v) [Field E] [TopologicalSpace E] [ValuativeRel E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (F' : Type u') [Field F'] [TopologicalSpace F'] [ValuativeRel F']
    [IsNonarchimedeanLocalField F'] (E' : Type v') [Field E'] [Algebra F' E']
    (σF : F ≃+* F'), Continuous σF → Continuous σF.symm →
    ∀ σE : E ≃+* E', (∀ x : F, σE (algebraMap F E x) = algebraMap F' E' (σF x)) →
    ∀ d : ℕ, IsDifferentExponent F E d →
    ∀ ψF' : UnitaryAdditiveCharacter F',
      (LocalFieldData.ofInstances F').additiveConductor ψF' = 0 →
    ∀ (ψF : UnitaryAdditiveCharacter F) (ψE : UnitaryAdditiveCharacter E),
      (∀ x, ψF x = ψF' (σF x)) → (∀ y, ψE y = ψF' (Algebra.trace F' E' (σE y))) →
      TraceEpsilonCharacterCondition ψF ψE d

theorem traceCharacterTransport : TraceCharacterTransportStatement.{u, v, u', v'} := by
  intro F _ _ _ _ E _ _ _ _ _ _ F' _ _ _ _ E' _ _ σF hσF hσFs σE hcomm d hd ψF' hcond
    ψF ψE hψF hψE
  exact traceEpsilonCharacterCondition_of_ringEquiv σF hσF hσFs σE hcomm hd ψF' hcond
    ψF ψE hψF hψE

end Langlands.BaseChange
