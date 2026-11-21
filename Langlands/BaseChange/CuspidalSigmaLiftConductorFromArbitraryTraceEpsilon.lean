import Langlands.BaseChange.CuspidalSigmaLiftConductorLocalReduction

/-!
# Conductor reduction for an arbitrary trace-related additive character

The local epsilon data may use any nontrivial additive character `ψF` of `F` and
its trace pullback relation to `ψE`. The count of norm-trivial characters and the
additive-conductor formula of a trace character are explicit premises.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.BaseChange

open HarmonicAnalysis (AdditiveHaarMeasure UnitaryAdditiveCharacter)

universe u v uV uW

/-- A cyclic extension of degree `l` has exactly `l` characters of `Fˣ` that are
trivial on norms. -/
def NormTrivialCountStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ X : Finset (Fˣ →* ℂˣ), (∀ κ, κ ∈ X ↔ IsNormTrivial E κ) → X.card = l

/-- For trace-related characters, `f·n(ψE) = [E:F]·n(ψF) + f·d`. -/
def TraceAdditiveConductorFormulaStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E] [Module.Finite F E]
    (f d : ℕ), IsResidueDegree F E f → IsDifferentExponent F E d →
    ∀ (ψF : UnitaryAdditiveCharacter F) (ψE : UnitaryAdditiveCharacter E),
      (∀ x : E, ψE x = ψF (Algebra.trace F E x)) →
      (f : ℤ) * (LocalFieldData.ofInstances E).additiveConductor ψE =
        (Module.finrank F E : ℤ) * (LocalFieldData.ofInstances F).additiveConductor ψF +
          (f : ℤ) * d

/-- The local factor data at the extension, with any trace-related pair of
additive characters. -/
def CuspidalSigmaLiftArbitraryTraceEpsilonDataStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (k : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear (k + 1) F) V)
      (hπ : IsAdmissible π), GeneralLinear.IsSupercuspidal π → π.IsIrreducible →
    ∀ (s k₁ : ℕ) (h : s * (k₁ + 1) = k + 1)
      (W₁ : Type uW) [AddCommGroup W₁] [Module ℂ W₁]
      (P₁ : Representation ℂ (GeneralLinear (k₁ + 1) E) W₁),
      GeneralLinear.IsSupercuspidal P₁ → P₁.IsIrreducible →
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (P : Representation ℂ (GeneralLinear (k + 1) E) W)
      (hP : IsAdmissible P),
      Nonempty (P.Equiv ((sigmaOrbitProduct σ s (Nat.succ_pos k₁) P₁).comp
        (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom)) →
    ∀ (A : SigmaIntertwiner σ (k + 1) P) (c : ℂ),
      (haveI := LocalFieldTopology.generalLinear_t2Space F (k + 1)
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F (k + 1)
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (k + 1)
       haveI := LocalFieldTopology.generalLinear_t2Space E (k + 1)
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E (k + 1)
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E (k + 1)
       IsSigmaLift σ l π hπ P hP A c) →
    ∀ f d : ℕ, IsResidueDegree F E f → IsDifferentExponent F E d →
    ∀ X : Finset (Fˣ →* ℂˣ), (∀ κ, κ ∈ X ↔ IsNormTrivial E κ) →
      ∃ (ψF : UnitaryAdditiveCharacter F) (ψE : UnitaryAdditiveCharacter E)
        (νF : letI := borel F; AdditiveHaarMeasure F)
        (νE : letI := borel E; AdditiveHaarMeasure E)
        (aF : (Fˣ →* ℂˣ) → ℕ) (a₁ : ℕ)
        (eF : (Fˣ →* ℂˣ) → ℂˣ × ℤ) (eOrbit : Fin s → ℂˣ × ℤ) (eP : ℂˣ × ℤ),
        (∀ x : E, ψE x = ψF (Algebra.trace F E x)) ∧
        (∀ κ ∈ X, IsStandardEpsilonConductor ψF νF
          (twist (κ.comp GeneralLinear.determinant) π) (aF κ) (eF κ)) ∧
        Conductor.IsNewvectorConductor P₁ a₁ ∧
        (∀ i : Fin s, IsStandardEpsilonConductor ψE νE
          (P₁.comp (entrywiseAut (σ ^ (i : ℕ)) (k₁ + 1)).toMonoidHom) a₁ (eOrbit i)) ∧
        OrbitProductEpsilonMultiplicativity ψE νE P eOrbit eP ∧
        EpsilonMonomialProductComparison (LocalFieldData.ofInstances F).residueCardinality
          (LocalFieldData.ofInstances E).residueCardinality X eF eP

private theorem firstFixedLevel_eq_of_isNewvectorConductor'
    {F : Type u} [Field F] [ValuativeRel F] {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GeneralLinear (r + 1) F) V} {a : ℕ}
    (ha : Conductor.IsNewvectorConductor ρ a) :
    Conductor.firstFixedLevel ρ = (a : WithTop ℕ) := by
  have h : Conductor.HasNewvectorLevel ρ := ⟨a, ha.1⟩
  rw [Conductor.firstFixedLevel_of_hasNewvectorLevel ρ h,
    (Conductor.newvectorConductor_eq_iff ρ h a).mpr ha]

/-- With the norm-trivial count and the trace conductor formula, local epsilon
data for any trace-related additive characters imply the exact conductor
formula. -/
def CuspidalSigmaLiftConductorFromArbitraryTraceEpsilonStatement : Prop :=
  NormTrivialCountStatement.{u, v} → TraceAdditiveConductorFormulaStatement.{u, v} →
    CuspidalSigmaLiftArbitraryTraceEpsilonDataStatement.{u, v, uV, uW} →
      CuspidalSigmaLiftConductorStatement.{u, v, uV, uW}

theorem cuspidalSigmaLiftConductorFromArbitraryTraceEpsilon :
    CuspidalSigmaLiftConductorFromArbitraryTraceEpsilonStatement.{u, v, uV, uW} := by
  intro hcount hformula hdata F _ _ _ _ _ E _ _ _ _ _ _ σ l hcyc k V _ _ π hπ hsuper hπirr
    s k₁ hrank W₁ _ _ P₁ hP₁super hP₁irr W _ _ P hP horbit A c hlift f d hf hd X hX
  obtain ⟨ψF, ψE, νF, νE, aF, a₁, eF, eOrbit, eP,
    htrace, hF, ha₁, hOrbit, hprod, hcomp⟩ :=
    hdata F E σ l hcyc k V π hπ hsuper hπirr s k₁ hrank W₁ P₁ hP₁super hP₁irr
      W P hP horbit A c hlift f d hf hd X hX
  let TF := LocalFieldData.ofInstances F
  let TE := LocalFieldData.ofInstances E
  let : Module.Finite F E := hcyc.1
  have hcard : X.card = l := hcount F E σ l hcyc X hX
  have hcond : (f : ℤ) * TE.additiveConductor ψE =
      (l : ℤ) * TF.additiveConductor ψF + (f : ℤ) * d := by
    have h := hformula F E f d hf hd ψF ψE htrace
    rwa [hcyc.2.1] at h
  have hq : TE.residueCardinality = TF.residueCardinality ^ f := hf
  have hsum := EpsilonMonomialProductComparison.sum_eq TF.residueCardinality_gt_one hq hcomp
  have hOrbitProd : EpsilonMonomialProductComparison TE.residueCardinality
      TE.residueCardinality Finset.univ eOrbit eP :=
    ⟨1, fun z => by simpa using hprod.2 z⟩
  have hOrbitSum := EpsilonMonomialProductComparison.sum_eq TE.residueCardinality_gt_one
    (pow_one TE.residueCardinality).symm hOrbitProd
  have heF (κ) (hκ : κ ∈ X) :
      (eF κ).2 = (aF κ : ℤ) + ((k + 1 : ℕ) : ℤ) * TF.additiveConductor ψF :=
    (hF κ hκ).2.2
  have heOrbit (i : Fin s) :
      (eOrbit i).2 = (a₁ : ℤ) + ((k₁ + 1 : ℕ) : ℤ) * TE.additiveConductor ψE :=
    (hOrbit i).2.2
  have hrankInt : (s : ℤ) * ((k₁ + 1 : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) := by
    exact_mod_cast hrank
  have heP : eP.2 = (s : ℤ) * a₁ + ((k + 1 : ℕ) : ℤ) * TE.additiveConductor ψE := by
    calc
      eP.2 = ∑ i : Fin s, (eOrbit i).2 := by simpa using hOrbitSum.symm
      _ = ∑ _ : Fin s, ((a₁ : ℤ) + ((k₁ + 1 : ℕ) : ℤ) * TE.additiveConductor ψE) :=
        Finset.sum_congr rfl (fun i _ => heOrbit i)
      _ = (s : ℤ) * a₁ + ((k + 1 : ℕ) : ℤ) * TE.additiveConductor ψE := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← hrankInt]
        ring
  have hsumF : ∑ κ ∈ X, (eF κ).2 = ∑ κ ∈ X, (aF κ : ℤ) +
      (X.card : ℤ) * (((k + 1 : ℕ) : ℤ) * TF.additiveConductor ψF) := by
    rw [Finset.sum_congr rfl heF, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hint : ∑ κ ∈ X, (aF κ : ℤ) =
      (f : ℤ) * ((s : ℤ) * a₁ + ((k + 1 : ℕ) : ℤ) * d) := by
    rw [hsumF, heP, hcard] at hsum
    linear_combination hsum + ((k + 1 : ℕ) : ℤ) * hcond
  have hnat : ∑ κ ∈ X, aF κ = f * (s * a₁ + (k + 1) * d) := by
    exact_mod_cast hint
  calc
    (∑ κ ∈ X, Conductor.firstFixedLevel (twist (κ.comp GeneralLinear.determinant) π)) =
        ∑ κ ∈ X, (aF κ : WithTop ℕ) :=
      Finset.sum_congr rfl
        (fun κ hκ => firstFixedLevel_eq_of_isNewvectorConductor' (hF κ hκ).2.1)
    _ = (f : WithTop ℕ) * ((s : WithTop ℕ) * Conductor.firstFixedLevel P₁ +
          ((k + 1 : ℕ) : WithTop ℕ) * (d : WithTop ℕ)) := by
      rw [firstFixedLevel_eq_of_isNewvectorConductor' ha₁]
      exact_mod_cast hnat

end Langlands.BaseChange
