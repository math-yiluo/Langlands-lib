import Langlands.Correspondence.HenniartWeilConductorCountStepReduction
import Langlands.Correspondence.HenniartWeilUpperScalar
import Langlands.Correspondence.HenniartGradedWeilCharacters

/-! # The rank-wise twisting equivalence given scalar descent -/

noncomputable section

namespace Langlands.Henniart.Numerical

open Correspondence FiniteRepresentation LocalClassField LocalFactor Weil.Local
open Ramification.Padic Ramification.HerbrandBridge VirtualRepresentation
open VirtualRepresentation.LocalWeil.Ramification

universe uK uW
variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- At an integral upper bound, the scalar character descends through
reciprocity to the corresponding successive unit quotient. -/
def WeilScalarGradeDescent (e : RankOne.ReciprocityCandidate K)
    (he : GeometricWeilReciprocityRelation K K.canonicalTopologicalData e) (l : ℕ) : Prop :=
  ∀ A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K),
    A.IsContinuous → A.IsIrreducible → HasUpperScalarAction K A l →
      (∀ b : ℝ, (l : ℝ) < b → IsTrivialAt K A b) →
      ∃ η : GradedUnitCharacters K l, ∀ w : upperGroup K l,
        A.representation w = (η (upperGradedReciprocity K e he l w) : ℂ) •
          (1 : Module.End ℂ A)

private abbrev Orbit := Weil.UnramifiedOrbitClasses.{uK, uW} (localDegree K)
private abbrev WeilClass (k : ℕ) := IrreducibleWeilClass.{uK, uW} K k.succPNat
private abbrev WeilRep := FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)

private abbrev orbitOf {k : ℕ} (σ : WeilClass.{uK, uW} K k) : Orbit.{uK, uW} K :=
  Weil.unramifiedOrbitClass (localDegree K) ⟨k.succPNat, σ⟩

private abbrev twistBy {k : ℕ} (χ : localWeilGroup K →ₜ* ℂˣ) :
    WeilClass.{uK, uW} K k ≃ WeilClass.{uK, uW} K k :=
  continuousIrreducibleTwistEquiv χ (k + 1)

private theorem twistBy_comm {k : ℕ} (χ η : localWeilGroup K →ₜ* ℂˣ)
    (σ : WeilClass.{uK, uW} K k) :
    twistBy K χ (twistBy K η σ) = twistBy K η (twistBy K χ σ) := by
  have hm (α β : localWeilGroup K →ₜ* ℂˣ) :
      twistBy K α (twistBy K β σ) = twistBy K (α * β) σ :=
    congrArg (fun f : WeilClass.{uK, uW} K k ≃ WeilClass.{uK, uW} K k => f σ)
      (continuousIrreducibleTwistEquiv_mul α β (k + 1))
  rw [hm χ η, hm η χ, mul_comm χ η]

private theorem weilUnramifiedTwist_twistBy {k : ℕ} (z : ℂˣ) (χ : localWeilGroup K →ₜ* ℂˣ)
    (σ : WeilClass.{uK, uW} K k) :
    weilUnramifiedTwist K k z (twistBy K χ σ) = twistBy K χ (weilUnramifiedTwist K k z σ) :=
  twistBy_comm K (unramifiedCharacter (localDegree K) z) χ σ

private theorem torsionNumber_twistBy {k : ℕ} (χ : localWeilGroup K →ₜ* ℂˣ)
    (σ : WeilClass.{uK, uW} K k) : weilTorsionNumber K (twistBy K χ σ) = weilTorsionNumber K σ := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivProp
  funext z
  apply propext
  rw [weilUnramifiedTwist_twistBy K, (twistBy K χ).injective.eq_iff]

private theorem twistBy_orbit_eq {k : ℕ} (χ : localWeilGroup K →ₜ* ℂˣ)
    {σ τ : WeilClass.{uK, uW} K k} (h : orbitOf K σ = orbitOf K τ) :
    orbitOf K (twistBy K χ σ) = orbitOf K (twistBy K χ τ) := by
  obtain ⟨z, hz⟩ := (weilOrbitClass_eq_iff K σ τ).mp h
  exact (weilOrbitClass_eq_iff K _ _).mpr
    ⟨z, (weilUnramifiedTwist_twistBy K z χ τ).trans (congrArg (twistBy K χ) hz)⟩

/-- Witness exhibiting the orbit and a representative of a torsion-one class. -/
private structure OrbitWitness (k : ℕ) (c : Orbit.{uK, uW} K) where
  sigma : WeilClass.{uK, uW} K k
  rep : WeilRep.{uK, uW} K
  orbit_eq : orbitOf K sigma = c
  class_eq : classOf rep = weilClassForget K sigma
  torsion_one : weilTorsionNumber K sigma = 1

private def OrbitWitness.twist {k : ℕ} {c : Orbit.{uK, uW} K}
    (x : OrbitWitness K k c) (χ : localWeilGroup K →ₜ* ℂˣ) :
    OrbitWitness K k (orbitOf K (twistBy K χ x.sigma)) where
  sigma := twistBy K χ x.sigma
  rep := FiniteRepresentation.twist χ.toMonoidHom x.rep
  orbit_eq := rfl
  class_eq := weilTwistRepresentative_classOf K x.class_eq χ
  torsion_one := (torsionNumber_twistBy K χ x.sigma).trans x.torsion_one

private theorem mem_weilSwanBelow_iff_witness {k b : ℕ} {c : Orbit.{uK, uW} K} :
    c ∈ weilSwanBelow K k b ↔ ∃ x : OrbitWitness K k c,
      ((k + 1 : ℕ) : ℝ) * lastBreak K x.rep < (b : ℝ) := by
  rw [mem_weilSwanBelow]
  constructor
  · rintro ⟨s, hs, σ, hσ, hS, hT⟩
    obtain ⟨R, hR⟩ := Quotient.exists_rep σ.val
    have hA : classOf R.val = weilClassForget K σ := congrArg (forgetPropertyClass _) hR
    refine ⟨⟨σ, R.val, hσ, hA, hT⟩, ?_⟩
    rw [← (hasWeilSwan_iff_eq_rank_mul_lastBreak K hA).mp hS]
    exact_mod_cast hs
  · rintro ⟨x, hx⟩
    have hS := hasWeilSwan_weilSwanExponent K x.sigma
    have h := (hasWeilSwan_iff_eq_rank_mul_lastBreak K x.class_eq).mp hS
    rw [← h] at hx
    exact ⟨_, by exact_mod_cast hx, x.sigma, x.orbit_eq, hS, x.torsion_one⟩

private theorem mem_shallow_iff {k l : ℕ} (hl : 0 < l) {c : Orbit.{uK, uW} K} :
    c ∈ weilSwanBelow K k ((k + 1) * l) ↔
      ∃ x : OrbitWitness K k c, IsTrivialAt K x.rep l := by
  rw [mem_weilSwanBelow_iff_witness]
  have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  simp only [Nat.cast_mul, mul_lt_mul_iff_right₀ hpos]
  exact exists_congr fun x => lastBreak_lt_iff_isTrivialAt K x.rep (b := (l : ℝ))
    (weilRepresentative_continuous_irreducible K x.class_eq).1 (by exact_mod_cast hl)

private theorem mem_bounded_iff {k l : ℕ} {c : Orbit.{uK, uW} K} :
    c ∈ weilSwanBelow K k ((k + 1) * l + 1) ↔
      ∃ x : OrbitWitness K k c, ∀ b : ℝ, (l : ℝ) < b → IsTrivialAt K x.rep b := by
  rw [mem_weilSwanBelow_iff_witness]
  apply exists_congr
  intro x
  have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hS := hasWeilSwan_weilSwanExponent K x.sigma
  have h := (hasWeilSwan_iff_eq_rank_mul_lastBreak K x.class_eq).mp hS
  have hle : weilSwanExponent K x.sigma ≤ (k + 1) * l ↔ lastBreak K x.rep ≤ (l : ℝ) := by
    rw [← Nat.cast_le (α := ℝ), h, Nat.cast_mul, mul_le_mul_iff_right₀ hpos]
  rw [← h, Nat.cast_lt, Nat.lt_succ_iff, hle]
  exact lastBreak_le_iff_isTrivialAbove K
    (weilRepresentative_continuous_irreducible K x.class_eq).1 (Nat.cast_nonneg l)

private theorem scalar_eq_of_equiv {A B : WeilRep.{uK, uW} K}
    (e : FiniteRepresentation.Equiv A B) (hA : 0 < A.rank)
    {w : localWeilGroup K} {a b : ℂˣ}
    (ha : A.representation w = (a : ℂ) • (1 : Module.End ℂ A))
    (hb : B.representation w = (b : ℂ) • (1 : Module.End ℂ B)) : a = b := by
  have : Nontrivial A := Module.finrank_pos_iff.mp hA
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  have hv' : e.toLinearEquiv v ≠ 0 := e.toLinearEquiv.map_ne_zero_iff.mpr hv
  have h := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap w v
  change e.toLinearEquiv (A.representation w v) = B.representation w (e.toLinearEquiv v) at h
  rw [ha, hb, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
    Module.End.one_apply, map_smul] at h
  exact CyclicRestriction.eigenline_scalar_unique _ hv' h

/-- Chosen lifts of the graded characters give a bijection from the product
with the shallow torsion-one orbits onto the bounded torsion-one orbits,
conditional only on descent of the scalar action. -/
def weilSwanBelow_stepEquiv (e : RankOne.ReciprocityCandidate K)
    (he : GeometricWeilReciprocityRelation K K.canonicalTopologicalData e)
    {k l i : ℕ} (hl : 0 < l) (hr : k + 1 = p ^ i)
    (hdesc : WeilScalarGradeDescent.{uK, uW} K e he l) :
    GradedUnitCharacters K l × weilSwanBelow.{uK, uW} K k ((k + 1) * l) ≃
      weilSwanBelow.{uK, uW} K k ((k + 1) * l + 1) := by
  let S := ↥(weilSwanBelow.{uK, uW} K k ((k + 1) * l))
  let D := ↥(weilSwanBelow.{uK, uW} K k ((k + 1) * l + 1))
  let χ (η : GradedUnitCharacters K l) := liftGradedCharacterToWeil K e η
  let pick (x : S) : OrbitWitness K k x.val := ((mem_shallow_iff K hl).mp x.property).choose
  have hpick (x : S) : IsTrivialAt K (pick x).rep l :=
    ((mem_shallow_iff K hl).mp x.property).choose_spec
  let M (η : GradedUnitCharacters K l) (x : S) := OrbitWitness.twist K (pick x) (χ η)
  let f : GradedUnitCharacters K l × S → D := fun (η, x) =>
    ⟨orbitOf K (M η x).sigma, (mem_bounded_iff K).mpr ⟨M η x, by
      intro b hb w hw
      change (χ η w : ℂ) • (pick x).rep.representation w = 1
      rw [liftGradedCharacterToWeil_deeper K e he η hb w hw, Units.val_one, one_smul]
      exact hpick x w (upperGroup_antitone K hb.le hw)⟩⟩
  have htop (η : GradedUnitCharacters K l) (x : S) (w : upperGroup K l) :
      (M η x).rep.representation w = (η (upperGradedReciprocity K e he l w) : ℂ) •
        (1 : Module.End ℂ (M η x).rep) := by
    change (χ η w : ℂ) • (pick x).rep.representation w = _
    rw [liftGradedCharacterToWeil_apply K e he η w, hpick x w w.property]
    rfl
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨η, x⟩ ⟨φ, y⟩ hxy
    have ho : orbitOf K (M η x).sigma = orbitOf K (M φ y).sigma := congrArg Subtype.val hxy
    obtain ⟨z, hz⟩ := (weilOrbitClass_eq_iff K _ _).mp ho
    let ζ := unramifiedCharacter (localDegree K) z
    let Z := OrbitWitness.twist K (M φ y) ζ
    have hZ : Z.sigma = (M η x).sigma := hz
    have hcZ : classOf (M η x).rep = classOf Z.rep := (M η x).class_eq.trans
      ((congrArg (weilClassForget K) hZ.symm).trans Z.class_eq.symm)
    obtain ⟨E⟩ := (classOf_eq_iff _ _).mp hcZ
    have hηφ : η = φ := by
      apply MonoidHom.ext
      intro a
      obtain ⟨w, rfl⟩ := upperGradedReciprocity_surjective K e he l a
      have hwI : w.val ∈ localInertia K := by
        rw [localInertia_eq_comap K, ← absoluteUpperCanonicalInertia K]
        exact absoluteUpperRamificationGroup_antitone K (Nat.cast_nonneg l) w.property
      have hz1 : ζ w.val = 1 := unramifiedCharacter_on_kernel (localDegree K) z hwI
      have hZval : Z.rep.representation w = (φ (upperGradedReciprocity K e he l w) : ℂ) •
          (1 : Module.End ℂ Z.rep) := by
        change (ζ w.val : ℂ) • (M φ y).rep.representation w = _
        rw [hz1, Units.val_one, one_smul, htop φ y w]
        rfl
      have hn : 0 < (M η x).rep.rank := by
        rw [(weilRepresentative_break_rank K (M η x).class_eq).2]
        exact Nat.succ_pos k
      exact scalar_eq_of_equiv K E hn (htop η x w) hZval
    subst φ
    change weilUnramifiedTwist K k z (twistBy K (χ η) (pick y).sigma) =
      twistBy K (χ η) (pick x).sigma at hz
    rw [weilUnramifiedTwist_twistBy K] at hz
    have h := (weilOrbitClass_eq_iff K _ _).mpr ⟨z, (twistBy K (χ η)).injective hz⟩
    exact Prod.ext rfl (Subtype.ext ((pick x).orbit_eq.symm.trans (h.trans (pick y).orbit_eq)))
  · intro c
    obtain ⟨x, hx⟩ := (mem_bounded_iff K).mp c.property
    obtain ⟨hc, hi⟩ := weilRepresentative_continuous_irreducible K x.class_eq
    have hs := hasUpperScalarAction_of_torsionOne K x.rep x.class_eq x.torsion_one hr
      (a := (l : ℝ)) (by exact_mod_cast hl)
      ((lastBreak_le_iff_isTrivialAbove K hc (Nat.cast_nonneg l)).mpr hx)
    obtain ⟨η, hη⟩ := hdesc x.rep hc hi hs hx
    let y := OrbitWitness.twist K x (χ η)⁻¹
    have hy : IsTrivialAt K y.rep l := by
      intro w hw
      change (↑((χ η w)⁻¹) : ℂ) • x.rep.representation w = 1
      rw [hη ⟨w, hw⟩, ← liftGradedCharacterToWeil_apply K e he η ⟨w, hw⟩,
        smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    let v : S := ⟨orbitOf K y.sigma, (mem_shallow_iff K hl).mpr ⟨y, hy⟩⟩
    refine ⟨(η, v), Subtype.ext ?_⟩
    change orbitOf K (twistBy K (χ η) (pick v).sigma) = c.val
    calc
      _ = orbitOf K (twistBy K (χ η) y.sigma) :=
        twistBy_orbit_eq K (χ η) (pick v).orbit_eq
      _ = c.val := by
        have hcancel : twistBy K (χ η) (twistBy K (χ η)⁻¹ x.sigma) = x.sigma :=
          continuousIrreducibleTwistEquiv_apply_inv (χ η) (k + 1) x.sigma
        exact (congrArg (orbitOf K) hcancel).trans x.orbit_eq

/-- The integer conductor-count step from graded scalar descent at this level. -/
theorem weilConductorCountStep_of_scalarGradeDescent (e : RankOne.ReciprocityCandidate K)
    (he : GeometricWeilReciprocityRelation K K.canonicalTopologicalData e) {r l : ℕ} (hl : 1 ≤ l)
    (hdesc : WeilScalarGradeDescent.{uK, uW} K e he l) :
    weilConductorCount.{uK, uW} K (p ^ r - 1) (p ^ r * l) =
      (K.canonicalTopologicalData.residueCardinality : ℕ∞) *
        weilConductorCount.{uK, uW} K (p ^ r - 1) (p ^ r * l - 1) := by
  apply weilConductorCountStep_of_equiv K hl (GradedUnitCharacters K l) (card_gradedUnitCharacters K hl)
  intro d hd
  have hdvd := (Nat.mem_divisors.mp hd).1
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  have h : d - 1 + 1 = d := by rw [hi]; have := pow_pos (Fact.out : p.Prime).pos i; omega
  simpa only [h] using (show Nonempty (GradedUnitCharacters K l ×
      weilSwanBelow.{uK, uW} K (d - 1) ((d - 1 + 1) * l) ≃
        weilSwanBelow.{uK, uW} K (d - 1) ((d - 1 + 1) * l + 1)) from
    ⟨weilSwanBelow_stepEquiv K e he hl (h.trans hi) hdesc⟩)

end Langlands.Henniart.Numerical
