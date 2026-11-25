import Langlands.TraceFormula.TwistedOrbitalTermInvariance
import Langlands.TraceFormula.SingleOrbitSimpleTrace

/-!
# One geometric expansion for a finite sum of functions

Let `G` be a topological group with its Borel structure, `Γ` a subgroup and `μG` a left-invariant
measure. Suppose that each of finitely many functions `φ k` has a geometric expansion of a number
`t k`: a finite family of representatives `r k j ∈ Γ`, pairwise not conjugate under `Γ`, meeting
every class on which the orbit function of `φ k` does not vanish, such that for all admissible
measures `t k = ∑ j, vol((Γ ∩ C) \ C) · O_{r k j}(φ k)` (`SimpleTraceGeometricExpansion`).
`exists_simpleTraceGeometricExpansion_sum` gives one family of representatives for which `∑ k, t k`
is the geometric expansion of `∑ k, φ k`. The representatives of the pieces are grouped by
conjugacy class and one representative of each class is kept; a piece contributes the term at the
kept representative by transport along conjugation
(`exists_isCompatible_of_isTwistedConjugate`), or nothing if its family misses the class.
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory Langlands.QuotientIntegration
open scoped ENNReal

universe u

section Algebra

variable {G : Type u} [Group G]

/-- Twisted conjugacy under a subgroup is reflexive. -/
theorem IsTwistedConjugate.refl (Γ : Subgroup G) (θ : G →* G) (x : G) :
    IsTwistedConjugate Γ θ x x :=
  ⟨1, Γ.one_mem, by simp⟩

/-- The orbit function of a finite sum is the sum of the orbit functions. -/
theorem twistedOrbitFunction_finsetSum (θ : G →* G) (γ : G) {ι : Type*} (s : Finset ι)
    (φ : ι → G → ℂ) :
    twistedOrbitFunction θ γ (fun x => ∑ k ∈ s, φ k x) =
      fun q => ∑ k ∈ s, twistedOrbitFunction θ γ (φ k) q := by
  funext q
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- An orbit function vanishes if the function vanishes on the twisted class. -/
theorem twistedOrbitFunction_eq_zero (θ : G →* G) (γ : G) {φ : G → ℂ}
    (h : ∀ x : G, φ (x⁻¹ * γ * θ x) = 0) : twistedOrbitFunction θ γ φ = 0 := by
  funext q
  induction q using Quotient.inductionOn with
  | h x => exact h x

/-- A choice of one element in each class of an equivalence relation on a finite type: a family
`rep : Fin m → ι` and a map `c : ι → Fin m`, constant on classes, with `rep (c i)` in the class of
`i` and `c (rep j) = j`. -/
theorem exists_classRepresentatives {ι : Type*} [Finite ι] (s : Setoid ι) :
    ∃ (m : ℕ) (rep : Fin m → ι) (c : ι → Fin m),
      (∀ i, s (rep (c i)) i) ∧ (∀ j, c (rep j) = j) ∧ ∀ i i', s i i' → c i = c i' := by
  classical
  let _ : Fintype (Quotient s) := Fintype.ofFinite _
  let e : Quotient s ≃ Fin (Fintype.card (Quotient s)) := Fintype.equivFin _
  refine ⟨Fintype.card (Quotient s), fun j => (e.symm j).out, fun i => e (Quotient.mk s i),
    fun i => ?_, fun j => ?_, fun i i' h => ?_⟩
  · simp only [Equiv.symm_apply_apply]
    exact Quotient.mk_out (s := s) i
  · simp only [Quotient.out_eq, Equiv.apply_symm_apply]
  · change e (Quotient.mk s i) = e (Quotient.mk s i')
    rw [Quotient.sound h]

end Algebra

section Expansion

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

/-- **One expansion for a finite sum.** If every `φ k` has a geometric expansion of `t k` with
representatives satisfying a property `P`, then `∑ k, φ k` has a geometric expansion of `∑ k, t k`
with representatives satisfying `P`, chosen among those of the pieces, one in each class. -/
theorem exists_simpleTraceGeometricExpansion_sum (Γ : Subgroup G) (μG : Measure G)
    [μG.IsMulLeftInvariant] (P : G → Prop) {N : ℕ} (φ : Fin N → G → ℂ) (t : Fin N → ℂ)
    (h : ∀ k, ∃ (m : ℕ) (r : Fin m → Γ),
      (∀ j l, IsTwistedConjugate Γ (MonoidHom.id G) (r j : G) (r l : G) → j = l) ∧
      (∀ j, P (r j : G)) ∧
      (∀ q ∈ Γ, (∃ x : G, φ k (x⁻¹ * q * x) ≠ 0) →
        ∃ j, IsTwistedConjugate Γ (MonoidHom.id G) (r j : G) q) ∧
      SimpleTraceGeometricExpansion Γ (MonoidHom.id G) μG (φ k) (t k) r) :
    ∃ (m : ℕ) (r : Fin m → Γ),
      (∀ j l, IsTwistedConjugate Γ (MonoidHom.id G) (r j : G) (r l : G) → j = l) ∧
      (∀ j, P (r j : G)) ∧
      (∀ q ∈ Γ, (∃ x : G, (∑ k, φ k (x⁻¹ * q * x)) ≠ 0) →
        ∃ j, IsTwistedConjugate Γ (MonoidHom.id G) (r j : G) q) ∧
      SimpleTraceGeometricExpansion Γ (MonoidHom.id G) μG (fun x => ∑ k, φ k x) (∑ k, t k) r := by
  classical
  choose m r hdist hP hcov hexp using h
  let R : (Σ k, Fin (m k)) → Γ := fun i => r i.1 i.2
  let s : Setoid (Σ k, Fin (m k)) :=
    { r := fun i i' => IsTwistedConjugate Γ (MonoidHom.id G) (R i : G) (R i' : G)
      iseqv := ⟨fun i => IsTwistedConjugate.refl Γ _ _, fun h => h.symm,
        fun h h' => h.trans h'⟩ }
  obtain ⟨m', rep, c, hrep, hcrep, hcs⟩ := exists_classRepresentatives s
  obtain ⟨r', hr'⟩ : ∃ r' : Fin m' → Γ, ∀ j, r' j = R (rep j) :=
    ⟨fun j => R (rep j), fun _ => rfl⟩
  have hconj (i : Σ k, Fin (m k)) :
      IsTwistedConjugate Γ (MonoidHom.id G) (r' (c i) : G) (R i : G) := by
    rw [hr']
    exact hrep i
  have hdist' (j l : Fin m')
      (hjl : IsTwistedConjugate Γ (MonoidHom.id G) (r' j : G) (r' l : G)) : j = l := by
    rw [← hcrep j, ← hcrep l]
    rw [hr', hr'] at hjl
    exact hcs _ _ hjl
  -- a piece whose family misses the class of `r' j'` has orbit function zero there
  have hmiss (k : Fin N) (j' : Fin m') (hk : ∀ j, c ⟨k, j⟩ ≠ j') (x : G) :
      φ k (x⁻¹ * (r' j' : G) * x) = 0 := by
    by_contra hx
    obtain ⟨j, hj⟩ := hcov k (r' j' : G) (r' j').property ⟨x, hx⟩
    apply hk j
    rw [← hcrep j']
    rw [hr'] at hj
    exact hcs _ _ hj
  refine ⟨m', r', hdist', fun j => by rw [hr']; exact hP _ _, ?_, ?_⟩
  · rintro q hq ⟨x, hx⟩
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    obtain ⟨j, hj⟩ := hcov k q hq ⟨x, hk⟩
    exact ⟨c ⟨k, j⟩, (hconj ⟨k, j⟩).trans hj⟩
  -- the measure block
  intro mC hmC mD hmD μC' hR' hF' hP' νC' νD' hc hcD
  let _ : ∀ (k : Fin N) (j : Fin (m k)),
      MeasurableSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) (r k j : G))) :=
    fun _ _ => borel _
  have _ : ∀ (k : Fin N) (j : Fin (m k)),
      BorelSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) (r k j : G))) :=
    fun _ _ => ⟨rfl⟩
  let _ : ∀ (k : Fin N) (j : Fin (m k)),
      MeasurableSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G)
        (r k j : G)))) :=
    fun _ _ => borel _
  have _ : ∀ (k : Fin N) (j : Fin (m k)),
      BorelSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G)
        (r k j : G)))) :=
    fun _ _ => ⟨rfl⟩
  have htransport (k : Fin N) (j : Fin (m k)) :
      ∃ (μ : Measure (twistedCentralizer (MonoidHom.id G) (r k j : G)))
        (_ : μ.IsMulRightInvariant),
        IsFiniteMeasureOnCompacts μ ∧ μ.IsOpenPosMeasure ∧
        ∃ (ν : Measure (LeftQuotient (twistedCentralizer (MonoidHom.id G) (r k j : G))))
          (νΓ : Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G)
            (r k j : G))))),
          IsCompatible (twistedCentralizer (MonoidHom.id G) (r k j : G)) μG μ ν ∧
          IsCompatible (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) (r k j : G))) μ
            Measure.count νΓ ∧
          νΓ Set.univ = νD' (c ⟨k, j⟩) Set.univ ∧
          ∀ ψ : G → ℂ,
            (Integrable (twistedOrbitFunction (MonoidHom.id G) (r k j : G) ψ) ν ↔
              Integrable (twistedOrbitFunction (MonoidHom.id G) (r' (c ⟨k, j⟩) : G) ψ)
                (νC' (c ⟨k, j⟩))) ∧
            twistedOrbitalIntegral (MonoidHom.id G) (r k j : G) ν ψ =
              twistedOrbitalIntegral (MonoidHom.id G) (r' (c ⟨k, j⟩) : G) (νC' (c ⟨k, j⟩)) ψ :=
    exists_isCompatible_of_isTwistedConjugate Γ (MonoidHom.id G) (hconj ⟨k, j⟩) μG
      (μC' (c ⟨k, j⟩)) (νC' (c ⟨k, j⟩)) (νD' (c ⟨k, j⟩)) (hc _) (hcD _)
  choose μT hRT hFT hPT νT νΓT hcT hcΓT hvolT hψT using htransport
  have hpiece (k : Fin N) := hexp k (μT k) (νT k) (νΓT k) (hcT k) (hcΓT k)
  -- integrability of the orbit function of each piece at each kept representative
  have hintk (k : Fin N) (j' : Fin m') :
      Integrable (twistedOrbitFunction (MonoidHom.id G) (r' j' : G) (φ k)) (νC' j') := by
    by_cases hex : ∃ j, c ⟨k, j⟩ = j'
    · obtain ⟨j, rfl⟩ := hex
      exact ((hψT k j (φ k)).1).1 ((hpiece k).2.1 j)
    · push Not at hex
      rw [twistedOrbitFunction_eq_zero (MonoidHom.id G) (r' j' : G) (hmiss k j' hex)]
      exact integrable_zero _ _ _
  -- the orbital integral of a piece at a kept representative missed by its family is zero
  have hzero (k : Fin N) (j' : Fin m') (hex : ∀ j, c ⟨k, j⟩ ≠ j') :
      twistedOrbitalIntegral (MonoidHom.id G) (r' j' : G) (νC' j') (φ k) = 0 := by
    rw [twistedOrbitalIntegral,
      twistedOrbitFunction_eq_zero (MonoidHom.id G) (r' j' : G) (hmiss k j' hex)]
    simp
  refine ⟨fun j' => ?_, fun j' => ?_, ?_⟩
  · rcases hi : rep j' with ⟨k, j⟩
    have hcj : c ⟨k, j⟩ = j' := by rw [← hi, hcrep]
    rw [← hcj, ← hvolT k j]
    exact (hpiece k).1 j
  · rw [twistedOrbitFunction_finsetSum]
    exact integrable_finsetSum _ fun k _ => hintk k j'
  · -- the trace
    have hk (k : Fin N) : t k = ∑ j' : Fin m', ((νD' j' Set.univ).toReal : ℂ) *
        twistedOrbitalIntegral (MonoidHom.id G) (r' j' : G) (νC' j') (φ k) := by
      rw [(hpiece k).2.2]
      refine Finset.sum_of_injOn (fun j => c ⟨k, j⟩) ?_ (fun _ _ => Finset.mem_univ _) ?_ ?_
      · intro j _ l _ hjl
        have hjl' : IsTwistedConjugate Γ (MonoidHom.id G) (R ⟨k, j⟩ : G) (R ⟨k, l⟩ : G) :=
          (hconj ⟨k, j⟩).symm.trans ((congrArg (fun a => (r' a : G)) hjl ▸ hconj ⟨k, l⟩))
        exact hdist k j l hjl'
      · intro j' _ hj'
        have hex : ∀ j, c ⟨k, j⟩ ≠ j' := fun j hj => hj' ⟨j, Finset.mem_coe.mpr
          (Finset.mem_univ _), hj⟩
        rw [hzero k j' hex, mul_zero]
      · intro j _
        simp only
        rw [hvolT k j, ((hψT k j (φ k)).2)]
    rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [← Finset.mul_sum, twistedOrbitalIntegral, twistedOrbitFunction_finsetSum,
      integral_finsetSum _ fun k _ => hintk k j']
    rfl

end Expansion

end Langlands.TraceFormula
