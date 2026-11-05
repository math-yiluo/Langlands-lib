import Langlands.Representation.Plancherel.RationalUnramifiedFactorization
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Instances.Complex
import Mathlib.Algebra.Polynomial.Roots

/-! # Density of the nonzero locus of an actual unramified regular function -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u v

/-- Evaluate a finite Laurent combination on a tuple of complex units. -/
def finiteLaurentEvaluation {n : ℕ} (c : Fin n → ℂˣ) :
    AddMonoidAlgebra ℂ (Fin n → ℤ) →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ _ _
    { toFun := fun m => ∏ i, ((c i ^ m.toAdd i : ℂˣ) : ℂ)
      map_one' := by simp
      map_mul' := by
        intro m k
        simp only [toAdd_mul, Pi.add_apply, zpow_add, Units.val_mul,
          Finset.prod_mul_distrib] }

@[simp]
theorem finiteLaurentEvaluation_single {n : ℕ} (c : Fin n → ℂˣ)
    (m : Fin n → ℤ) (a : ℂ) :
    finiteLaurentEvaluation c (AddMonoidAlgebra.single m a) =
      a * ∏ i, ((c i ^ m i : ℂˣ) : ℂ) := by
  simp [finiteLaurentEvaluation]

/-- Laurent evaluations determine a polynomial when each variable ranges over
an infinite set, with coefficients tested by a separating family of maps. -/
theorem laurent_eq_zero_of_eval_on_infinite
    {R : Type v} [CommRing R] {A : Type*} (e : A → R →+* ℂ)
    (he : ∀ r, (∀ a, e a r = 0) → r = 0)
    (s : Set ℂˣ) (hs : s.Infinite) (p : LaurentPolynomial R)
    (hp : ∀ a z, z ∈ s → LaurentPolynomial.eval₂ (e a) z p = 0) :
    p = 0 := by
  classical
  obtain ⟨k, q, hq⟩ := LaurentPolynomial.exists_T_pow p
  have hmap (a : A) : q.map (e a) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (hs.image Units.val_injective.injOn).mono
    rintro _ ⟨z, hz, rfl⟩
    change (q.map (e a)).eval (z : ℂ) = 0
    rw [Polynomial.eval_map]
    rw [← LaurentPolynomial.eval₂_toLaurent]
    rw [hq, map_mul, hp a z hz, zero_mul]
  have hq0 : q = 0 := by
    ext i
    apply he
    intro a
    have hi := congrArg (fun t : Polynomial ℂ => t.coeff i) (hmap a)
    simpa using hi
  have hmul : p * LaurentPolynomial.T (k : ℤ) = 0 := by
    rw [← hq, hq0, map_zero]
  exact (LaurentPolynomial.isUnit_T (R := R) (k : ℤ)).mul_left_eq_zero.mp hmul

theorem finiteLaurentEvaluation_cons {n : ℕ} (z : ℂˣ)
    (c : Fin n → ℂˣ) (p : AddMonoidAlgebra ℂ (Fin (n + 1) → ℤ)) :
    finiteLaurentEvaluation (Fin.cons z c) p =
      LaurentPolynomial.eval₂ (finiteLaurentEvaluation c).toRingHom z
        (finiteLaurentSuccessorEquiv ℂ n p) := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single m a =>
      simp only [finiteLaurentEvaluation_single, finiteLaurentSuccessorEquiv,
        RingEquiv.trans_apply, AddMonoidAlgebra.mapDomainRingEquiv_single]
      change a * ∏ i : Fin (n + 1),
        ((((Fin.cons z c : Fin (n + 1) → ℂˣ) i) ^ m i : ℂˣ) : ℂ) =
        LaurentPolynomial.eval₂ (finiteLaurentEvaluation c).toRingHom z
          (AddMonoidAlgebra.curryRingEquiv
            (AddMonoidAlgebra.single (m 0, fun i => m i.succ) a))
      rw [AddMonoidAlgebra.curryRingEquiv_single]
      simp [finiteLaurentEvaluation_single,
        LaurentPolynomial.single_eq_C_mul_T, Fin.prod_univ_succ,
        mul_assoc]
      exact Or.inl (mul_comm _ _)

theorem finiteLaurentEvaluation_empty (p : AddMonoidAlgebra ℂ (Fin 0 → ℤ)) :
    finiteLaurentEvaluation (fun i => Fin.elim0 i) p =
      AddMonoidAlgebra.uniqueRingEquiv (R := ℂ) (Fin 0 → ℤ) p := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single m a =>
      have hm : m = ![] := Subsingleton.elim _ _
      subst m
      simp [finiteLaurentEvaluation_single, AddMonoidAlgebra.uniqueRingEquiv]

/-- A finite Laurent combination vanishing on a box with infinite sides is
zero. The empty tuple is included. -/
theorem finiteLaurent_eq_zero_of_eval_on_box (n : ℕ)
    (s : Fin n → Set ℂˣ) (hs : ∀ i, (s i).Infinite)
    (p : AddMonoidAlgebra ℂ (Fin n → ℤ))
    (hp : ∀ c ∈ Set.pi Set.univ s, finiteLaurentEvaluation c p = 0) :
    p = 0 := by
  classical
  induction n with
  | zero =>
      apply (AddMonoidAlgebra.uniqueRingEquiv (R := ℂ) (Fin 0 → ℤ)).injective
      rw [map_zero, ← finiteLaurentEvaluation_empty]
      exact hp (fun i => Fin.elim0 i) (by simp [Set.mem_pi])
  | succ n ih =>
      apply (finiteLaurentSuccessorEquiv ℂ n).injective
      rw [map_zero]
      apply laurent_eq_zero_of_eval_on_infinite
        (fun c : Set.pi Set.univ (fun i : Fin n => s i.succ) =>
          (finiteLaurentEvaluation c.val).toRingHom)
        (fun r hr => ih (fun i => s i.succ) (fun i => hs i.succ) r
          (fun c hc => hr ⟨c, hc⟩))
        (s 0) (hs 0)
      intro c z hz
      rw [← finiteLaurentEvaluation_cons]
      apply hp
      intro i _
      exact Fin.cases hz (fun j => c.property j (Set.mem_univ _)) i

/-- A nonempty open subset of the complex units is infinite. -/
theorem complexUnits_infinite_of_isOpen {s : Set ℂˣ}
    (hs : IsOpen s) (hne : s.Nonempty) : s.Infinite := by
  obtain ⟨z, hz⟩ := hne
  apply Set.Infinite.of_image (fun z : ℂˣ => (z : ℂ))
  exact infinite_of_mem_nhds (z : ℂ)
    (((IsOpenUnits.isOpenEmbedding_unitsVal (M := ℂ)).isOpenMap s hs).mem_nhds
      ⟨z, hz, rfl⟩)

/-- Vanishing on any nonempty open part of the complex torus forces a finite
Laurent combination to vanish identically. -/
theorem finiteLaurent_eq_zero_of_eval_on_open {n : ℕ}
    (p : AddMonoidAlgebra ℂ (Fin n → ℤ))
    {U : Set (Fin n → ℂˣ)} (hU : IsOpen U) (hne : U.Nonempty)
    (hp : ∀ c ∈ U, finiteLaurentEvaluation c p = 0) :
    p = 0 := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨s, hs, hsU⟩ := isOpen_pi_iff'.mp hU c hc
  exact finiteLaurent_eq_zero_of_eval_on_box n s
    (fun i => complexUnits_infinite_of_isOpen (hs i).1 ⟨c i, (hs i).2⟩)
    p (fun z hz => hp z (hsU hz))

section ActualCharacters

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints G)]
  (hp : Continuous (rationalValuationImageProjection G))
  (hG : GroupScheme.IsConnectedReductive G)

/-- The actual Laurent-algebra comparison evaluates by the finite character
coordinates, for every finite Laurent combination. -/
theorem rationalUnramifiedLaurentAlgebraEquiv_eval
    (p : AddMonoidAlgebra ℂ (Fin (rationalImageRank G) → ℤ))
    (χ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)) :
    (rationalUnramifiedLaurentAlgebraEquiv G hp hG p).val χ =
      finiteLaurentEvaluation
        (((rationalImageUnramifiedContinuousEquiv G hp).symm.trans
          (rationalReductiveImageCharacterCoordinates G hG)) χ) p := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, Subalgebra.coe_add, Pi.add_apply, hp, hq]
  | single m a =>
      rw [rationalUnramifiedLaurentAlgebraEquiv_single,
        finiteLaurentEvaluation_single]
      change a * ((∏ i, rationalImageUnramifiedDescend G χ
        ((rationalReductiveValuationBasis G hG i).toMul) ^ m i : ℂˣ) : ℂ) =
        a * ∏ i, ((rationalImageUnramifiedDescend G χ
          ((rationalReductiveValuationBasis G hG i).toMul) ^ m i : ℂˣ) : ℂ)
      simp

include hp hG

/-- An actual regular scalar vanishing on any nonempty open set of the full
unramified character space is zero. -/
theorem rationalUnramifiedRegular_eq_zero_of_isOpen
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
    (hU : IsOpen U) (hne : U.Nonempty) (hb : ∀ χ ∈ U, b.val χ = 0) :
    b = 0 := by
  let e := ((rationalImageUnramifiedContinuousEquiv G hp).symm.trans
    (rationalReductiveImageCharacterCoordinates G hG)).toHomeomorph
  let a := rationalUnramifiedLaurentAlgebraEquiv G hp hG
  apply a.symm.injective
  rw [map_zero]
  apply finiteLaurent_eq_zero_of_eval_on_open (a.symm b)
    (hU.preimage e.symm.continuous) (hne.preimage e.symm.surjective)
  intro c hc
  have he := rationalUnramifiedLaurentAlgebraEquiv_eval G hp hG
    (a.symm b) (e.symm c)
  rw [a.apply_symm_apply] at he
  change b.val (e.symm c) = finiteLaurentEvaluation (e (e.symm c)) (a.symm b) at he
  rw [e.apply_symm_apply] at he
  exact he.symm.trans (hb (e.symm c) hc)

/-- A nonzero actual regular scalar has a nonzero value in every nonempty
open set. -/
theorem rationalUnramifiedRegular_exists_ne_zero_of_isOpen
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : b ≠ 0)
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ χ ∈ U, b.val χ ≠ 0 := by
  by_contra h
  apply hb
  apply rationalUnramifiedRegular_eq_zero_of_isOpen G hp hG b hU hne
  simpa only [not_exists, not_and, not_not] using h

/-- The nonzero locus of a nonzero actual regular scalar is dense in the full
unramified character space. -/
theorem rationalUnramifiedRegular_dense_nonzero
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : b ≠ 0) :
    Dense {χ | b.val χ ≠ 0} := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨χ, hχ, hbχ⟩ :=
    rationalUnramifiedRegular_exists_ne_zero_of_isOpen G hp hG b hb hU hne
  exact ⟨χ, hχ, hbχ⟩

/-- Density persists on any open parameter region, including the empty one. -/
theorem rationalUnramifiedRegular_dense_nonzero_on_open
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : b ≠ 0)
    {U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
    (hU : IsOpen U) :
    Dense {χ : U | b.val χ.val ≠ 0} :=
  (rationalUnramifiedRegular_dense_nonzero G hp hG b hb).preimage
    hU.isOpenMap_subtype_val

end ActualCharacters

end Langlands.Plancherel
