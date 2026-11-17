import Langlands.Representation.Plancherel.RationalUnitaryNonvanishing
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.Connected.Clopen

/-! # Laurent coordinate divisibility from unitary slices -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace Langlands.Plancherel

universe v

/-- The Laurent factor theorem at a unit, over any commutative coefficient
ring. Clearing a power of `T` reduces it to the polynomial factor theorem. -/
theorem laurent_T_sub_C_dvd_iff_eval_eq_zero
    {R : Type v} [CommRing R] (a : Rˣ) (p : LaurentPolynomial R) :
    LaurentPolynomial.T (1 : ℤ) - LaurentPolynomial.C (a : R) ∣ p ↔
      LaurentPolynomial.eval₂ (RingHom.id R) a p = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    simp only [map_mul, map_sub, LaurentPolynomial.eval₂_T,
      LaurentPolynomial.eval₂_C, RingHom.id_apply, zpow_one,
      sub_self, zero_mul]
  · intro hp
    obtain ⟨k, q, hq⟩ := LaurentPolynomial.exists_T_pow p
    have hroot : q.IsRoot (a : R) := by
      change q.eval (a : R) = 0
      rw [← Polynomial.eval₂_id, ← LaurentPolynomial.eval₂_toLaurent,
        hq, map_mul, hp, zero_mul]
    obtain ⟨r, hr⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    refine ⟨Polynomial.toLaurent r * LaurentPolynomial.T (-(k : ℤ)), ?_⟩
    calc
      p = Polynomial.toLaurent q * LaurentPolynomial.T (-(k : ℤ)) := by
        rw [hq, mul_assoc, ← LaurentPolynomial.T_add]
        simp
      _ = (LaurentPolynomial.T (1 : ℤ) - LaurentPolynomial.C (a : R)) *
          (Polynomial.toLaurent r * LaurentPolynomial.T (-(k : ℤ))) := by
        rw [hr, map_mul, map_sub]
        simp only [Polynomial.toLaurent_X, Polynomial.toLaurent_C, mul_assoc]

/-- A nonempty open subset of the circle has infinitely many points. -/
theorem circle_infinite_of_isOpen {s : Set Circle}
    (hs : IsOpen s) (hne : s.Nonempty) : s.Infinite := by
  intro hfin
  have hsU : s = Set.univ := (IsClopen.eq_univ ⟨hfin.isClosed, hs⟩ hne)
  have hfinU : (Set.univ : Set Circle).Finite := hsU ▸ hfin
  exact infinite_range_circleToUnits
    (by simpa only [Set.image_univ] using hfinU.image Circle.toUnits)

/-- A Laurent polynomial vanishing on any nonempty open part of the unitary
torus vanishes identically, including the zero-dimensional torus. -/
theorem finiteLaurent_eq_zero_of_eval_unitary_open {n : ℕ}
    (p : AddMonoidAlgebra ℂ (Fin n → ℤ))
    {U : Set (Fin n → Circle)} (hU : IsOpen U) (hne : U.Nonempty)
    (hp : ∀ z ∈ U,
      finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) p = 0) :
    p = 0 := by
  classical
  obtain ⟨z, hz⟩ := hne
  obtain ⟨s, hs, hsU⟩ := isOpen_pi_iff'.mp hU z hz
  apply finiteLaurent_eq_zero_of_eval_on_box n
    (fun i => Circle.toUnits '' s i)
    (fun i => (circle_infinite_of_isOpen (hs i).1 ⟨z i, (hs i).2⟩).image
      (fun a ha b hb hab => Circle.coe_injective (congrArg Units.val hab))) p
  intro c hc
  choose w hw hwc using fun i => hc i (Set.mem_univ i)
  have hcw : c = fun i => Circle.toUnits (w i) := funext fun i => (hwc i).symm
  rw [hcw]
  exact hp w (hsU (fun i _ => hw i))

/-- Evaluate the first Laurent coordinate at a specified complex unit, keeping
all remaining coordinates as Laurent variables. -/
def finiteLaurentFirstEvaluation (n : ℕ) (a : ℂˣ) :
    AddMonoidAlgebra ℂ (Fin (n + 1) → ℤ) →+*
      AddMonoidAlgebra ℂ (Fin n → ℤ) :=
  (LaurentPolynomial.eval₂ (RingHom.id _)
    (Units.map (algebraMap ℂ (AddMonoidAlgebra ℂ (Fin n → ℤ))) a)).comp
      (finiteLaurentSuccessorEquiv ℂ n).toRingHom

/-- Evaluation after fixing the first coordinate agrees with full torus
evaluation. -/
theorem finiteLaurentEvaluation_firstEvaluation (n : ℕ) (a : ℂˣ)
    (c : Fin n → ℂˣ) (p : AddMonoidAlgebra ℂ (Fin (n + 1) → ℤ)) :
    finiteLaurentEvaluation c (finiteLaurentFirstEvaluation n a p) =
      finiteLaurentEvaluation (Fin.cons a c) p := by
  classical
  let R := AddMonoidAlgebra ℂ (Fin n → ℤ)
  let aR : Rˣ := Units.map (algebraMap ℂ R) a
  have hu (m : ℤ) :
      finiteLaurentEvaluation c ((aR ^ m : Rˣ) : R) = ((a ^ m : ℂˣ) : ℂ) := by
    dsimp only [aR]
    rw [← map_zpow, Units.coe_map]
    exact (finiteLaurentEvaluation c).commutes _
  have he (r : LaurentPolynomial R) :
      finiteLaurentEvaluation c (LaurentPolynomial.eval₂ (RingHom.id R) aR r) =
        LaurentPolynomial.eval₂ (finiteLaurentEvaluation c).toRingHom a r := by
    induction r using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add r s hr hs => simp only [map_add, hr, hs]
    | single m r =>
        simp only [LaurentPolynomial.single_eq_C_mul_T, map_mul,
          LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, RingHom.id_apply]
        rw [hu]
        rfl
  rw [finiteLaurentEvaluation_cons]
  exact he _

/-- The first-coordinate root factor `X₀ - a`, on the original finite Laurent
algebra rather than its iterated-polynomial presentation. -/
def finiteLaurentCoordinateRoot (n : ℕ) (a : ℂˣ) :
    AddMonoidAlgebra ℂ (Fin (n + 1) → ℤ) :=
  (finiteLaurentSuccessorEquiv ℂ n).symm
    (LaurentPolynomial.T (1 : ℤ) -
      LaurentPolynomial.C (algebraMap ℂ (AddMonoidAlgebra ℂ (Fin n → ℤ)) (a : ℂ)))

/-- Divisibility by the coordinate root is equivalent to identically zero
restriction to that algebraic coordinate hyperplane. -/
theorem finiteLaurentCoordinateRoot_dvd_iff (n : ℕ) (a : ℂˣ)
    (p : AddMonoidAlgebra ℂ (Fin (n + 1) → ℤ)) :
    finiteLaurentCoordinateRoot n a ∣ p ↔ finiteLaurentFirstEvaluation n a p = 0 := by
  rw [← map_dvd_iff (finiteLaurentSuccessorEquiv ℂ n),
    finiteLaurentCoordinateRoot, RingEquiv.apply_symm_apply]
  change LaurentPolynomial.T (1 : ℤ) -
      LaurentPolynomial.C (algebraMap ℂ (AddMonoidAlgebra ℂ (Fin n → ℤ)) (a : ℂ)) ∣
        finiteLaurentSuccessorEquiv ℂ n p ↔
    LaurentPolynomial.eval₂ (RingHom.id (AddMonoidAlgebra ℂ (Fin n → ℤ)))
      (Units.map (algebraMap ℂ (AddMonoidAlgebra ℂ (Fin n → ℤ))) a)
      (finiteLaurentSuccessorEquiv ℂ n p) = 0
  exact laurent_T_sub_C_dvd_iff_eval_eq_zero
    (R := AddMonoidAlgebra ℂ (Fin n → ℤ))
    (Units.map (algebraMap ℂ (AddMonoidAlgebra ℂ (Fin n → ℤ))) a)
    (finiteLaurentSuccessorEquiv ℂ n p)

/-- Vanishing on a nonempty open piece of the unitary coordinates in a
coordinate hyperplane forces algebraic divisibility by its root factor. -/
theorem finiteLaurentCoordinateRoot_dvd_of_eval_unitary_open
    {n : ℕ} (a : ℂˣ) (p : AddMonoidAlgebra ℂ (Fin (n + 1) → ℤ))
    {U : Set (Fin n → Circle)} (hU : IsOpen U) (hne : U.Nonempty)
    (hp : ∀ z ∈ U,
      finiteLaurentEvaluation (Fin.cons a (fun i => Circle.toUnits (z i))) p = 0) :
    finiteLaurentCoordinateRoot n a ∣ p := by
  apply (finiteLaurentCoordinateRoot_dvd_iff n a p).mpr
  apply finiteLaurent_eq_zero_of_eval_unitary_open _ hU hne
  intro z hz
  rw [finiteLaurentEvaluation_firstEvaluation]
  exact hp z hz

end Langlands.Plancherel
