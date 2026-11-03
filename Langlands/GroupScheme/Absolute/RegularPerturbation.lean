import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith

/-! # Integral regular directions and sign-preserving perturbations -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IntegralPerturbation

variable {Index : Type v} {M : Type w} [AddCommGroup M]

/-- One more than the largest absolute error in the given finite family. -/
def bound (f : Index → M →+ ℤ) (s : Finset Index) (eta : M) : ℕ :=
  s.sup (fun a => (f a eta).natAbs) + 1

theorem bound_pos (f : Index → M →+ ℤ) (s : Finset Index) (eta : M) :
    0 < bound f s eta := Nat.succ_pos _

theorem abs_lt_bound (f : Index → M →+ ℤ) (s : Finset Index) (eta : M) {a : Index}
    (ha : a ∈ s) : |f a eta| < (bound f s eta : ℤ) := by
  have h := Finset.le_sup (f := fun a => (f a eta).natAbs) ha
  have h' : (f a eta).natAbs < bound f s eta := Nat.lt_succ_of_le h
  rw [← Int.natCast_natAbs]
  exact_mod_cast h'

private theorem integer_signs {N a b : ℤ} (hN : 0 < N) (hb : |b| < N) :
    (0 < N * a + b ↔ 0 < a ∨ a = 0 ∧ 0 < b) ∧
      (N * a + b < 0 ↔ a < 0 ∨ a = 0 ∧ b < 0) ∧
      (N * a + b = 0 ↔ a = 0 ∧ b = 0) := by
  have hb' := abs_lt.mp hb
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have ha' : a ≤ -1 := by omega
    have hmul := mul_le_mul_of_nonneg_left ha' hN.le
    have hneg : N * a + b < 0 := by nlinarith
    constructor
    · constructor <;> intro h
      · exact False.elim ((not_lt_of_ge hneg.le) h)
      · rcases h with h | ⟨h, _⟩ <;> omega
    · constructor
      · exact ⟨fun _ => Or.inl ha, fun _ => hneg⟩
      · constructor <;> intro h
        · omega
        · omega
  · simp
  · have ha' : 1 ≤ a := by omega
    have hmul := mul_le_mul_of_nonneg_left ha' hN.le
    have hpos : 0 < N * a + b := by nlinarith
    constructor
    · exact ⟨fun _ => Or.inl ha, fun _ => hpos⟩
    · constructor
      · constructor <;> intro h
        · exact False.elim ((not_lt_of_ge hpos.le) h)
        · rcases h with h | ⟨h, _⟩ <;> omega
      · constructor <;> intro h <;> omega

/-- At or above the finite bound, signs are ordered lexicographically by the
main direction and then by the error direction. -/
theorem signs (f : Index → M →+ ℤ) (s : Finset Index) (mu eta : M) {N : ℕ}
    (hN : bound f s eta ≤ N) {a : Index} (ha : a ∈ s) :
    (0 < f a (N • mu + eta) ↔ 0 < f a mu ∨ f a mu = 0 ∧ 0 < f a eta) ∧
      (f a (N • mu + eta) < 0 ↔ f a mu < 0 ∨ f a mu = 0 ∧ f a eta < 0) ∧
      (f a (N • mu + eta) = 0 ↔ f a mu = 0 ∧ f a eta = 0) := by
  have hNpos : 0 < N := lt_of_lt_of_le (bound_pos f s eta) hN
  have hb : |f a eta| < (N : ℤ) :=
    lt_of_lt_of_le (abs_lt_bound f s eta ha) (by exact_mod_cast hN)
  simpa only [map_add, map_nsmul, nsmul_eq_mul] using
    integer_signs (a := f a mu) (by exact_mod_cast hNpos) hb

/-- A finite family of nonzero integral linear forms has a simultaneous
regular direction. -/
theorem exists_regular (f : Index → M →+ ℤ) (s : Finset Index)
    (hf : ∀ a ∈ s, f a ≠ 0) :
    ∃ eta : M, ∀ a ∈ s, f a eta ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨eta, heta⟩ := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    obtain ⟨mu, hmu⟩ : ∃ mu : M, f a mu ≠ 0 := by
      by_contra h
      apply hf a (Finset.mem_insert_self a s)
      ext x
      simpa using not_exists.mp h x
    by_cases hetaa : f a eta = 0
    · refine ⟨bound f s mu • eta + mu, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · simpa [map_add, map_nsmul, hetaa] using hmu
      · intro hzero
        exact heta b hb (((signs f s eta mu le_rfl hb).2.2.mp hzero).1)
    · exact ⟨eta, fun b hb => (Finset.mem_insert.mp hb).elim
        (fun h => h ▸ hetaa) (fun h => heta b h)⟩

/-- Perturbing by a regular error direction makes the result regular, and
every nonnegative form for the result was nonnegative on the main direction. -/
theorem regular_and_nonneg (f : Index → M →+ ℤ) (s : Finset Index) (mu eta : M)
    (heta : ∀ a ∈ s, f a eta ≠ 0) {N : ℕ} (hN : bound f s eta ≤ N) :
    (∀ a ∈ s, f a (N • mu + eta) ≠ 0) ∧
      (∀ a ∈ s, 0 ≤ f a (N • mu + eta) → 0 ≤ f a mu) := by
  constructor
  · intro a ha hzero
    exact heta a ha (((signs f s mu eta hN ha).2.2.mp hzero).2)
  · intro a ha hnonneg
    by_contra h
    have hneg := (signs f s mu eta hN ha).2.1.mpr (Or.inl (lt_of_not_ge h))
    exact (not_lt_of_ge hnonneg) hneg

end IntegralPerturbation

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Every split torus has a perfect pairing on its actual character lattices. -/
theorem IsSplitTorus.isPerfPair_latticePairing (hT : IsSplitTorus T.toGrp) :
    (latticePairing T).IsPerfPair := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let _ := hI
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  refine LinearMap.IsPerfPair.congr (characterLattice.congr eC).toIntLinearEquiv
    (cocharacterLattice.congr eC).toIntLinearEquiv (latticePairing T)
    (p := latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)) ?_
  ext alpha nu
  exact (latticePairing_congr eC.symm alpha nu)

/-- Any finite set of nonzero characters of a split torus admits a regular
cocharacter on the actual cocharacter lattice. -/
theorem IsSplitTorus.exists_regular_on_finite (hT : IsSplitTorus T.toGrp)
    (r : Set (characterLattice T)) (hr : r.Finite) (h0 : ∀ alpha ∈ r, alpha ≠ 0) :
    ∃ eta : cocharacterLattice T, ∀ alpha ∈ r, latticePairing T alpha eta ≠ 0 := by
  classical
  have hf : ∀ alpha ∈ hr.toFinset, (latticePairing T alpha).toAddMonoidHom ≠ 0 := by
    intro alpha halpha hzero
    apply h0 alpha (hr.mem_toFinset.mp halpha)
    apply hT.isPerfPair_latticePairing.separatingLeft alpha
    intro nu
    exact congrArg (fun f : cocharacterLattice T →+ ℤ => f nu) hzero
  obtain ⟨eta, heta⟩ := IntegralPerturbation.exists_regular
    (fun alpha : characterLattice T => (latticePairing T alpha).toAddMonoidHom) hr.toFinset hf
  exact ⟨eta, fun alpha halpha => heta alpha (hr.mem_toFinset.mpr halpha)⟩

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- A split torus with finitely many actual roots has a regular cocharacter. -/
theorem IsSplitTorus.exists_regularCocharacter (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) (hr : (roots j).Finite) :
    ∃ eta : cocharacterLattice T, IsRegularCocharacter j eta :=
  hT.exists_regular_on_finite (roots j) hr (fun _ halpha => halpha.1)

/-- A sufficiently large positive multiple of any cocharacter plus a regular
cocharacter is regular, with no new nonnegative root pairings. -/
theorem exists_regularCocharacter_perturbation (j : T.toGrp ⟶ G)
    (hr : (roots j).Finite) (mu eta : cocharacterLattice T) (heta : IsRegularCocharacter j eta) :
    ∃ N : ℕ, 0 < N ∧ IsRegularCocharacter j (N • mu + eta) ∧
      ∀ alpha ∈ roots j, 0 ≤ latticePairing T alpha (N • mu + eta) →
        0 ≤ latticePairing T alpha mu := by
  classical
  let f := fun alpha : characterLattice T => (latticePairing T alpha).toAddMonoidHom
  let s := hr.toFinset
  have heta' : ∀ alpha ∈ s, f alpha eta ≠ 0 := fun alpha halpha => heta alpha (hr.mem_toFinset.mp halpha)
  have h := IntegralPerturbation.regular_and_nonneg f s mu eta heta' le_rfl
  refine ⟨IntegralPerturbation.bound f s eta, IntegralPerturbation.bound_pos f s eta, ?_, ?_⟩
  · exact fun alpha halpha => h.1 alpha (hr.mem_toFinset.mpr halpha)
  · exact fun alpha halpha => h.2 alpha (hr.mem_toFinset.mpr halpha)

end Langlands.GroupScheme
