import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Derivative.Iteration
import Langlands.Group.GL.MirabolicOppositeIntersection
import Langlands.Group.GL.Maps

/-!
# Vanishing of the intermediate derivatives of a supercuspidal representation

For `0 < k < N`, the derivative of order `k` of a smooth representation `A` of `GL_N` is
a quotient of `A` on which the unipotent radical of the standard two-block parabolic
`(N - k, k)` acts trivially. The Jacquet module for that parabolic is zero when `A` is
supercuspidal, so the derivative is zero.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Classification.SupercuspidalDerivativeVanishing

open GeneralLinear GeneralLinear.Mirabolic Derivative Derivative.Mirabolic HarmonicAnalysis

universe uF uV u

/-! ## Block unipotent matrices -/

section Matrices

variable {R : Type u} [CommRing R]

/-- `g = [[I_m, Y], [0, I]]`: the first `m` columns and the rows from `m` on are
those of the identity matrix. -/
def IsBlockUnipotent {N : ℕ} (m : ℕ) (g : GeneralLinear N R) : Prop :=
  ∀ i j : Fin N, (j.val < m ∨ m ≤ i.val) → g.val i j = if i = j then 1 else 0

/-- A block unipotent matrix is upper unipotent. -/
theorem mem_upperUnipotent_of_isBlockUnipotent {N m : ℕ} {g : GeneralLinear N R}
    (hg : IsBlockUnipotent m g) : g ∈ GeneralLinear.upperUnipotent N R := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · have hij : i ≠ j := ne_of_gt hji
    have hji' : j.val < i.val := hji
    by_cases hj : j.val < m
    · rw [hg i j (Or.inl hj), ite_eq_right hij]
    · rw [hg i j (Or.inr (by omega)), ite_eq_right hij]
  · by_cases hi : i.val < m
    · rw [hg i i (Or.inl hi), ite_eq_left rfl]
    · rw [hg i i (Or.inr (by omega)), ite_eq_left rfl]

/-- A block unipotent matrix with `m ≤ n` lies in the mirabolic subgroup of `GL_(n+1)`. -/
theorem mem_mirabolic_of_isBlockUnipotent {n m : ℕ} (hmn : m ≤ n)
    {g : GeneralLinear (n + 1) R} (hg : IsBlockUnipotent m g) : g ∈ mirabolic n R := by
  intro j
  rw [hg (Fin.last n) j (Or.inr (by simpa using hmn))]
  by_cases hj : j = Fin.last n
  · subst hj
    simp
  · rw [ite_eq_right (Ne.symm hj), ite_eq_right hj]

/-- In `P_(m+1)`, a block unipotent element lies in the radical `V_(m+1)`. -/
theorem mem_radical_of_isBlockUnipotent {m : ℕ} {g : mirabolic m R}
    (hg : IsBlockUnipotent m g.val) : g ∈ radical m R := by
  intro i j
  exact hg i j.castSucc (Or.inl (by simp))

/-- An element of the unipotent radical of the two-block parabolic `(m, c)` is block
unipotent. -/
theorem isBlockUnipotent_of_mem_binary {m c : ℕ} (hm : 0 < m) (hc : 0 < c)
    {g : GeneralLinear (m + c) R}
    (hg : g ∈ (BlockShape.binary m c hm hc).unipotentSubgroup R) :
    IsBlockUnipotent m g := by
  rw [BlockShape.mem_unipotentSubgroup_iff] at hg
  obtain ⟨hP, hD⟩ := hg
  rw [BlockShape.mem_parabolic_iff] at hP
  have h00 : ∀ a b : Fin m, g.val (Fin.castAdd c a) (Fin.castAdd c b) =
      if a = b then 1 else 0 := by
    intro a b
    have := hD (0 : Fin 2) a b
    simp only [BlockShape.binary_index_zero] at this
    exact this
  have h11 : ∀ a b : Fin c, g.val (Fin.natAdd m a) (Fin.natAdd m b) =
      if a = b then 1 else 0 := by
    intro a b
    have := hD (1 : Fin 2) a b
    simp only [BlockShape.binary_index_one] at this
    exact this
  have h10 : ∀ (a : Fin c) (b : Fin m), g.val (Fin.natAdd m a) (Fin.castAdd c b) = 0 := by
    intro a b
    have := hP (1 : Fin 2) (0 : Fin 2) a b (show (0 : Fin 2) < 1 from by decide)
    simp only [BlockShape.binary_index_zero, BlockShape.binary_index_one] at this
    exact this
  intro i j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;> intro hij
  · rw [h00 a b]
    simp [Fin.castAdd_inj]
  · exfalso
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hij
    have := a.isLt
    omega
  · rw [h10 a b]
    have hne : Fin.natAdd m a ≠ Fin.castAdd c b := by
      intro h
      have hb := b.isLt
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    rw [ite_eq_right hne]
  · rw [h11 a b]
    simp [Fin.natAdd_inj]

/-- The two-block parabolic `(m, c)` with positive blocks is proper. -/
theorem binary_parabolic_ne_top [Nontrivial R] {m c : ℕ} (hm : 0 < m) (hc : 0 < c) :
    (BlockShape.binary m c hm hc).parabolic R ≠ ⊤ := by
  intro htop
  let a : Fin c := ⟨0, hc⟩
  let b : Fin m := ⟨0, hm⟩
  let w := Equiv.swap (Fin.natAdd m a) (Fin.castAdd c b)
  have hw : permutation (m + c) R w ∈ (BlockShape.binary m c hm hc).parabolic R :=
    htop ▸ Subgroup.mem_top _
  have hz := ((BlockShape.binary m c hm hc).mem_parabolic_iff R _).mp hw
    (1 : Fin 2) (0 : Fin 2) a b (show (0 : Fin 2) < 1 from by decide)
  simp only [BlockShape.binary_index_zero, BlockShape.binary_index_one] at hz
  have hone : permutation (m + c) R w (Fin.natAdd m a) (Fin.castAdd c b) = 1 := by
    rw [permutation_entry, ite_eq_left]
    exact Equiv.swap_apply_right _ _
  exact one_ne_zero (hone.symm.trans hz)

/-- A mirabolic element of `P_(n+2)` whose last column and penultimate row are standard
comes from `P_(n+1)`. -/
theorem exists_successor_eq {n : ℕ} (s : mirabolic (n + 1) R)
    (hcol : ∀ i : Fin (n + 1), s.val.val i.castSucc (Fin.last (n + 1)) = 0)
    (hrow : ∀ j : Fin (n + 1),
      s.val.val (Fin.last n).castSucc j.castSucc = if j = Fin.last n then 1 else 0) :
    ∃ h : mirabolic n R, successor h = s := by
  have hbot : ∀ j : Fin (n + 1), s.val.val (Fin.last (n + 1)) j.castSucc = 0 := by
    intro j
    rw [s.property j.castSucc, ite_eq_right (Fin.castSucc_ne_last j)]
  let H : GeneralLinear (n + 1) R :=
    { val := Matrix.of fun i j => s.val.val i.castSucc j.castSucc
      inv := Matrix.of fun i j => s.val.inv i.castSucc j.castSucc
      val_inv := by
        ext i j
        have h1 := congrArg (fun M : Matrix (Fin (n + 2)) (Fin (n + 2)) R =>
          M i.castSucc j.castSucc) s.val.val_inv
        rw [Matrix.mul_apply, Fin.sum_univ_castSucc] at h1
        simp only [hcol, zero_mul, add_zero, Matrix.one_apply, Fin.castSucc_inj] at h1
        simpa only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] using h1
      inv_val := by
        ext i j
        have h1 := congrArg (fun M : Matrix (Fin (n + 2)) (Fin (n + 2)) R =>
          M i.castSucc j.castSucc) s.val.inv_val
        rw [Matrix.mul_apply, Fin.sum_univ_castSucc] at h1
        simp only [hbot, mul_zero, add_zero, Matrix.one_apply, Fin.castSucc_inj] at h1
        simpa only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] using h1 }
  have hH : H ∈ mirabolic n R := by
    intro j
    exact hrow j
  refine ⟨⟨H, hH⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [(successor (⟨H, hH⟩ : mirabolic n R)).property (Fin.last (n + 1)),
      s.property (Fin.last (n + 1))]
  · rw [(successor (⟨H, hH⟩ : mirabolic n R)).property j.castSucc,
      s.property j.castSucc]
  · rw [successor_last, hcol]
  · rw [successor_first]
    rfl

/-- A block unipotent element of `P_(n+2)` is a radical element with vanishing last
coordinate times the successor image of a block unipotent element of `P_(n+1)`. -/
theorem exists_radical_mul_successor {n m : ℕ} (hmn : m ≤ n) (g : mirabolic (n + 1) R)
    (hg : IsBlockUnipotent m g.val) :
    ∃ (g' : mirabolic n R) (c : Fin (n + 1) → R), c (Fin.last n) = 0 ∧
      IsBlockUnipotent m g'.val ∧
      g = ((radicalElement c : radical (n + 1) R) : mirabolic (n + 1) R) * successor g' := by
  let c : Fin (n + 1) → R := fun i => g.val.val i.castSucc (Fin.last (n + 1))
  let r : mirabolic (n + 1) R := (radicalElement c : radical (n + 1) R)
  let r' : mirabolic (n + 1) R := (radicalElement (-c) : radical (n + 1) R)
  have hrr' : r * r' = 1 := by
    have h := radicalElement_add c (-c)
    rw [add_neg_cancel, radicalElement_zero] at h
    exact congrArg Subtype.val h.symm
  let s := r' * g
  have hs : ∀ (i : Fin (n + 1)) (j : Fin (n + 2)),
      s.val.val i.castSucc j =
        g.val.val i.castSucc j + (-c i) * g.val.val (Fin.last (n + 1)) j := by
    intro i j
    change ((radicalElement (-c)).val.val.val * g.val.val) i.castSucc j = _
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp only [radicalElement_first, radicalElement_last, Pi.neg_apply, ite_mul, one_mul,
      zero_mul, Fin.castSucc_inj, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hs' : ∀ i j : Fin (n + 1), s.val.val i.castSucc j.castSucc =
      g.val.val i.castSucc j.castSucc := by
    intro i j
    rw [hs, g.property j.castSucc, ite_eq_right (Fin.castSucc_ne_last j), mul_zero, add_zero]
  have hcol : ∀ i : Fin (n + 1), s.val.val i.castSucc (Fin.last (n + 1)) = 0 := by
    intro i
    rw [hs, g.property (Fin.last (n + 1)), ite_eq_left rfl, mul_one]
    exact add_neg_cancel _
  have hrow : ∀ j : Fin (n + 1),
      s.val.val (Fin.last n).castSucc j.castSucc = if j = Fin.last n then 1 else 0 := by
    intro j
    rw [hs', hg _ _ (Or.inr (by simpa using hmn))]
    simp only [Fin.castSucc_inj, eq_comm]
  obtain ⟨g', hg'⟩ := exists_successor_eq s hcol hrow
  refine ⟨g', c, ?_, ?_, ?_⟩
  · change g.val.val (Fin.last n).castSucc (Fin.last (n + 1)) = 0
    rw [hg _ _ (Or.inr (by simpa using hmn)), ite_eq_right (Fin.castSucc_ne_last _)]
  · intro i j hij
    have he : g'.val.val i j = s.val.val i.castSucc j.castSucc := by
      rw [← hg', successor_first]
    rw [he, hs', hg _ _ (by simpa using hij)]
    simp only [Fin.castSucc_inj]
  · rw [hg']
    change g = r * (r' * g)
    rw [← mul_assoc, hrr', one_mul]

end Matrices

/-! ## The iterated quotient map -/

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The composite quotient map `X → (Φ⁻)^j X`, applying the largest-rank quotient first. -/
def iterateQuotient (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ) :
    (j : ℕ) → letI := T.topology
      (X : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + j) F.Carrier)) →
        X →ₗ[ℂ] (phiMinusIterate T ψ m j).obj X
  | 0 => fun _ => LinearMap.id
  | j + 1 => fun X => letI := T.topology
      iterateQuotient T ψ m j ((phiMinus T ψ (m + j)).obj X) ∘ₗ phiMinusQuotient T ψ (m + j) X

theorem iterateQuotient_surjective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ) :
    ∀ (j : ℕ), letI := T.topology
      ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + j) F.Carrier),
        Function.Surjective (iterateQuotient T ψ m j X)
  | 0 => fun _ => Function.surjective_id
  | j + 1 => fun X => by
      let _ := T.topology
      exact (iterateQuotient_surjective T ψ m j ((phiMinus T ψ (m + j)).obj X)).comp
        (phiMinusQuotient_surjective T ψ (m + j) X)

/-- The `Φ⁻` normalization character is trivial on block unipotent elements. -/
theorem phiMinusCharacter_eq_one (T : F.TopologicalData) {n m : ℕ} (g : mirabolic n F.Carrier)
    (hg : IsBlockUnipotent m g.val) :
    realPowerCharacter ((T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype)
      (-(1 / 2 : ℝ)) g = 1 := by
  have hdet : GeneralLinear.determinant g.val = 1 := by
    have hu := mem_upperUnipotent_of_isBlockUnipotent hg
    exact Units.ext (by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
        Matrix.det_of_isUpperTriangular hu.1, Finset.prod_eq_one fun i _ => hu.2 i])
  have hnorm : (T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype g = 1 := by
    change T.normalizedAbsUnits (GeneralLinear.determinant g.val) = 1
    rw [hdet, map_one]
  unfold realPowerCharacter
  rw [MonoidHom.comp_apply, hnorm, map_one]

/-- The composite quotient `X → Ψ⁻ (Φ⁻)^j X` is invariant under every block unipotent
`[[I_m, Y], [0, I_(j+1)]]` in `P_(m+j+1)`. -/
theorem psiMinusQuotient_iterateQuotient_invariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ) :
    ∀ (j : ℕ), letI := T.topology
      ∀ (X : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + j) F.Carrier))
        (g : mirabolic (m + j) F.Carrier), IsBlockUnipotent m g.val → ∀ v : X,
          psiMinusQuotient T m ((phiMinusIterate T ψ m j).obj X)
              (iterateQuotient T ψ m j X (X.representation g v)) =
            psiMinusQuotient T m ((phiMinusIterate T ψ m j).obj X)
              (iterateQuotient T ψ m j X v)
  | 0 => fun X g hg v => by
      let _ := T.topology
      exact psiMinusQuotient_radical T m X ⟨g, mem_radical_of_isBlockUnipotent hg⟩ v
  | j + 1 => fun X g hg v => by
      let _ := T.topology
      obtain ⟨g', c, hc, hg', rfl⟩ :=
        exists_radical_mul_successor (n := m + j) (Nat.le_add_right m j) g hg
      have hq : ∀ w : X,
          phiMinusQuotient T ψ (m + j) X (X.representation
              (((radicalElement c : radical (m + j + 1) F.Carrier) :
                mirabolic (m + j + 1) F.Carrier) * successor g') w) =
            ((phiMinus T ψ (m + j)).obj X).representation g'
              (phiMinusQuotient T ψ (m + j) X w) := by
        intro w
        rw [map_mul, Module.End.mul_apply, phiMinusQuotient_radical, phiMinus_action,
          phiMinusCharacter_eq_one T g' hg', Units.val_one, one_smul]
        have ht : (T.mirabolicTheta ψ (m + j) (radicalElement c) : ℂ) = 1 := by
          change (Derivative.Mirabolic.theta ψ (m + j) (radicalElement c) : ℂ) = 1
          rw [theta_radicalElement, hc, AddChar.map_zero_eq_one]
        rw [ht, one_smul]
      change psiMinusQuotient T m ((phiMinusIterate T ψ m j).obj ((phiMinus T ψ (m + j)).obj X))
          (iterateQuotient T ψ m j ((phiMinus T ψ (m + j)).obj X)
            (phiMinusQuotient T ψ (m + j) X (X.representation _ v))) =
        psiMinusQuotient T m ((phiMinusIterate T ψ m j).obj ((phiMinus T ψ (m + j)).obj X))
          (iterateQuotient T ψ m j ((phiMinus T ψ (m + j)).obj X)
            (phiMinusQuotient T ψ (m + j) X v))
      rw [hq]
      exact psiMinusQuotient_iterateQuotient_invariant T ψ m j _ g' hg' _

/-! ## Vanishing of the intermediate derivatives -/

/-- A positive derivative `GL_(m+j+1) → GL_m` with `m > 0` of a supercuspidal
representation is zero. -/
theorem subsingleton_generalLinearDerivativePositive (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m j : ℕ) (hm : 0 < m) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + j + 1) F.Carrier),
      IsSupercuspidal A.representation →
        Subsingleton ((generalLinearDerivativePositive T ψ m j).obj A) := by
  let _ := T.topology
  intro A hA
  let X := (generalLinearRestriction T (m + j)).obj A
  let tot : A →ₗ[ℂ] (generalLinearDerivativePositive T ψ m j).obj A :=
    psiMinusQuotient T m ((phiMinusIterate T ψ m j).obj X) ∘ₗ iterateQuotient T ψ m j X
  have hsurj : Function.Surjective tot :=
    (psiMinusQuotient_surjective T m _).comp (iterateQuotient_surjective T ψ m j X)
  let B : BlockShape (m + j + 1) := BlockShape.binary m (j + 1) hm (Nat.succ_pos j)
  have hJ := hA.2 B (binary_parabolic_ne_top (R := F.Carrier) hm (Nat.succ_pos j)) 1
  have hinv : ∀ u : B.conjugateUnipotent 1, tot ∘ₗ A.representation u.val = tot := by
    rintro ⟨u, hu⟩
    apply LinearMap.ext
    intro v
    have hu' : u ∈ B.unipotentSubgroup F.Carrier := by
      obtain ⟨u', hu', rfl⟩ := hu
      simpa using hu'
    have hb := isBlockUnipotent_of_mem_binary (c := j + 1) hm (Nat.succ_pos j) hu'
    have hP : u ∈ mirabolic (m + j) F.Carrier :=
      mem_mirabolic_of_isBlockUnipotent (Nat.le_add_right m j) hb
    exact psiMinusQuotient_iterateQuotient_invariant T ψ m j X ⟨u, hP⟩ hb v
  refine ⟨fun x y => ?_⟩
  obtain ⟨v, rfl⟩ := hsurj x
  obtain ⟨w, rfl⟩ := hsurj y
  have hl := Jacquet.lift_mk A.representation (B.conjugateUnipotent 1) tot hinv
  rw [← hl v, ← hl w,
    Subsingleton.elim (Jacquet.mk A.representation (B.conjugateUnipotent 1) v)
      (Jacquet.mk A.representation (B.conjugateUnipotent 1) w)]

/-- Rank transport preserves supercuspidality. -/
theorem isSupercuspidal_rankCast (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier),
      IsSupercuspidal A.representation →
        IsSupercuspidal ((generalLinearRankCast T h).obj A).representation := by
  subst h
  intro A hA
  exact hA

/-- BZ77 §4.4, vanishing part: for `0 < k < N`, the derivative of order `k` of a
supercuspidal representation of `GL_N` is zero. -/
theorem subsingleton_generalLinearDerivative (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N k : ℕ) (hk : k ≤ N)
    (hpos : 0 < k) (hlt : k < N) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier),
      IsSupercuspidal A.representation →
        Subsingleton ((generalLinearDerivative T ψ N k hk).obj A) := by
  let _ := T.topology
  intro A hA
  rw [generalLinearDerivative_of_pos T ψ N k hk hpos]
  exact subsingleton_generalLinearDerivativePositive T ψ (N - k) (k - 1) (by omega) _
    (isSupercuspidal_rankCast T (rank_eq_of_pos_le hk hpos) A hA)

end Langlands.Classification.SupercuspidalDerivativeVanishing
