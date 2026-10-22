import Langlands.WeilDeligne.SumsTensor
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Tactic.Ring

/-! # Uncentered special blocks with raising monodromy -/

noncomputable section

universe uK uG uV

namespace Langlands.WeilDeligneRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

open scoped TensorProduct

namespace Special

/-- The coordinate representation with weights `1, ν, ..., ν^(m-1)`. -/
def action (ν : G →* Kˣ) (m : ℕ) : Representation K G (Fin m → K) where
  toFun g := LinearMap.pi fun j => (ν g : K) ^ j.val • LinearMap.proj j
  map_one' := by
    ext v j
    simp
  map_mul' g h := by
    ext v j
    simp [mul_pow, mul_assoc]

@[simp]
theorem action_apply (ν : G →* Kˣ) (m : ℕ) (g : G) (v : Fin m → K) (j : Fin m) :
    action ν m g v j = (ν g : K) ^ j.val * v j := rfl

/-- Raising monodromy: the coordinate at `j>0` is the old coordinate at `j-1`. -/
def raising (K : Type uK) [Field K] (m : ℕ) : Module.End K (Fin m → K) :=
  LinearMap.pi fun j =>
    if h : 0 < j.val then LinearMap.proj ⟨j.val - 1, by omega⟩ else 0

@[simp]
theorem raising_apply (m : ℕ) (v : Fin m → K) (j : Fin m) :
    raising K m v j = if h : 0 < j.val then v ⟨j.val - 1, by omega⟩ else 0 := by
  by_cases h : 0 < j.val <;> simp [raising, h]

/-- Each application of raising monodromy removes one more bottom coordinate. -/
theorem raising_pow_apply_eq_zero (m k : ℕ) (v : Fin m → K) (j : Fin m)
    (h : j.val < k) : (raising K m ^ k) v j = 0 := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    rw [pow_succ']
    change raising K m ((raising K m ^ k) v) j = 0
    rw [raising_apply]
    split
    · apply ih
      change j.val - 1 < k
      omega
    · rfl

/-- The explicit exponent `m` kills the raising endomorphism, also when `m=0`. -/
theorem raising_pow (m : ℕ) : raising K m ^ m = 0 := by
  apply LinearMap.ext
  intro v
  funext j
  exact raising_pow_apply_eq_zero m m v j j.isLt

/-- The coordinate basis vector at the specified weight. -/
def basisVector (K : Type uK) [Field K] {m : ℕ} (j : Fin m) : Fin m → K :=
  fun k => if k = j then 1 else 0

/-- The last coordinate vector in a positive-rank block. -/
def topVector (K : Type uK) [Field K] (n : ℕ) : Fin (n + 1) → K :=
  basisVector K (Fin.last n)

/-- The monodromy kernel consists exactly of vectors supported at the top weight. -/
theorem raising_eq_zero_iff (n : ℕ) (v : Fin (n + 1) → K) :
    raising K (n + 1) v = 0 ↔ ∀ j : Fin (n + 1), j.val < n → v j = 0 := by
  constructor
  · intro h j hj
    have hv := congrFun h (⟨j.val + 1, by omega⟩ : Fin (n + 1))
    simpa [raising_apply] using hv
  · intro h
    funext j
    rw [raising_apply]
    split
    · apply h
      change j.val - 1 < n
      omega
    · rfl

/-- The kernel is the top-weight line, rather than the bottom-weight line. -/
theorem ker_raising (n : ℕ) :
    LinearMap.ker (raising K (n + 1)) = Submodule.span K {topVector K n} := by
  ext v
  rw [LinearMap.mem_ker, raising_eq_zero_iff, Submodule.mem_span_singleton]
  constructor
  · intro h
    refine ⟨v (Fin.last n), ?_⟩
    funext j
    by_cases hj : j = Fin.last n
    · subst j
      simp [topVector, basisVector]
    · have hj' : j.val < n := by
        have hne : j.val ≠ n := by
          intro he
          apply hj
          exact Fin.ext he
        omega
      simp [topVector, basisVector, hj, h j hj']
  · rintro ⟨a, rfl⟩ j hj
    have hne : j ≠ Fin.last n := by
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_last] at this
      omega
    simp [topVector, basisVector, hne]

/-- The action on each coordinate basis vector has its specified uncentered weight. -/
theorem action_basisVector (ν : G →* Kˣ) (m : ℕ) (g : G) (j : Fin m) :
    action ν m g (basisVector K j) = (ν g : K) ^ j.val • basisVector K j := by
  funext k
  by_cases h : k = j
  · subst k
    simp [basisVector]
  · simp [basisVector, h]

/-- The last coordinate has the highest weight `ν^n`. -/
theorem action_topVector (ν : G →* Kˣ) (n : ℕ) (g : G) :
    action ν (n + 1) g (topVector K n) = (ν g : K) ^ n • topVector K n :=
  action_basisVector ν (n + 1) g (Fin.last n)

/-- Monodromy sends each non-top basis vector to the next one. -/
theorem raising_basisVector (n : ℕ) (j : Fin n) :
    raising K (n + 1) (basisVector K j.castSucc) = basisVector K j.succ := by
  funext k
  rw [raising_apply]
  by_cases hk : 0 < k.val
  · rw [dite_eq_left hk]
    have heq : (⟨k.val - 1, by omega⟩ : Fin (n + 1)) = j.castSucc ↔ k = j.succ := by
      simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
      omega
    simp only [basisVector, heq]
  · have hne : k ≠ j.succ := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_succ] at hv
      omega
    simp [hk, basisVector, hne]

/-- The top basis vector is killed by monodromy. -/
theorem raising_topVector (n : ℕ) : raising K (n + 1) (topVector K n) = 0 := by
  apply (raising_eq_zero_iff n _).mpr
  intro j hj
  have hne : j ≠ Fin.last n := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_last] at hv
    omega
  simp [topVector, basisVector, hne]

/-- Blocks of rank at least two have genuinely nonzero monodromy. -/
theorem raising_ne_zero (n : ℕ) : raising K (n + 2) ≠ 0 := by
  intro h
  have hv := raising_basisVector (K := K) (n + 1) (0 : Fin (n + 1))
  rw [h] at hv
  have hc := congrFun hv ((0 : Fin (n + 1)).succ)
  simp [basisVector] at hc

/-- The uncentered weights and raising direction give the specified norm covariance. -/
theorem covariance (ν : G →* Kˣ) (m : ℕ) (g : G) :
    action ν m g * raising K m * action ν m g⁻¹ = (ν g : K) • raising K m := by
  apply LinearMap.ext
  intro v
  funext j
  change (ν g : K) ^ j.val * raising K m (action ν m g⁻¹ v) j =
    (ν g : K) * raising K m v j
  simp only [raising_apply]
  split
  · rename_i hj
    rw [action_apply]
    have hj' : j.val = (j.val - 1) + 1 := by omega
    have hc : (ν g : K) * (ν g⁻¹ : K) = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    calc
      (ν g : K) ^ j.val * ((ν g⁻¹ : K) ^ (j.val - 1) * v ⟨j.val - 1, by omega⟩) =
          (ν g : K) *
            (((ν g : K) * (ν g⁻¹ : K)) ^ (j.val - 1) * v ⟨j.val - 1, by omega⟩) := by
              conv_lhs => arg 1; rw [hj', pow_succ]
              rw [mul_pow]
              ring
      _ = (ν g : K) * v ⟨j.val - 1, by omega⟩ := by rw [hc]; simp
  · simp

end Special

/-- The actual uncentered special block `S_m`, allowing `m=0` internally. -/
def specialBlock (ν : G →* Kˣ) (m : ℕ) : WeilDeligneRepresentation.{uK, uG, uK} K G ν where
  toFiniteRepresentation := FiniteRepresentation.of (Special.action ν m)
  monodromy := Special.raising K m
  nilpotent := ⟨m, Special.raising_pow m⟩
  covariance := Special.covariance ν m

@[simp]
theorem rank_specialBlock (ν : G →* Kˣ) (m : ℕ) :
    (specialBlock ν m).rank = m := Module.finrank_fin_fun K

/-- The actual pair has the top-weight kernel in positive rank. -/
theorem ker_specialBlock (ν : G →* Kˣ) (n : ℕ) :
    LinearMap.ker (specialBlock ν (n + 1)).monodromy =
      Submodule.span K {Special.topVector K n} :=
  Special.ker_raising n

/-- The actual pair has nonzero monodromy in every rank at least two. -/
theorem specialBlock_monodromy_ne_zero (ν : G →* Kˣ) (n : ℕ) :
    (specialBlock ν (n + 2)).monodromy ≠ 0 :=
  Special.raising_ne_zero n

/-- A block with specified Weil representation and length, without a decomposition assertion. -/
def block (ν : G →* Kˣ) (A : FiniteRepresentation.{uK, uG, uV} K G) (m : ℕ) :
    WeilDeligneRepresentation.{uK, uG, max uV uK} K G ν :=
  tensor (zeroMonodromy ν A) (specialBlock ν m)

@[simp]
theorem rank_block (ν : G →* Kˣ) (A : FiniteRepresentation.{uK, uG, uV} K G) (m : ℕ) :
    (block ν A m).rank = A.rank * m := by
  change Module.finrank K (TensorProduct K A (Fin m → K)) = A.rank * m
  rw [Module.finrank_tensorProduct, Module.finrank_fin_fun]
  rfl

/-- Monodromy acts only on the special-block factor. -/
theorem block_monodromy_tmul (ν : G →* Kˣ)
    (A : FiniteRepresentation.{uK, uG, uV} K G) (m : ℕ)
    (v : A) (w : Fin m → K) :
    (block ν A m).monodromy (v ⊗ₜ[K] w) = v ⊗ₜ[K] Special.raising K m w := by
  change (TensorProduct.map (0 : Module.End K A) (1 : Module.End K (Fin m → K)) +
    TensorProduct.map (1 : Module.End K A) (Special.raising K m)) (v ⊗ₜ[K] w) = _
  simp

/-- An equivalence of the Weil factors gives a genuine equivalence of the specified blocks. -/
def blockEquiv (ν : G →* Kˣ) {A B : FiniteRepresentation.{uK, uG, uV} K G}
    (e : FiniteRepresentation.Equiv A B) (m : ℕ) : Equiv (block ν A m) (block ν B m) :=
  tensorEquiv
    (Equiv.ofIso ((zeroMonodromyFunctor ν).mapIso (FiniteRepresentation.isoOfEquiv e)))
    (Equiv.refl (specialBlock ν m))

/-- Specified blocks descend to genuine isomorphism classes of Weil factors. -/
def blockClass (ν : G →* Kˣ) (m : ℕ) :
    FiniteRepresentation.IsomorphismClasses.{uK, uG, uV} K G →
      IsomorphismClasses.{uK, uG, max uV uK} K G ν :=
  Quotient.map (fun A => block ν A m) (fun _ _ ⟨e⟩ => ⟨blockEquiv ν e m⟩)

/-- Specified positive-length block data; no irreducibility or decomposition is assumed. -/
structure BlockDatum (K : Type uK) (G : Type uG) [Field K] [Group G] where
  representation : FiniteRepresentation.{uK, uG, uV} K G
  length : ℕ
  length_pos : 0 < length

namespace BlockDatum

/-- Construct the pair specified by a block datum. -/
def pair (d : BlockDatum.{uK, uG, uV} K G) (ν : G →* Kˣ) :
    WeilDeligneRepresentation.{uK, uG, max uV uK} K G ν :=
  block ν d.representation d.length

/-- Irreducibility is an additional predicate on the Weil factor, not a hidden assumption. -/
def IsIrreducible (d : BlockDatum K G) : Prop :=
  Representation.IsIrreducible d.representation.representation

/-- Positive-length block data whose Weil factor is irreducible. -/
def IrreducibleData (K : Type uK) (G : Type uG) [Field K] [Group G] :=
  {d : BlockDatum.{uK, uG, uV} K G // d.IsIrreducible}

end BlockDatum

end Langlands.WeilDeligneRepresentation
