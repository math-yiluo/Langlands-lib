import Langlands.Representation.Archimedean.RealStandardEllipticCartanComparisonReduction
import Langlands.Representation.Archimedean.RealCartanCompactSupport

/-! # Matrix realization of the elliptic Cartan coordinates -/

noncomputable section

open Matrix

set_option autoImplicit false

namespace Langlands.Archimedean.RealStandardEllipticCartan

open RealCartanCompactSupport

/-- Complex and real slots of the Cartan. -/
abbrev CartanSlot (r s : ℕ) := Fin r ⊕ Fin s

/-- A complex slot occupies two coordinates, and a real slot occupies one. -/
abbrev slotSize {r s : ℕ} : CartanSlot r s → ℕ := Sum.elim (fun _ => 2) (fun _ => 1)

/-- The coordinates within the consecutive one- and two-dimensional blocks. -/
abbrev CartanIndex (r s : ℕ) := Σ u : CartanSlot r s, Fin (slotSize u)

/-- Index the complex planes first, followed by the real lines. -/
def cartanIndexEquiv {n r s : ℕ} (h : 2 * r + s = n) : CartanIndex r s ≃ Fin n :=
  (Equiv.sumSigmaDistrib (fun u : CartanSlot r s => Fin (slotSize u))).trans
    ((Equiv.sumCongr (Equiv.sigmaEquivProd (Fin r) (Fin 2))
      (Equiv.sigmaEquivProd (Fin s) (Fin 1))).trans
      ((Equiv.sumCongr finProdFinEquiv (Equiv.prodUnique (Fin s) (Fin 1))).trans
        (finSumFinEquiv.trans (finCongr (by omega)))))

@[simp]
theorem cartanIndexEquiv_inl_val {n r s : ℕ} (h : 2 * r + s = n)
    (u : Fin r) (i : Fin 2) :
    (cartanIndexEquiv h ⟨.inl u, i⟩).val = i.val + 2 * u.val :=
  rfl

@[simp]
theorem cartanIndexEquiv_inr_val {n r s : ℕ} (h : 2 * r + s = n) (u : Fin s) (i : Fin 1) :
    (cartanIndexEquiv h ⟨.inr u, i⟩).val = 2 * r + u.val := by
  change r * 2 + u.val = 2 * r + u.val
  rw [Nat.mul_comm r 2]

/-- The block label of a matrix coordinate in the Cartan. -/
def cartanLabel {n r s : ℕ} (h : 2 * r + s = n) (i : Fin n) : Fin (r + s) :=
  finSumFinEquiv ((cartanIndexEquiv h).symm i).1

@[simp]
theorem cartanLabel_apply_indexEquiv {n r s : ℕ} (h : 2 * r + s = n) (u : CartanIndex r s) :
    cartanLabel h (cartanIndexEquiv h u) = finSumFinEquiv u.1 := by
  simp [cartanLabel]

/-- The number of coordinates in each Cartan block is one or two. -/
def cartanFiberEquiv {n r s : ℕ} (h : 2 * r + s = n) (u : CartanSlot r s) :
    Fin (slotSize u) ≃ BlockFiber (cartanLabel h) (finSumFinEquiv u) := by
  let f (i : Fin (slotSize u)) : BlockFiber (cartanLabel h) (finSumFinEquiv u) :=
    ⟨cartanIndexEquiv h ⟨u, i⟩, cartanLabel_apply_indexEquiv h _⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j hij
    exact eq_of_heq (Sigma.mk.inj_iff.mp
      ((cartanIndexEquiv h).injective (congrArg Subtype.val hij))).2
  · intro i
    obtain ⟨⟨v, j⟩, hj⟩ := (cartanIndexEquiv h).surjective i.val
    have hv : v = u := finSumFinEquiv.injective (by simpa [← hj] using i.property)
    subst v
    exact ⟨j, Subtype.ext hj⟩

@[simp]
theorem cartanFiber_card {n r s : ℕ} (h : 2 * r + s = n) (u : CartanSlot r s) :
    Nat.card (BlockFiber (cartanLabel h) (finSumFinEquiv u)) = slotSize u := by
  simpa using (Nat.card_congr (cartanFiberEquiv h u)).symm

theorem cartanLabel_surjective {n r s : ℕ} (h : 2 * r + s = n) :
    Function.Surjective (cartanLabel h) := by
  intro i
  obtain ⟨u, rfl⟩ := (finSumFinEquiv : CartanSlot r s ≃ Fin (r + s)).surjective i
  have hu : 0 < slotSize u := by cases u <;> simp [slotSize]
  exact ⟨cartanIndexEquiv h ⟨u, ⟨0, hu⟩⟩, by simp⟩

theorem cartanPairBlock_card {n r s : ℕ} (h : 2 * r + s = n) :
    Nat.card (PairBlock (cartanLabel h)) = r := by
  let f (i : Fin r) : PairBlock (cartanLabel h) :=
    ⟨finSumFinEquiv (.inl i), cartanFiber_card h (.inl i)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j he => Sum.inl.inj (finSumFinEquiv.injective (congrArg Subtype.val he)), ?_⟩
    intro p
    obtain ⟨u, hu⟩ := (finSumFinEquiv : CartanSlot r s ≃ Fin (r + s)).surjective p.val
    have htwo := p.property
    rw [← hu, cartanFiber_card] at htwo
    cases u with
    | inl i => exact ⟨i, Subtype.ext hu⟩
    | inr j => simp [slotSize] at htwo
  simpa using (Nat.card_congr (Equiv.ofBijective f hf)).symm

private def assemble {n r s : ℕ} (h : 2 * r + s = n) :
    (∀ u : CartanSlot r s, Matrix (Fin (slotSize u)) (Fin (slotSize u)) ℝ) →+*
      Matrix (Fin n) (Fin n) ℝ :=
  (reindexRingEquiv ℝ (cartanIndexEquiv h)).toRingHom.comp (blockDiagonal'RingHom _ ℝ)

private theorem assemble_transpose {n r s : ℕ} (h : 2 * r + s = n)
    (F : ∀ u : CartanSlot r s, Matrix (Fin (slotSize u)) (Fin (slotSize u)) ℝ) :
    (assemble h F)ᵀ = assemble h (fun u => (F u)ᵀ) := by
  let e := cartanIndexEquiv h
  change (reindex e e (blockDiagonal' F))ᵀ = reindex e e (blockDiagonal' fun u => (F u)ᵀ)
  rw [transpose_reindex, blockDiagonal'_transpose]

private theorem assemble_diagonal {n r s : ℕ} (h : 2 * r + s = n)
    (f : CartanSlot r s → ℝ) :
    assemble h (fun u => diagonal (fun _ => f u)) =
      diagonal (fun i => f ((cartanIndexEquiv h).symm i).1) := by
  let e := cartanIndexEquiv h
  change reindex e e (blockDiagonal' fun u => diagonal (fun _ : Fin (slotSize u) => f u)) = _
  rw [blockDiagonal'_diagonal]
  ext i j
  change diagonal (fun u : CartanIndex r s => f u.1) (e.symm i) (e.symm j) =
    diagonal (fun k => f (e.symm k).1) i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [diagonal_apply_ne _ (e.symm.injective.ne hij), diagonal_apply_ne _ hij]

private def rotationBlock (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

private theorem rotationBlock_orthogonal (θ : ℝ) :
    rotationBlock θ * (rotationBlock θ)ᵀ = 1 ∧ (rotationBlock θ)ᵀ * rotationBlock θ = 1 := by
  have h := Real.sin_sq_add_cos_sq θ
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotationBlock, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

/-- The angular and sign parts of the Cartan blocks. -/
def orthogonalBlock {r s : ℕ} (x : Coordinates r s) (u : CartanSlot r s) :
    Matrix (Fin (slotSize u)) (Fin (slotSize u)) ℝ :=
  match u with
  | .inl i => rotationBlock (x.1 i).toAdd.2
  | .inr j => ((-1 : ℝ) ^ (x.2 j).toAdd.2) • 1

theorem orthogonalBlock_inl {r s : ℕ} (x : Coordinates r s) (u : Fin r) :
    orthogonalBlock x (.inl u) =
      !![Real.cos (x.1 u).toAdd.2, -Real.sin (x.1 u).toAdd.2;
        Real.sin (x.1 u).toAdd.2, Real.cos (x.1 u).toAdd.2] :=
  rfl

theorem orthogonalBlock_inr {r s : ℕ} (x : Coordinates r s) (u : Fin s) :
    orthogonalBlock x (.inr u) = ((-1 : ℝ) ^ (x.2 u).toAdd.2) • 1 :=
  rfl

private theorem orthogonalBlock_orthogonal {r s : ℕ} (x : Coordinates r s) (u : CartanSlot r s) :
    orthogonalBlock x u * (orthogonalBlock x u)ᵀ = 1 ∧
      (orthogonalBlock x u)ᵀ * orthogonalBlock x u = 1 := by
  cases u with
  | inl i => exact rotationBlock_orthogonal _
  | inr j =>
    let z : ℤ := (x.2 j).toAdd.2
    have hs : (-1 : ℝ) ^ z * (-1 : ℝ) ^ z = 1 := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
      exact (show Even (z + z) from ⟨z, rfl⟩).neg_one_zpow
    let S : Matrix (Fin 1) (Fin 1) ℝ := ((-1 : ℝ) ^ z) • 1
    have hS : Sᵀ = S := by simp only [S, transpose_smul, transpose_one]
    have hmul : S * S = 1 := by
      simp only [S, Matrix.mul_smul, mul_one, smul_smul, hs, one_smul]
    change S * Sᵀ = 1 ∧ Sᵀ * S = 1
    rw [hS]
    exact ⟨hmul, hmul⟩

/-- The positive part of the Cartan matrix, with the same radius at both coordinates
of a complex plane. -/
def cartanDiagonal {n r s : ℕ} (h : 2 * r + s = n) (x : Coordinates r s) :
    Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i => Real.exp (coordinateRadius x ((cartanIndexEquiv h).symm i).1))

@[simp]
theorem cartanDiagonal_apply_indexEquiv {n r s : ℕ} (h : 2 * r + s = n)
    (x : Coordinates r s) (u : CartanIndex r s) :
    cartanDiagonal h x (cartanIndexEquiv h u) (cartanIndexEquiv h u) =
      Real.exp (coordinateRadius x u.1) := by
  simp [cartanDiagonal]

/-- The orthogonal part of the Cartan matrix, with rotation and sign blocks. -/
def cartanOrthogonal {n r s : ℕ} (h : 2 * r + s = n) (x : Coordinates r s) :
    Matrix (Fin n) (Fin n) ℝ :=
  assemble h (orthogonalBlock x)

theorem cartanOrthogonal_orthogonal {n r s : ℕ} (h : 2 * r + s = n) (x : Coordinates r s) :
    cartanOrthogonal h x * (cartanOrthogonal h x)ᵀ = 1 ∧
      (cartanOrthogonal h x)ᵀ * cartanOrthogonal h x = 1 := by
  simp only [cartanOrthogonal, assemble_transpose, ← map_mul]
  have hm : orthogonalBlock x * (fun u => (orthogonalBlock x u)ᵀ) = 1 :=
    funext fun u => (orthogonalBlock_orthogonal x u).1
  have ht : (fun u => (orthogonalBlock x u)ᵀ) * orthogonalBlock x = 1 :=
    funext fun u => (orthogonalBlock_orthogonal x u).2
  rw [hm, ht, map_one]
  exact ⟨rfl, rfl⟩

private def cartanDiagonalUnits {n r s : ℕ} (h : 2 * r + s = n) (x : Coordinates r s) :
    Langlands.GeneralLinear n ℝ where
  val := cartanDiagonal h x
  inv := diagonal (fun i => (Real.exp (coordinateRadius x ((cartanIndexEquiv h).symm i).1))⁻¹)
  val_inv := by simp [cartanDiagonal, diagonal_mul_diagonal, Real.exp_ne_zero]
  inv_val := by simp [cartanDiagonal, diagonal_mul_diagonal, Real.exp_ne_zero]

/-- The element of `GL_n(ℝ)` with the indicated complex and real Cartan coordinates. -/
def cartanElement {n r s : ℕ} (h : 2 * r + s = n) (x : Coordinates r s) :
    Langlands.GeneralLinear n ℝ :=
  cartanDiagonalUnits h x *
    ⟨cartanOrthogonal h x, (cartanOrthogonal h x)ᵀ,
      (cartanOrthogonal_orthogonal h x).1, (cartanOrthogonal_orthogonal h x).2⟩

theorem cartanElement_val {n r s : ℕ} (h : 2 * r + s = n) (x : Coordinates r s) :
    (cartanElement h x : Matrix (Fin n) (Fin n) ℝ) = cartanDiagonal h x * cartanOrthogonal h x := rfl

private def scaledBlock {r s : ℕ} (x : Coordinates r s) (u : CartanSlot r s) :
    Matrix (Fin (slotSize u)) (Fin (slotSize u)) ℝ :=
  Real.exp (coordinateRadius x u) • orthogonalBlock x u

private theorem cartanElement_val_assemble {n r s : ℕ} (h : 2 * r + s = n)
    (x : Coordinates r s) :
    (cartanElement h x : Matrix (Fin n) (Fin n) ℝ) = assemble h (scaledBlock x) := by
  rw [cartanElement_val, cartanOrthogonal, cartanDiagonal,
    ← assemble_diagonal h (fun u => Real.exp (coordinateRadius x u)), ← map_mul]
  congr 1
  funext u
  simp [scaledBlock, ← smul_one_eq_diagonal]

/-- Inside its block, the Cartan matrix is the radius times its angular or sign factor. -/
@[simp]
theorem cartanElement_apply_block {n r s : ℕ} (h : 2 * r + s = n) (x : Coordinates r s)
    (u : CartanSlot r s) (i j : Fin (slotSize u)) :
    (cartanElement h x : Matrix (Fin n) (Fin n) ℝ)
        (cartanIndexEquiv h ⟨u, i⟩) (cartanIndexEquiv h ⟨u, j⟩) =
      Real.exp (coordinateRadius x u) * orthogonalBlock x u i j := by
  rw [cartanElement_val_assemble]
  change blockDiagonal' (scaledBlock x) ((cartanIndexEquiv h).symm _) _ = _
  simp [scaledBlock]

/-- Matrix entries between two different Cartan blocks are zero. -/
theorem cartanElement_apply_of_label_ne {n r s : ℕ} (h : 2 * r + s = n) (x : Coordinates r s)
    {i j : Fin n} (hij : cartanLabel h i ≠ cartanLabel h j) :
    (cartanElement h x : Matrix (Fin n) (Fin n) ℝ) i j = 0 := by
  rw [cartanElement_val_assemble]
  have hne : ((cartanIndexEquiv h).symm i).1 ≠ ((cartanIndexEquiv h).symm j).1 :=
    fun he => hij (congrArg finSumFinEquiv he)
  change blockDiagonal' (scaledBlock x) _ _ = _
  exact blockDiagonal'_apply_ne _ _ _ hne

/-- The squared radius assigned to each Cartan block. -/
def cartanSquaredRadius {r s : ℕ} (x : Coordinates r s) (v : Fin (r + s)) : ℝ :=
  Real.exp (2 * coordinateRadius x (finSumFinEquiv.symm v))

theorem cartanSquaredRadius_injective {r s : ℕ} {x : Coordinates r s}
    (hx : x ∈ separatedRegularCoordinates r s) : Function.Injective (cartanSquaredRadius x) := by
  intro i j hij
  apply finSumFinEquiv.symm.injective
  apply hx.1
  have he := Real.exp_injective hij
  linarith

/-- Both Gram products of the Cartan matrix are diagonal, given by the squared radii. -/
theorem cartanElement_gram {n r s : ℕ} (h : 2 * r + s = n) (x : Coordinates r s) :
    let C := (cartanElement h x : Matrix (Fin n) (Fin n) ℝ)
    C * Cᵀ = diagonal (cartanSquaredRadius x ∘ cartanLabel h) ∧
      Cᵀ * C = diagonal (cartanSquaredRadius x ∘ cartanLabel h) := by
  dsimp only
  rw [cartanElement_val_assemble, assemble_transpose, ← map_mul, ← map_mul]
  let d (u : CartanSlot r s) := Real.exp (2 * coordinateRadius x u)
  have hd : (cartanSquaredRadius x ∘ cartanLabel h) =
      fun i => d ((cartanIndexEquiv h).symm i).1 := by
    funext i
    simp [cartanSquaredRadius, cartanLabel, d]
  have hb (u : CartanSlot r s) :
      scaledBlock x u * (scaledBlock x u)ᵀ = diagonal (fun _ => d u) ∧
        (scaledBlock x u)ᵀ * scaledBlock x u = diagonal (fun _ => d u) := by
    obtain ⟨h₁, h₂⟩ := orthogonalBlock_orthogonal x u
    constructor <;>
      simp only [scaledBlock, transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
        h₁, h₂, smul_smul, ← Real.exp_add, ← two_mul] <;>
      exact smul_one_eq_diagonal _
  rw [hd, ← assemble_diagonal h d]
  exact ⟨congrArg (assemble h) (funext fun u => (hb u).1),
    congrArg (assemble h) (funext fun u => (hb u).2)⟩

private theorem cartanBlock_cases {n r s : ℕ} {h : 2 * r + s = n} {i j : Fin n}
    (hne : i ≠ j) (he : cartanLabel h i = cartanLabel h j) :
    ∃ (u : Fin r) (p q : Fin 2), p ≠ q ∧
      i = cartanIndexEquiv h ⟨Sum.inl u, p⟩ ∧ j = cartanIndexEquiv h ⟨Sum.inl u, q⟩ := by
  obtain ⟨⟨u, p⟩, rfl⟩ := (cartanIndexEquiv h).surjective i
  obtain ⟨⟨v, q⟩, rfl⟩ := (cartanIndexEquiv h).surjective j
  have hv : u = v := finSumFinEquiv.injective (by simpa using he)
  subst v
  have hpq : p ≠ q := fun hpq => hne (by rw [hpq])
  cases u with
  | inl u => exact ⟨u, p, q, hpq, rfl, rfl⟩
  | inr u => exact (hpq (Subsingleton.elim (α := Fin 1) p q)).elim

theorem cartanLabel_eq_or_eq {n r s : ℕ} {h : 2 * r + s = n} {i j k : Fin n}
    (hne : i ≠ j) (hij : cartanLabel h i = cartanLabel h j)
    (hik : cartanLabel h k = cartanLabel h i) : k = i ∨ k = j := by
  obtain ⟨u, p, q, hpq, rfl, rfl⟩ := cartanBlock_cases hne hij
  obtain ⟨⟨v, z⟩, rfl⟩ := (cartanIndexEquiv h).surjective k
  have hv : v = Sum.inl u := finSumFinEquiv.injective (by simpa using hik)
  subst v
  change Fin 2 at z
  have hz : z = p ∨ z = q := by omega
  exact hz.imp (fun hz => by rw [hz]) (fun hz => by rw [hz])

/-- On a complex plane the off-diagonal entries are skew and nonzero at regular angles. -/
theorem cartanElement_skew_and_ne {n r s : ℕ} {h : 2 * r + s = n} {x : Coordinates r s}
    (hx : x ∈ separatedRegularCoordinates r s) {i j : Fin n}
    (hne : i ≠ j) (hij : cartanLabel h i = cartanLabel h j) :
    let C := (cartanElement h x : Matrix (Fin n) (Fin n) ℝ)
    C i j = - C j i ∧ C i j ≠ 0 := by
  obtain ⟨u, p, q, hpq, rfl, rfl⟩ := cartanBlock_cases hne hij
  have hsin := hx.2 u
  dsimp only
  rw [cartanElement_apply_block h x (.inl u) p q, cartanElement_apply_block h x (.inl u) q p]
  let a := Real.exp (coordinateRadius x (.inl u))
  let θ := (x.1 u).toAdd.2
  change a * rotationBlock θ p q = -(a * rotationBlock θ q p) ∧ a * rotationBlock θ p q ≠ 0
  fin_cases p <;> fin_cases q <;>
    first | contradiction | simp [rotationBlock, mul_neg, a, θ, Real.exp_ne_zero, hsin]

/-- The regular Cartan elements have the source labels, Gram matrix and entry conditions
for compact-column support. -/
def RealStandardEllipticCartanMatrixStatement : Prop :=
  ∀ {n r s : ℕ} (h : 2 * r + s = n) (x : Coordinates r s),
    x ∈ separatedRegularCoordinates r s →
    let a := cartanLabel h
    let d := cartanSquaredRadius x
    let C := (cartanElement h x : Matrix (Fin n) (Fin n) ℝ)
    Function.Surjective a ∧ Nat.card (PairBlock a) = r ∧
    (∀ ⦃i j k⦄, i ≠ j → a i = a j → a k = a i → k = i ∨ k = j) ∧
    (∀ ⦃i j⦄, a i ≠ a j → C i j = 0) ∧
    (∀ ⦃i j⦄, i ≠ j → a i = a j → C i j = - C j i) ∧
    (∀ ⦃i j⦄, i ≠ j → a i = a j → C i j ≠ 0) ∧
    C * Cᵀ = diagonal (d ∘ a) ∧ Function.Injective d ∧ C * Cᵀ = Cᵀ * C

theorem realStandardEllipticCartanMatrix : RealStandardEllipticCartanMatrixStatement := by
  intro n r s h x hx
  obtain ⟨hg, ht⟩ := cartanElement_gram h x
  refine ⟨cartanLabel_surjective h, cartanPairBlock_card h, ?_, ?_, ?_, ?_, hg,
    cartanSquaredRadius_injective hx, hg.trans ht.symm⟩
  · intro i j k hij ha hk
    exact cartanLabel_eq_or_eq hij ha hk
  · intro i j hij
    exact cartanElement_apply_of_label_ne h x hij
  · intro i j hij ha
    exact (cartanElement_skew_and_ne hx hij ha).1
  · intro i j hij ha
    exact (cartanElement_skew_and_ne hx hij ha).2

end Langlands.Archimedean.RealStandardEllipticCartan
