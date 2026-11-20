import Langlands.BaseChange.CyclicAlgebraStructure

/-! # Reduction of the cyclic norm lemma to field extensions -/

namespace Langlands.BaseChange

universe u v

/-- The three clauses of the cyclic norm lemma for cyclic algebras that are fields. -/
def FieldCyclicNormLemmaStatement : Prop :=
  ∀ (F : Type u) [Field F] (L : Type v) [Field L] [Algebra F L] (τ : L ≃ₐ[F] L)
    (d n : ℕ), IsCyclicAlgebra τ d →
    (∀ δ : GeneralLinear n L, ∃ γ : GeneralLinear n F, IsNormAssociated τ d δ γ) ∧
    (∀ (δ : GeneralLinear n L) (γ γ' : GeneralLinear n F),
      IsNormAssociated τ d δ γ → IsNormAssociated τ d δ γ' →
        ∃ y : GeneralLinear n F, y⁻¹ * γ * y = γ') ∧
    (∀ δ δ' : GeneralLinear n L,
      (∃ g : GeneralLinear n L, g⁻¹ * cyclicNorm τ d δ * g = cyclicNorm τ d δ') →
        ∃ x : GeneralLinear n L, x⁻¹ * δ * entrywiseAut τ n x = δ')

/-- The field case suffices for the cyclic norm lemma for finite reduced algebras. -/
def CyclicNormLemmaFieldReductionStatement : Prop :=
  FieldCyclicNormLemmaStatement.{u,v} → CyclicNormLemmaStatement.{u,v}

noncomputable section

open Matrix CyclicAlgebraStructure

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {l n : ℕ}

private theorem cyclicNorm_add (a b : ℕ) (δ : GeneralLinear n E) :
    cyclicNorm σ (a + b) δ = cyclicNorm σ a δ * entrywiseAut (σ ^ a) n (cyclicNorm σ b δ) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ, cyclicNorm_succ, ih, cyclicNorm_succ, map_mul,
      ← entrywiseAut_mul_apply, ← pow_add, mul_assoc]

variable (c : Coordinates σ l)

private def residueAt (i : ℕ) : E →+* (E ⧸ c.m.asIdeal) :=
  (Ideal.Quotient.mk c.m.asIdeal).comp (σ ^ i).toRingHom

private def coord (n i : ℕ) : GeneralLinear n E →* GeneralLinear n (E ⧸ c.m.asIdeal) :=
  Matrix.GeneralLinearGroup.map (residueAt c i)

private theorem coord_ext {g g' : GeneralLinear n E}
    (h : ∀ i : Fin c.r, coord c n i.val g = coord c n i.val g') : g = g' := by
  ext a b
  apply c.coords.injective
  funext i
  rw [c.coords_apply, c.coords_apply]
  exact congrArg (fun x : GeneralLinear n (E ⧸ c.m.asIdeal) => x a b) (h i)

private theorem coord_surjective (g : Fin c.r → GeneralLinear n (E ⧸ c.m.asIdeal)) :
    ∃ x : GeneralLinear n E, ∀ i : Fin c.r, coord c n i.val x = g i := by
  let lift (A : Fin c.r → Matrix (Fin n) (Fin n) (E ⧸ c.m.asIdeal)) : Matrix (Fin n) (Fin n) E :=
    fun a b => c.coords.symm (fun i => A i a b)
  have hLift (A : Fin c.r → Matrix (Fin n) (Fin n) (E ⧸ c.m.asIdeal)) (i : Fin c.r) :
      (lift A).map (residueAt c i.val) = A i := by
    ext a b
    rw [Matrix.map_apply]
    change Ideal.Quotient.mk c.m.asIdeal ((σ ^ i.val) (c.coords.symm _)) = A i a b
    rw [← c.coords_apply, c.coords.apply_symm_apply]
  have hMatrix {A B : Matrix (Fin n) (Fin n) E}
      (h : ∀ i : Fin c.r, A.map (residueAt c i.val) = B.map (residueAt c i.val)) : A = B := by
    ext a b
    apply c.coords.injective
    funext i
    rw [c.coords_apply, c.coords_apply]
    exact congrFun (congrFun (h i) a) b
  let A := lift (fun i => (g i).val)
  let B := lift (fun i => ((g i)⁻¹).val)
  have hAB : A * B = 1 := hMatrix fun i => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hLift, hLift, Units.mul_inv]
  have hBA : B * A = 1 := hMatrix fun i => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hLift, hLift, Units.inv_mul]
  exact ⟨⟨A, B, hAB, hBA⟩, fun i => Units.ext (hLift _ i)⟩

private theorem coord_baseChange (i : ℕ) (γ : GeneralLinear n F) :
    coord c n i (baseChange F E n γ) = baseChange F (E ⧸ c.m.asIdeal) n γ := by
  ext a b
  change Ideal.Quotient.mk c.m.asIdeal ((σ ^ i) (algebraMap F E (γ a b))) = _
  rw [AlgEquiv.commutes]
  rfl

private theorem coord_add (a b : ℕ) (δ : GeneralLinear n E) :
    coord c n (a + b) δ = coord c n a (entrywiseAut (σ ^ b) n δ) := by
  ext i j
  change Ideal.Quotient.mk c.m.asIdeal ((σ ^ (a + b)) (δ i j)) =
    Ideal.Quotient.mk c.m.asIdeal ((σ ^ a) ((σ ^ b) (δ i j)))
  rw [pow_add, AlgEquiv.mul_apply]

private theorem coord_wrap (i : ℕ) (g : GeneralLinear n E) :
    coord c n (c.r + i) g = entrywiseAut c.τ n (coord c n i g) := by
  ext a b
  change Ideal.Quotient.mk c.m.asIdeal ((σ ^ (c.r + i)) (g a b)) =
    c.τ (Ideal.Quotient.mk c.m.asIdeal ((σ ^ i) (g a b)))
  rw [pow_add, AlgEquiv.mul_apply, c.wrap]

private theorem coord_mul (k : ℕ) (g : GeneralLinear n E) :
    coord c n (c.r * k) g = entrywiseAut (c.τ ^ k) n (coord c n 0 g) := by
  induction k with
  | zero => simp [entrywiseAut_one_apply]
  | succ k ih =>
    rw [Nat.mul_succ, add_comm, coord_wrap, ih, pow_succ', entrywiseAut_mul_apply]

private theorem coord_norm (δ : GeneralLinear n E) :
    coord c n 0 (cyclicNorm σ l δ) = cyclicNorm c.τ c.d (coord c n 0 (cyclicNorm σ c.r δ)) := by
  have blocks (k : ℕ) : coord c n 0 (cyclicNorm σ (c.r * k) δ) =
      cyclicNorm c.τ k (coord c n 0 (cyclicNorm σ c.r δ)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, cyclicNorm_add, map_mul, ih, ← coord_add, Nat.zero_add, coord_mul,
        cyclicNorm_succ]
  exact (congrArg (fun k => coord c n 0 (cyclicNorm σ k δ)) c.degree_eq).trans (blocks c.d)

private theorem coord_norm_conj (h : IsCyclicAlgebra σ l) (i : ℕ) (δ : GeneralLinear n E) :
    coord c n i (cyclicNorm σ l δ) = (coord c n 0 (cyclicNorm σ i δ))⁻¹ *
      coord c n 0 (cyclicNorm σ l δ) * coord c n 0 (cyclicNorm σ i δ) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [coord_add, pow_one, entrywiseAut_cyclicNorm, h.pow_eq_one, entrywiseAut_one_apply,
      map_mul, map_mul, map_inv, ih, cyclicNorm_succ, map_mul, ← coord_add, Nat.zero_add]
    group

/-- Coordinate evaluation transports the three norm assertions to the residue field; the
coordinate isomorphism lifts each required conjugator. -/
theorem cyclicNormLemma_of_field : CyclicNormLemmaFieldReductionStatement.{u,v} := by
  intro hfield F _ E _ _ σ l n h
  obtain ⟨c⟩ := exists_coordinates h
  let : c.m.asIdeal.IsMaximal := c.m.isMaximal
  let : Field (E ⧸ c.m.asIdeal) := Ideal.Quotient.field _
  obtain ⟨hex, hunique, htwist⟩ := hfield F (E ⧸ c.m.asIdeal) c.τ c.d n c.cyclic
  let P (δ : GeneralLinear n E) (i : ℕ) := coord c n 0 (cyclicNorm σ i δ)
  let y (δ : GeneralLinear n E) := P δ c.r
  have hP (δ : GeneralLinear n E) (i : ℕ) : P δ (i + 1) = P δ i * coord c n i δ := by
    dsimp only [P]
    rw [cyclicNorm_succ, map_mul, ← coord_add, Nat.zero_add]
  refine ⟨?_, ?_, ?_⟩
  · intro δ
    obtain ⟨γ, b, hb⟩ := hex (y δ)
    obtain ⟨g, hg⟩ := coord_surjective c (fun i => (P δ i.val)⁻¹ * b)
    refine ⟨γ, g, coord_ext c fun i => ?_⟩
    rw [map_mul, map_mul, map_inv, hg i, coord_baseChange, coord_norm_conj c h,
      coord_norm]
    change ((P δ i.val)⁻¹ * b)⁻¹ *
      ((P δ i.val)⁻¹ * cyclicNorm c.τ c.d (y δ) * P δ i.val) * ((P δ i.val)⁻¹ * b) = _
    rw [← hb]
    group
  · intro δ γ γ' hγ hγ'
    have pass {γ : GeneralLinear n F} (hγ : IsNormAssociated σ l δ γ) :
        IsNormAssociated c.τ c.d (y δ) γ := by
      obtain ⟨g, hg⟩ := hγ
      refine ⟨coord c n 0 g, ?_⟩
      apply_fun coord c n 0 at hg
      simpa only [map_mul, map_inv, coord_norm, coord_baseChange] using hg
    exact hunique (y δ) γ γ' (pass hγ) (pass hγ')
  · rintro δ δ' ⟨g, hg⟩
    have hg0 := congrArg (coord c n 0) hg
    simp only [map_mul, map_inv, coord_norm] at hg0
    obtain ⟨x0, hx0⟩ := htwist (y δ) (y δ') ⟨coord c n 0 g, hg0⟩
    obtain ⟨x, hx⟩ := coord_surjective c (fun i => (P δ i.val)⁻¹ * x0 * P δ' i.val)
    have hstart : coord c n 0 x = x0 := by
      have ht := hx (⟨0, c.r_pos⟩ : Fin c.r)
      simpa [P] using ht
    have hend : coord c n c.r x = (P δ c.r)⁻¹ * x0 * P δ' c.r := by
      have ht := coord_wrap c 0 x
      rw [Nat.add_zero, hstart] at ht
      rw [ht]
      change x0⁻¹ * P δ c.r * entrywiseAut c.τ n x0 = P δ' c.r at hx0
      rw [← hx0]
      group
    have hx' (i : ℕ) (hi : i ≤ c.r) : coord c n i x = (P δ i)⁻¹ * x0 * P δ' i := by
      rcases lt_or_eq_of_le hi with hi | rfl
      · exact hx ⟨i, hi⟩
      · exact hend
    refine ⟨x, coord_ext c fun i => ?_⟩
    have hshift : coord c n i.val (entrywiseAut σ n x) = coord c n (i.val + 1) x := by
      simpa only [pow_one] using (coord_add c i.val 1 x).symm
    rw [map_mul, map_mul, map_inv, hshift, hx i, hx' _ i.isLt, hP, hP]
    group

end

end Langlands.BaseChange
