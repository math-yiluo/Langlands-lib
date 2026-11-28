import Langlands.Algebra.CentralSimple.LandherrAssembly
import Langlands.Algebra.CentralSimple.LandherrFinish
import Langlands.Algebra.CentralSimple.LandherrGoodPlaces
import Langlands.Algebra.CentralSimple.LandherrNormGlobal
import Langlands.Algebra.CentralSimple.LandherrSplitPlace
import Langlands.Algebra.CentralSimple.LandherrRealSplitting
import Langlands.Algebra.CentralSimple.LandherrNumberFieldNorm

/-! # Landherr's theorem for units of relative reduced norm one -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root Langlands.BinaryElementary
open NumberField IsDedekindDomain Filter _root_.Topology _root_.Polynomial
open scoped TensorProduct

universe u

/-- The matrix `diag(b, 1)`. -/
abbrev diagOne {B : Type u} [Ring B] (b : B) : Matrix (Fin 2) (Fin 2) B :=
  Matrix.of ![![b, 0], ![0, 1]]

section Coordinates

variable (F : Type u) [Field F] (B : Type u) [Ring B] [Algebra F B] [FiniteDimensional F B]
  (k : Type u) [Field k] [Algebra F k] {ι : Type*} [Fintype ι] (β : Module.Basis ι F B)

omit [FiniteDimensional F B] in
/-- Scalar extension of `diag(b, 1)`. -/
theorem matrixBaseMap_diagOne (b : B) :
    matrixBaseMap F B k (diagOne b) = diagOne ((1 : k) ⊗ₜ[F] b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Algebra.TensorProduct.one_def]

omit [FiniteDimensional F B] in
/-- Coordinates in `F` give entries over `k` which are the images of entries over `F`. -/
theorem coordPoint_algebraMap {L : ℕ} (x : Fin L × Fin 2 × ι → F) :
    coordPoint F B β (fun α => algebraMap F k (x α)) =
      fun j => ((1 : k) ⊗ₜ[F] ∑ i, x (j, 0, i) • β i, (1 : k) ⊗ₜ[F] ∑ i, x (j, 1, i) • β i) := by
  funext j
  simp only [coordPoint, TensorProduct.tmul_sum, TensorProduct.tmul_smul, algebraMap_smul]

end Coordinates

section Local

variable (F E : Type u) [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CharZero F]
  (B : Type u) [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
  (τ : FirstKindInvolution F B)
  (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e))

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CharZero F] in
/-- Relative reduced norm one is preserved by scalar extension. -/
theorem relNorm_one_tmul_eq_one (k : Type u) [Field k] [Algebra F k] (y : B)
    (hy : relNorm F E B F ((1 : F) ⊗ₜ[F] y) = 1) : relNorm F E B k ((1 : k) ⊗ₜ[F] y) = 1 := by
  have h := relNorm_naturality F E B (Algebra.ofId F k) ((1 : F) ⊗ₜ[F] y)
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, hy, map_one] at h
  exact h

include hτ in
/-- **Local coordinate neighbourhoods.** Let `τ` act on `E` by quadratic conjugation.
Let `k` be a complete nontrivially normed field over `F` with `UnitaryInvolutionSplitting k`
in which `skewSq F E` has nonsquare image. Let `y` be a unit of relative reduced norm one
with `1 ⊗ y = x τ_k(x)` for a unit `x` of `k ⊗[F] B`.
For every sufficiently large length there are coordinate neighbourhoods over `k` on which
`t diag(1 ⊗ y, 1) τ_k(t)ᵗ` is a square in the `k`-algebra it generates. -/
theorem exists_local_nbhd [FiniteDimensional F B] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : Module.Basis ι F B) (k : Type u) [NontriviallyNormedField k] [CompleteSpace k]
    [Algebra F k] (hd : ¬ IsSquare (algebraMap F k (skewSq F E)))
    (hS : UnitaryInvolutionSplitting k) (y : Bˣ) (x : (k ⊗[F] B)ˣ)
    (hx : (1 : k) ⊗ₜ[F] (y : B) = x * τ.baseChange k x)
    (hy : relNorm F E B F ((1 : F) ⊗ₜ[F] (y : B)) = 1) :
    ∃ N : ℕ, ∀ L, N ≤ L → ∃ c₀ : Fin L × Fin 2 × ι → k, ∃ t : Fin L × Fin 2 × ι → Set k,
      (∀ α, t α ∈ 𝓝 (c₀ α)) ∧ ∀ c : Fin L × Fin 2 × ι → k, (∀ α, c α ∈ t α) →
        ∃ σ ∈ Algebra.adjoin k {targetMap F B τ (matrixBaseMap F B k (diagOne y.val)) (coordPoint F B β c)},
          σ * σ = targetMap F B τ (matrixBaseMap F B k (diagOne y.val)) (coordPoint F B β c) := by
  have : Fact (¬ IsSquare (algebraMap F k (skewSq F E))) := ⟨hd⟩
  have : CharZero k := charZero_of_injective_algebraMap (algebraMap F k).injective
  obtain ⟨l, hl⟩ := exists_target_list F E B τ hτ k hS y x hx
    (relNorm_one_tmul_eq_one F E B k (y : B) hy)
  refine ⟨l.length, fun L hL => ?_⟩
  rw [matrixBaseMap_diagOne]
  exact exists_target_nbhd F B τ β two_ne_zero _ l hl L hL

end Local

section Global

variable (F E : Type u) [Field F] [NumberField F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
  (B : Type u) [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
  (τ : FirstKindInvolution F B)
  (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e))

/-- The matrix `t D τ(t)ᵗ` in `M₂(B)` for the elementary product `t` with entries `g`. -/
abbrev globalTarget (D : Matrix (Fin 2) (Fin 2) B) {L : ℕ} (g : Fin L → B × B) :
    Matrix (Fin 2) (Fin 2) B :=
  (listProd (List.ofFn g) : Matrix (Fin 2) (Fin 2) B) * D *
    τ.matrix (Fin 2) (listProd (List.ofFn g) : Matrix (Fin 2) (Fin 2) B)

include hτ in
/-- **Choice of the elementary product.** Let `τ` act on `E` by quadratic conjugation
and let `y` be a unit of relative reduced norm one. Suppose that at every finite and
infinite place `v` there is a unit `x_v` of `F_v ⊗[F] B` with `1 ⊗ y = x_v τ_v(x_v)`.
For any basis `β` of `B` over `F` and finite set `S` of finite places, there is a finite
place `v₀ ∉ S` at which `d = skewSq F E` is a square, and there are elementary matrix
entries `g` in `B` whose coordinates in `β` are integral outside `S ∪ {v₀}`.
At each place of `S` and each infinite place, either `d` is a square in the completion or
the scalar extension of `t diag(y, 1) τ(t)ᵗ` is a square in the local algebra it generates,
where `t` is the elementary product determined by `g`. -/
theorem exists_entries [FiniteDimensional F B] (y : Bˣ)
    (hlocf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : (v.adicCompletion F ⊗[F] B)ˣ,
      (1 : v.adicCompletion F) ⊗ₜ[F] (y : B) = x * τ.baseChange (v.adicCompletion F) x)
    (hloci : ∀ w : InfinitePlace F, ∃ x : (w.Completion ⊗[F] B)ˣ,
      (1 : w.Completion) ⊗ₜ[F] (y : B) = x * τ.baseChange w.Completion x)
    (hN : relNorm F E B F ((1 : F) ⊗ₜ[F] (y : B)) = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι F B)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ v₀ : HeightOneSpectrum (𝓞 F), v₀ ∉ S ∧
      IsSquare (algebraMap F (v₀.adicCompletion F) (skewSq F E)) ∧
      ∃ (L : ℕ) (g : Fin L → B × B),
        (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v ≠ v₀ → ∀ j,
          IntAt β v (g j).1 ∧ IntAt β v (g j).2) ∧
        (∀ v ∈ S, IsSquare (algebraMap F (v.adicCompletion F) (skewSq F E)) ∨
          ∃ σ ∈ Algebra.adjoin (v.adicCompletion F)
            {matrixBaseMap F B (v.adicCompletion F) (globalTarget F B τ (diagOne y.val) g)},
            σ * σ = matrixBaseMap F B _ (globalTarget F B τ (diagOne y.val) g)) ∧
        (∀ w : InfinitePlace F, IsSquare (algebraMap F w.Completion (skewSq F E)) ∨
          ∃ σ ∈ Algebra.adjoin w.Completion
            {matrixBaseMap F B w.Completion (globalTarget F B τ (diagOne y.val) g)},
            σ * σ = matrixBaseMap F B _ (globalTarget F B τ (diagOne y.val) g)) := by
  classical
  choose xf hxf using hlocf
  choose xi hxi using hloci
  obtain ⟨v₀, hv₀S, hv₀⟩ := exists_split_finitePlace F E S
  have hnf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ N : ℕ, ∀ L, N ≤ L →
      ∃ c₀ : Fin L × Fin 2 × ι → v.adicCompletion F,
      ∃ t : Fin L × Fin 2 × ι → Set (v.adicCompletion F), (∀ α, t α ∈ 𝓝 (c₀ α)) ∧
        (¬ IsSquare (algebraMap F (v.adicCompletion F) (skewSq F E)) →
          ∀ c : Fin L × Fin 2 × ι → v.adicCompletion F, (∀ α, c α ∈ t α) →
            ∃ σ ∈ Algebra.adjoin (v.adicCompletion F)
              {targetMap F B τ (matrixBaseMap F B _ (diagOne y.val)) (coordPoint F B β c)},
              σ * σ = targetMap F B τ (matrixBaseMap F B _ (diagOne y.val))
                (coordPoint F B β c)) := by
    intro v
    by_cases hsq : IsSquare (algebraMap F (v.adicCompletion F) (skewSq F E))
    · exact ⟨0, fun L _ => ⟨0, fun _ => Set.univ, fun _ => Filter.univ_mem,
        fun h => absurd hsq h⟩⟩
    · let _ : NontriviallyNormedField (v.adicCompletion F) :=
        Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
      obtain ⟨N, hN'⟩ := exists_local_nbhd F E B τ hτ β (v.adicCompletion F) hsq
        (finiteCompletion_unitaryInvolutionSplitting v) y (xf v) (hxf v) hN
      refine ⟨N, fun L hL => ?_⟩
      obtain ⟨c₀, t, ht, h⟩ := hN' L hL
      exact ⟨c₀, t, ht, fun _ => h⟩
  have hni : ∀ w : InfinitePlace F, ∃ N : ℕ, ∀ L, N ≤ L →
      ∃ c₀ : Fin L × Fin 2 × ι → w.Completion,
      ∃ t : Fin L × Fin 2 × ι → Set w.Completion, (∀ α, t α ∈ 𝓝 (c₀ α)) ∧
        (¬ IsSquare (algebraMap F w.Completion (skewSq F E)) →
          ∀ c : Fin L × Fin 2 × ι → w.Completion, (∀ α, c α ∈ t α) →
            ∃ σ ∈ Algebra.adjoin w.Completion
              {targetMap F B τ (matrixBaseMap F B _ (diagOne y.val)) (coordPoint F B β c)},
              σ * σ = targetMap F B τ (matrixBaseMap F B _ (diagOne y.val))
                (coordPoint F B β c)) := by
    intro w
    by_cases hsq : IsSquare (algebraMap F w.Completion (skewSq F E))
    · exact ⟨0, fun L _ => ⟨0, fun _ => Set.univ, fun _ => Filter.univ_mem,
        fun h => absurd hsq h⟩⟩
    · let _ : NontriviallyNormedField w.Completion :=
        { (inferInstance : NormedField w.Completion) with
          non_trivial := by
            refine ⟨2, ?_⟩
            have h2 := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
              (map_zero (InfinitePlace.Completion.extensionEmbedding w)) (2 : w.Completion)
            rw [← h2]
            norm_num only [map_ofNat, Complex.norm_ofNat] }
      obtain ⟨N, hN'⟩ := exists_local_nbhd F E B τ hτ β w.Completion hsq
        (infiniteCompletion_unitaryInvolutionSplitting w) y (xi w) (hxi w) hN
      refine ⟨N, fun L hL => ?_⟩
      obtain ⟨c₀, t, ht, h⟩ := hN' L hL
      exact ⟨c₀, t, ht, fun _ => h⟩
  choose Nf hNf using hnf
  choose Ni hNi using hni
  set L := ∑ v ∈ S, Nf v + ∑ w, Ni w with hL
  have hLf : ∀ v ∈ S, Nf v ≤ L := fun v hv =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv).trans (Nat.le_add_right _ _)
  have hLi : ∀ w, Ni w ≤ L := fun w =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)).trans
      (Nat.le_add_left _ _)
  have hcf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c₀ : Fin L × Fin 2 × ι → v.adicCompletion F,
      ∃ t : Fin L × Fin 2 × ι → Set (v.adicCompletion F), (∀ α, t α ∈ 𝓝 (c₀ α)) ∧
        (v ∈ S → ¬ IsSquare (algebraMap F (v.adicCompletion F) (skewSq F E)) →
          ∀ c : Fin L × Fin 2 × ι → v.adicCompletion F, (∀ α, c α ∈ t α) →
            ∃ σ ∈ Algebra.adjoin (v.adicCompletion F)
              {targetMap F B τ (matrixBaseMap F B _ (diagOne y.val)) (coordPoint F B β c)},
              σ * σ = targetMap F B τ (matrixBaseMap F B _ (diagOne y.val))
                (coordPoint F B β c)) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨c₀, t, ht, h⟩ := hNf v L (hLf v hv)
      exact ⟨c₀, t, ht, fun _ => h⟩
    · exact ⟨0, fun _ => Set.univ, fun _ => Filter.univ_mem, fun h => absurd h hv⟩
  choose cf Tf hTf hTfsq using hcf
  choose ci Ti hTi hTisq using fun w => hNi w L (hLi w)
  obtain ⟨x, hxS, hxI, hxv⟩ := exists_approx_coords S v₀ hv₀S cf Tf (fun v _ => hTf v) ci Ti hTi
  refine ⟨v₀, hv₀S, hv₀, L, fun j => (∑ i, x (j, 0, i) • β i, ∑ i, x (j, 1, i) • β i),
    ?_, ?_, ?_⟩
  · intro v hv hv' j
    exact ⟨intAt_sum fun i _ => intAt_smul (hxv v hv hv' _) (intAt_basis i),
      intAt_sum fun i _ => intAt_smul (hxv v hv hv' _) (intAt_basis i)⟩
  · intro v hv
    by_cases hsq : IsSquare (algebraMap F (v.adicCompletion F) (skewSq F E))
    · exact Or.inl hsq
    · right
      have h := hTfsq v hv hsq (fun α => algebraMap F _ (x α)) (hxS v hv)
      rw [coordPoint_algebraMap] at h
      rw [globalTarget, matrixBaseMap_targetMap]
      exact h
  · intro w
    by_cases hsq : IsSquare (algebraMap F w.Completion (skewSq F E))
    · exact Or.inl hsq
    · right
      have h := hTisq w hsq (fun α => algebraMap F _ (x α)) (hxI w)
      rw [coordPoint_algebraMap] at h
      rw [globalTarget, matrixBaseMap_targetMap]
      exact h

include hτ in
/-- **Landherr's theorem in relative reduced norm one.** Let `τ` act on `E` by quadratic
conjugation and let `y` be a `τ`-symmetric unit of relative reduced norm one. If at every
finite and infinite place `v` there is a unit `x_v` of `F_v ⊗[F] B` with
`1 ⊗ y = x_v τ_v(x_v)`, then `y = x τ(x)` for a unit `x` of `B`. -/
theorem exists_eq_mul_of_relNorm_eq_one (y : Bˣ) (hy : τ (y : B) = y)
    (hlocf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : (v.adicCompletion F ⊗[F] B)ˣ,
      (1 : v.adicCompletion F) ⊗ₜ[F] (y : B) = x * τ.baseChange (v.adicCompletion F) x)
    (hloci : ∀ w : InfinitePlace F, ∃ x : (w.Completion ⊗[F] B)ˣ,
      (1 : w.Completion) ⊗ₜ[F] (y : B) = x * τ.baseChange w.Completion x)
    (hN : relNorm F E B F ((1 : F) ⊗ₜ[F] (y : B)) = 1) :
    ∃ x : Bˣ, (y : B) = x * τ x := by
  classical
  have : FiniteDimensional F E :=
    .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]; decide)
  have : FiniteDimensional F B := Module.Finite.trans E B
  have hd : skewSq F E ≠ 0 := by
    intro h0
    have := algebraMap_skewSq F E
    rw [h0, map_zero] at this
    exact skewRoot_ne_zero F E (mul_self_eq_zero.mp this.symm)
  let βB := Module.finBasis F B
  let β₂ := Module.finBasis F (Matrix (Fin 2) (Fin 2) B)
  have hfinand : ∀ {P Q : HeightOneSpectrum (𝓞 F) → Prop}, {v | ¬ P v}.Finite →
      {v | ¬ Q v}.Finite → {v | ¬ (P v ∧ Q v)}.Finite := fun hP hQ =>
    (hP.union hQ).subset fun v hv => by
      simp only [Set.mem_ofPred_eq, Set.mem_union, not_and_or] at hv ⊢
      exact hv
  have hGood : {v : HeightOneSpectrum (𝓞 F) | ¬ (BasisIntAt β₂ v ∧
      (∀ i, IntAt β₂ v (upperPart F (βB i))) ∧ (∀ i, IntAt β₂ v (lowerPart F (βB i))) ∧
      IntAt β₂ v (diagOne y.val) ∧ IntAt β₂ v (diagOne (y⁻¹).val) ∧
      (∀ i, IntAt β₂ v (τ.matrix (Fin 2) (β₂ i))) ∧ v.valuation F 2 = 1 ∧
      v.valuation F (skewSq F E) = 1)}.Finite :=
    hfinand (finite_setOf_not_basisIntAt β₂) <|
      hfinand (finite_setOf_not_forall_intAt β₂ fun i => upperPart F (βB i)) <|
      hfinand (finite_setOf_not_forall_intAt β₂ fun i => lowerPart F (βB i)) <|
      hfinand (finite_setOf_not_intAt β₂ (diagOne y.val)) <|
      hfinand (finite_setOf_not_intAt β₂ (diagOne (y⁻¹).val)) <|
      hfinand (finite_setOf_not_forall_intAt β₂ fun i => τ.matrix (Fin 2) (β₂ i)) <|
      hfinand (finite_setOf_valuation_ne_one two_ne_zero) (finite_setOf_valuation_ne_one hd)
  set S := hGood.toFinset with hSdef
  have hS : ∀ v, v ∉ S → (BasisIntAt β₂ v ∧
      (∀ i, IntAt β₂ v (upperPart F (βB i))) ∧ (∀ i, IntAt β₂ v (lowerPart F (βB i))) ∧
      IntAt β₂ v (diagOne y.val) ∧ IntAt β₂ v (diagOne (y⁻¹).val) ∧
      (∀ i, IntAt β₂ v (τ.matrix (Fin 2) (β₂ i))) ∧ v.valuation F 2 = 1 ∧
      v.valuation F (skewSq F E) = 1) := fun v hv => by
    rw [hSdef, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
    exact hv
  obtain ⟨v₀, hv₀S, hv₀, L, g, hint, hsqf, hsqi⟩ :=
    exists_entries F E B τ hτ y hlocf hloci hN βB S
  set t : (Matrix (Fin 2) (Fin 2) B)ˣ := listProd (List.ofFn g) with ht
  set y' := globalTarget F B τ (diagOne y.val) g with hy'
  let Du : (Matrix (Fin 2) (Fin 2) B)ˣ :=
    { val := diagOne y.val
      inv := diagOne (y⁻¹).val
      val_inv := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      inv_val := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] }
  have hu : y' = ((t * Du * involutionUnit (τ.matrix (Fin 2)) t :
      (Matrix (Fin 2) (Fin 2) B)ˣ) : Matrix (Fin 2) (Fin 2) B) := rfl
  have hDτ : τ.matrix (Fin 2) (diagOne y.val) = diagOne y.val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hy]
  have hy'τ : τ.matrix (Fin 2) y' = y' := by
    rw [hy', globalTarget]
    simp only [FirstKindInvolution.map_mul, FirstKindInvolution.apply_apply, hDτ, mul_assoc]
  let K := Algebra.adjoin F {y'}
  let z : K := ⟨y', Algebra.subset_adjoin rfl⟩
  have hz : IsUnit z := isUnit_subalgebra (a := z) (by
    change IsUnit y'
    rw [hu]
    exact Units.isUnit _) fun a b => mul_comm a b
  obtain ⟨X, Y, hXY⟩ : ∃ X Y : K, X ^ 2 - algebraMap F K (skewSq F E) * Y ^ 2 = z := by
    refine exists_sq_sub_mul_sq_of_local (skewSq F E) hd z hz (fun v => ?_) (fun w => ?_)
    · by_cases hv : v ∈ S
      · rcases hsqf v hv with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (exists_mul_self_eq_tmul F B _ K z h))
      · by_cases hsq : IsSquare (algebraMap F (v.adicCompletion F) (skewSq F E))
        · exact Or.inl hsq
        have hvv₀ : v ≠ v₀ := by
          rintro rfl
          exact hsq hv₀
        obtain ⟨hB, hup, hlo, hDi, hD'i, hτi, h2, hdv⟩ := hS v hv
        have hτm : ∀ a, IntAt β₂ v a → IntAt β₂ v (τ.matrix (Fin 2) a) := fun a ha =>
          intAt_map β₂ (τ.matrix (Fin 2)).toLinearMap hτi ha
        have hlist : ∀ pq ∈ List.ofFn g, IntAt βB v pq.1 ∧ IntAt βB v pq.2 := by
          intro pq hpq
          rw [List.mem_ofFn'] at hpq
          obtain ⟨j, rfl⟩ := hpq
          exact hint v hv hvv₀ j
        obtain ⟨ht1, ht2⟩ := intAt_listProd βB hB hup hlo (List.ofFn g) hlist
        have hy'i : IntAt β₂ v y' := intAt_mul hB (intAt_mul hB ht1 hDi) (hτm _ ht1)
        have hinv : (((hz.unit⁻¹ : Kˣ) : K) : Matrix (Fin 2) (Fin 2) B) =
            τ.matrix (Fin 2) ((t⁻¹ : (Matrix (Fin 2) (Fin 2) B)ˣ) : Matrix (Fin 2) (Fin 2) B) *
              diagOne (y⁻¹).val * ((t⁻¹ : (Matrix (Fin 2) (Fin 2) B)ˣ) :
                Matrix (Fin 2) (Fin 2) B) := by
          have h1 : y' * (((hz.unit⁻¹ : Kˣ) : K) : Matrix (Fin 2) (Fin 2) B) = 1 :=
            congrArg Subtype.val hz.mul_val_inv
          rw [hu] at h1
          rw [← Units.inv_eq_of_mul_eq_one_right h1]
          simp only [mul_inv_rev, Units.val_mul, mul_assoc]
          rfl
        have hy'inv : IntAt β₂ v (((hz.unit⁻¹ : Kˣ) : K) : Matrix (Fin 2) (Fin 2) B) := by
          rw [hinv]
          exact intAt_mul hB (intAt_mul hB (hτm _ ht2) hD'i) ht2
        obtain ⟨f, hfm, hfc, hf0⟩ := exists_monic_of_intAt hB hy'i
        obtain ⟨f', hf'm, hf'c, hf'0⟩ := exists_monic_of_intAt hB hy'inv
        refine Or.inr (Or.inr ⟨h2, hdv, f, f', hfm, hf'm, hfc, hf'c, ?_, ?_⟩)
        · have : ((aeval z f : K) : Matrix (Fin 2) (Fin 2) B) = 0 := by
            rw [Polynomial.aeval_subalgebra_coe]
            exact hf0
          exact_mod_cast this
        · have : ((aeval ((hz.unit⁻¹ : Kˣ) : K) f' : K) : Matrix (Fin 2) (Fin 2) B) = 0 := by
            rw [Polynomial.aeval_subalgebra_coe]
            exact hf'0
          exact_mod_cast this
    · rcases hsqi w with h | h
      · exact Or.inl h
      · exact Or.inr (exists_mul_self_eq_tmul F B _ K z h)
  have hZm := mul_matrix_eq_of_norm F E B τ hτ y' hy'τ X Y hXY
  set Zm := (X : Matrix (Fin 2) (Fin 2) B) +
    algebraMap E (Matrix (Fin 2) (Fin 2) B) (skewRoot F E) * (Y : Matrix (Fin 2) (Fin 2) B)
  refine exists_eq_mul_of_diag_unit F E B τ hτ y
    (((t⁻¹ : (Matrix (Fin 2) (Fin 2) B)ˣ) : Matrix (Fin 2) (Fin 2) B) * Zm) ?_
  have h1 : τ.matrix (Fin 2) (t : Matrix (Fin 2) (Fin 2) B) *
      τ.matrix (Fin 2) ((t⁻¹ : (Matrix (Fin 2) (Fin 2) B)ˣ) : Matrix (Fin 2) (Fin 2) B) = 1 := by
    rw [← FirstKindInvolution.map_mul, Units.inv_mul, FirstKindInvolution.map_one]
  rw [FirstKindInvolution.map_mul]
  calc ((t⁻¹ : (Matrix (Fin 2) (Fin 2) B)ˣ) : Matrix (Fin 2) (Fin 2) B) * Zm *
        (τ.matrix (Fin 2) Zm *
          τ.matrix (Fin 2) ((t⁻¹ : (Matrix (Fin 2) (Fin 2) B)ˣ) : Matrix (Fin 2) (Fin 2) B))
      = ((t⁻¹ : (Matrix (Fin 2) (Fin 2) B)ˣ) : Matrix (Fin 2) (Fin 2) B) *
          (Zm * τ.matrix (Fin 2) Zm) *
          τ.matrix (Fin 2) ((t⁻¹ : (Matrix (Fin 2) (Fin 2) B)ˣ) : Matrix (Fin 2) (Fin 2) B) := by
        simp only [mul_assoc]
    _ = ((t⁻¹ : (Matrix (Fin 2) (Fin 2) B)ˣ) : Matrix (Fin 2) (Fin 2) B) *
          ((t : Matrix (Fin 2) (Fin 2) B) * diagOne y.val * τ.matrix (Fin 2) t) *
          τ.matrix (Fin 2) ((t⁻¹ : (Matrix (Fin 2) (Fin 2) B)ˣ) : Matrix (Fin 2) (Fin 2) B) := by
        rw [hZm]
    _ = (((t⁻¹ : (Matrix (Fin 2) (Fin 2) B)ˣ) : Matrix (Fin 2) (Fin 2) B) * t) * diagOne y.val *
          (τ.matrix (Fin 2) (t : Matrix (Fin 2) (Fin 2) B) *
            τ.matrix (Fin 2) ((t⁻¹ : (Matrix (Fin 2) (Fin 2) B)ˣ) : Matrix (Fin 2) (Fin 2) B)) := by
        simp only [mul_assoc]
    _ = !![(y : B), 0; 0, 1] := by
        rw [Units.inv_mul, h1, one_mul, mul_one]

end Global

end Langlands.CentralSimple.Landherr
