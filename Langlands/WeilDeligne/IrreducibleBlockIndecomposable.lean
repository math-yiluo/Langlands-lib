import Langlands.WeilDeligne.BlockStatements

/-!
# A block with irreducible Weil factor is indecomposable

For an irreducible finite representation `σ` and `m : ℕ`, the uncentered block
`σ ⊗ S_(m+1)` is an indecomposable Weil–Deligne pair. The proof embeds `σ` as
the top-weight line `a ↦ a ⊗ e_top`, which is the monodromy kernel: a stable
subspace meets this line in a subrepresentation of `σ`, and a stable subspace that
meets it trivially is zero because monodromy is nilpotent. Indecomposability is
also shown to be invariant under pair equivalence, and a one-term direct sum of
pairs is equivalent to its term.
-/

noncomputable section

universe uK uG uV uW

open scoped TensorProduct DirectSum

namespace Langlands.WeilDeligneRepresentation

namespace Special

variable {K : Type uK} [Field K]

/-- Lowering on the coordinates of a positive-rank block: the coordinate at `j < m`
is the old coordinate at `j + 1`, and the top coordinate is zero. -/
def lowering (K : Type uK) [Field K] (m : ℕ) : Module.End K (Fin (m + 1) → K) :=
  LinearMap.pi fun j =>
    if h : j.val < m then LinearMap.proj ⟨j.val + 1, by omega⟩ else 0

theorem lowering_apply (m : ℕ) (v : Fin (m + 1) → K) (j : Fin (m + 1)) :
    lowering K m v j = if h : j.val < m then v ⟨j.val + 1, by omega⟩ else 0 := by
  by_cases h : j.val < m <;> simp [lowering, h]

/-- Lowering inverts raising away from the top coordinate. -/
theorem lowering_raising_add (m : ℕ) (w : Fin (m + 1) → K) :
    lowering K m (raising K (m + 1) w) + w (Fin.last m) • topVector K m = w := by
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lowering_apply, topVector,
    basisVector]
  by_cases h : j.val < m
  · have hj : j ≠ Fin.last m := by
      intro he
      rw [he, Fin.val_last] at h
      exact lt_irrefl m h
    simp [h, hj, raising_apply]
  · have hj : j = Fin.last m := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
    subst hj
    simp

variable {V : Type uV} [AddCommGroup V] [Module K V]

/-- The top-weight embedding `a ↦ a ⊗ e_top`. -/
def topEmbedding (V : Type uV) [AddCommGroup V] [Module K V] (m : ℕ) :
    V →ₗ[K] V ⊗[K] (Fin (m + 1) → K) :=
  (TensorProduct.mk K V (Fin (m + 1) → K)).flip (topVector K m)

/-- The top-coordinate projection `a ⊗ w ↦ w_top • a`. -/
def topProjection (V : Type uV) [AddCommGroup V] [Module K V] (m : ℕ) :
    V ⊗[K] (Fin (m + 1) → K) →ₗ[K] V :=
  (TensorProduct.rid K V).toLinearMap ∘ₗ LinearMap.lTensor V (LinearMap.proj (Fin.last m))

theorem topEmbedding_apply (m : ℕ) (a : V) :
    topEmbedding (K := K) V m a = a ⊗ₜ topVector K m := rfl

theorem topProjection_tmul (m : ℕ) (a : V) (w : Fin (m + 1) → K) :
    topProjection V m (a ⊗ₜ w) = w (Fin.last m) • a := by
  simp [topProjection]

theorem topProjection_topEmbedding (m : ℕ) (a : V) :
    topProjection V m (topEmbedding (K := K) V m a) = a := by
  rw [topEmbedding_apply, topProjection_tmul]
  simp [topVector, basisVector]

/-- Every tensor is its lowered monodromy image plus its top-weight part. -/
theorem lTensor_lowering_raising_add (m : ℕ) (x : V ⊗[K] (Fin (m + 1) → K)) :
    LinearMap.lTensor V (lowering K m) (LinearMap.lTensor V (raising K (m + 1)) x) +
      topEmbedding V m (topProjection V m x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a w =>
    rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, topProjection_tmul,
      topEmbedding_apply, TensorProduct.smul_tmul, ← TensorProduct.tmul_add,
      lowering_raising_add]
  | add x y hx hy =>
    simp only [map_add]
    rw [add_add_add_comm, hx, hy]

/-- A tensor killed by `1 ⊗ raising` lies on the top-weight line. -/
theorem topEmbedding_topProjection_of_lTensor_raising (m : ℕ) (x : V ⊗[K] (Fin (m + 1) → K))
    (hx : LinearMap.lTensor V (raising K (m + 1)) x = 0) :
    topEmbedding V m (topProjection V m x) = x := by
  have h := lTensor_lowering_raising_add m x
  rwa [hx, map_zero, zero_add] at h

end Special

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

/-- The block monodromy is raising on the special factor. -/
theorem block_monodromy_apply (A : FiniteRepresentation.{uK, uG, uV} K G) (m : ℕ)
    (x : block ν A m) :
    (block ν A m).monodromy x = LinearMap.lTensor A (Special.raising K m) x := by
  change (TensorProduct.map (0 : Module.End K A) (1 : Module.End K (Fin m → K)) +
    TensorProduct.map (1 : Module.End K A) (Special.raising K m)) x = _
  rw [TensorProduct.map_zero_left, zero_add]
  rfl

/-- The Weil action on the top-weight line has weight `ν^m`. -/
theorem block_representation_topEmbedding (A : FiniteRepresentation.{uK, uG, uV} K G)
    (m : ℕ) (g : G) (a : A) :
    (block ν A (m + 1)).representation g (Special.topEmbedding (K := K) A m a) =
      ((ν g : K) ^ m) • Special.topEmbedding (K := K) A m (A.representation g a) := by
  rw [Special.topEmbedding_apply, Special.topEmbedding_apply]
  change A.representation g a ⊗ₜ Special.action ν (m + 1) g (Special.topVector K m) = _
  rw [Special.action_topVector]
  exact TensorProduct.tmul_smul (R := K) (M := A) (N := Fin (m + 1) → K) ((ν g : K) ^ m)
    (A.representation g a) (Special.topVector K m)

/-- The isomorphism `⨁_{i : Fin 1} X i ≃ X 0` of carriers. -/
def directSumFinOneLinearEquiv (X : Fin 1 → WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    (directSum X) ≃ₗ[K] X 0 where
  toLinearMap := DirectSum.component K (Fin 1) (fun i => X i) 0
  invFun := DirectSum.lof K (Fin 1) (fun i => X i) 0
  left_inv x := by
    apply DirectSum.ext
    intro i
    obtain rfl : i = 0 := Subsingleton.elim i 0
    exact DirectSum.lof_apply K (0 : Fin 1) _
  right_inv a := DirectSum.component.lof_self (M := fun i : Fin 1 => X i) K 0 a

/-- The zeroth component commutes with the componentwise monodromy. -/
theorem component_directSum_monodromy (X : Fin 1 → WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (x : directSum X) :
    DirectSum.component K (Fin 1) (fun i => X i) 0 ((directSum X).monodromy x) =
      (X 0).monodromy (DirectSum.component K (Fin 1) (fun i => X i) 0 x) :=
  rfl

/-- A one-term direct sum of pairs is equivalent to its only term. -/
def directSumFinOneEquiv (X : Fin 1 → WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    Equiv (directSum X) (X 0) where
  representationEquiv :=
    Representation.Equiv.mk (directSumFinOneLinearEquiv X) fun _ => rfl
  comm_monodromy := LinearMap.ext fun x => component_directSum_monodromy X x

namespace Blocks

variable {G : Type uG} [Group G] {ν : G →* ℂˣ}

/-- Indecomposability is invariant under genuine equivalence of pairs. -/
theorem IsIndecomposable.of_equiv {A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν}
    {B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν} (e : Equiv A B)
    (hA : IsIndecomposable A) : IsIndecomposable B := by
  obtain ⟨hnt, hdec⟩ := hA
  let f : A ≃ₗ[ℂ] B := e.representationEquiv.toLinearEquiv
  have hfN : ∀ x, f (A.monodromy x) = B.monodromy (f x) := fun x =>
    LinearMap.congr_fun e.comm_monodromy x
  have hfg : ∀ g x, f (A.representation g x) = B.representation g (f x) := fun g x =>
    Representation.IntertwiningMap.isIntertwining _ _ e.representationEquiv.toIntertwiningMap g x
  have hstab : ∀ U : Submodule ℂ B, LinearAlgebra.IsStable B U →
      LinearAlgebra.IsStable A (U.comap f.toLinearMap) := by
    intro U hU
    refine ⟨fun g x hx => ?_, fun x hx => ?_⟩
    · change f (A.representation g x) ∈ U
      rw [hfg]
      exact hU.1 g hx
    · change f (A.monodromy x) ∈ U
      rw [hfN]
      exact hU.2 hx
  have := hnt
  refine ⟨f.symm.toEquiv.nontrivial, fun S T hS hT hST => ?_⟩
  have hc : IsCompl (S.comap f.toLinearMap) (T.comap f.toLinearMap) :=
    (Submodule.orderIsoMapComap f).symm.isCompl hST
  rcases hdec _ _ (hstab S hS) (hstab T hT) hc with h | h
  · left
    exact (map_eq_bot_iff (Submodule.orderIsoMapComap f).symm).mp h
  · right
    exact (map_eq_bot_iff (Submodule.orderIsoMapComap f).symm).mp h

/-- An irreducible representation has a nonzero vector. -/
theorem exists_ne_zero_of_isIrreducible {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible) : ∃ a : V, a ≠ 0 := by
  by_contra h
  push Not at h
  apply hρ.bot_ne_top
  apply Subrepresentation.toSubmodule_injective
  change (⊥ : Submodule ℂ V) = ⊤
  rw [Submodule.eq_top_iff']
  intro a
  rw [h a]
  exact zero_mem _

/-- A block `σ ⊗ S_(m+1)` with irreducible Weil factor `σ` is indecomposable. -/
theorem isIndecomposable_block {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    (hA : A.representation.IsIrreducible) (m : ℕ) :
    IsIndecomposable (block ν A (m + 1)) := by
  set X := block ν A (m + 1) with hX
  let ι : A →ₗ[ℂ] X := Special.topEmbedding A m
  let φ : X →ₗ[ℂ] A := Special.topProjection A m
  have hφι : ∀ a, φ (ι a) = a := Special.topProjection_topEmbedding m
  have hker : ∀ x : X, X.monodromy x = 0 → ι (φ x) = x := by
    intro x hx
    exact Special.topEmbedding_topProjection_of_lTensor_raising m x
      ((block_monodromy_apply A (m + 1) x).symm.trans hx)
  have hsub : ∀ S : Submodule ℂ X, LinearAlgebra.IsStable X S → ∀ (g : G) (a : A),
      ι a ∈ S → ι (A.representation g a) ∈ S := by
    intro S hS g a ha
    have h1 : ((ν g : ℂ) ^ m) • ι (A.representation g a) ∈ S := by
      have h0 : X.representation g (ι a) ∈ S := hS.1 g ha
      have heq : X.representation g (ι a) = ((ν g : ℂ) ^ m) • ι (A.representation g a) :=
        block_representation_topEmbedding A m g a
      rwa [heq] at h0
    have hc : ((ν g : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (ν g).ne_zero
    have h2 := S.smul_mem ((ν g : ℂ) ^ m)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
  let sub : ∀ S : Submodule ℂ X, LinearAlgebra.IsStable X S →
      Subrepresentation A.representation := fun S hS =>
    ⟨S.comap ι, fun g a ha => hsub S hS g a ha⟩
  have hbot : ∀ (S : Submodule ℂ X) (hS : LinearAlgebra.IsStable X S),
      sub S hS = ⊥ → S = ⊥ := by
    intro S hS h
    have hzero : ∀ y ∈ S, X.monodromy y = 0 → y = 0 := by
      intro y hy hNy
      have hmem : φ y ∈ (sub S hS).toSubmodule := by
        change ι (φ y) ∈ S
        rw [hker y hNy]
        exact hy
      rw [h] at hmem
      have h0 : φ y = 0 := (Submodule.mem_bot ℂ).mp hmem
      rw [← hker y hNy, h0, map_zero]
    have hind : ∀ k : ℕ, ∀ y ∈ S, (X.monodromy ^ k) y = 0 → y = 0 := by
      intro k
      induction k with
      | zero =>
        intro y _ hy
        simpa using hy
      | succ k ih =>
        intro y hy hk
        have hNy : X.monodromy y ∈ S := hS.2 hy
        refine hzero y hy (ih _ hNy ?_)
        rw [← Module.End.mul_apply, ← pow_succ]
        exact hk
    obtain ⟨n, hn⟩ := X.nilpotent
    rw [eq_bot_iff]
    intro y hy
    exact (Submodule.mem_bot ℂ).mpr (hind n y hy (by rw [hn]; rfl))
  obtain ⟨a0, ha0⟩ := exists_ne_zero_of_isIrreducible hA
  have hι0 : ι a0 ≠ 0 := by
    intro h
    apply ha0
    rw [← hφι a0, h, map_zero]
  refine ⟨⟨ι a0, 0, hι0⟩, fun S T hS hT hST => ?_⟩
  have := hA
  rcases eq_bot_or_eq_top (sub S hS) with h1 | h1
  · exact Or.inl (hbot S hS h1)
  rcases eq_bot_or_eq_top (sub T hT) with h2 | h2
  · exact Or.inr (hbot T hT h2)
  exfalso
  have hS0 : a0 ∈ (sub S hS).toSubmodule := by
    rw [h1]
    exact Submodule.mem_top
  have hT0 : a0 ∈ (sub T hT).toSubmodule := by
    rw [h2]
    exact Submodule.mem_top
  exact hι0 ((Submodule.disjoint_def.mp hST.disjoint) (ι a0) hS0 hT0)

end Blocks

end Langlands.WeilDeligneRepresentation
