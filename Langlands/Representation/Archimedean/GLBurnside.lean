import Langlands.Representation.Archimedean.GLLowestWeight
import Langlands.Representation.Archimedean.LowerVerma
import Langlands.Algebra.SandwichDimensionBoundProof

/-!
# Families, representations and Burnside's theorem

* `famOf σ`: the family `σ(E_pq)` of a representation `σ` of `𝔤𝔩_n(ℂ)`; it satisfies the
  relations (`isGlFamily_famOf`) and has integral weights when `σ` does (`intWeights_famOf`).
* `lieOf e he`: conversely, the representation `Y ↦ Σ_{p,q} Y_pq e_pq` of a family satisfying
  the relations, and `envOf e he` the induced action of `U(𝔤𝔩_n(ℂ))`.
* `exists_eq_smul_of_commute` (Schur's lemma): on a finite-dimensional irreducible module an
  operator commuting with every `e_pq` is a scalar.
* `envOf_surjective` (Burnside's theorem): on a finite-dimensional irreducible module every
  linear operator is the action of an element of `U(𝔤𝔩_n(ℂ))`. After making `V` a simple
  `U(𝔤𝔩_n(ℂ))`-module, this is the Library's `SandwichDimensionBound.action_surjective`.
* `centChar e he`: the character of the center of `U(𝔤𝔩_n(ℂ))` on an irreducible module.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GLReynolds

open ComplexJacquetFinite Module

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

/-! ### Families and representations -/

section Bridge

/-- The family `σ(E_pq)` of a representation `σ`. -/
def famOf (σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V) : Fin n → Fin n → Module.End ℂ V :=
  fun p q => σ (Matrix.single p q 1)

theorem famOf_apply (σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V) (p q : Fin n) :
    famOf σ p q = σ (Matrix.single p q 1) := rfl

theorem single_mul_single_one (a b c d : Fin n) :
    (Matrix.single a b (1 : ℂ)) * Matrix.single c d 1 =
      if b = c then Matrix.single a d 1 else 0 := by
  split_ifs with h
  · subst h; rw [Matrix.single_mul_single_same, one_mul]
  · exact Matrix.single_mul_single_of_ne (α := ℂ) (h := h) ..

theorem isGlFamily_famOf (σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V) :
    IsGlFamily (famOf σ) := by
  intro a b c d
  simp only [famOf]
  rw [← Ring.lie_def, ← LieHom.map_lie, Ring.lie_def, single_mul_single_one,
    single_mul_single_one]
  split_ifs <;> simp

theorem intWeights_famOf {σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V}
    (hσ : VermaGL.HasIntegralWeights σ) : IntWeights (famOf σ) := hσ

/-- The linear map `Y ↦ Σ_{p,q} Y_pq e_pq`. -/
def lieLin (e : Fin n → Fin n → Module.End ℂ V) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ V where
  toFun Y := ∑ p, ∑ q, Y p q • e p q
  map_add' Y Z := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c Y := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

theorem lieLin_single (e : Fin n → Fin n → Module.End ℂ V) (i j : Fin n) (x : ℂ) :
    lieLin e (Matrix.single i j x) = x • e i j := by
  change ∑ p, ∑ q, Matrix.single i j x p q • e p q = _
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro q _ hq
    simp [Ne.symm hq]
  · simp
  · intro p _ hp
    apply Finset.sum_eq_zero
    intro q _
    simp [Ne.symm hp]
  · simp

variable {e : Fin n → Fin n → Module.End ℂ V}

theorem lieLin_lie (he : IsGlFamily e) (Y Z : Matrix (Fin n) (Fin n) ℂ) :
    lieLin e ⁅Y, Z⁆ = ⁅lieLin e Y, lieLin e Z⁆ := by
  induction Y using Matrix.induction_on' with
  | h_zero => simp
  | h_add Y₁ Y₂ h₁ h₂ => rw [add_lie, map_add, h₁, h₂, map_add, add_lie]
  | h_std_basis i j x =>
    induction Z using Matrix.induction_on' with
    | h_zero => simp
    | h_add Z₁ Z₂ h₁ h₂ => rw [lie_add, map_add, h₁, h₂, map_add, lie_add]
    | h_std_basis k l y =>
      rw [Ring.lie_def, Ring.lie_def, lieLin_single, lieLin_single, map_sub,
        smul_mul_smul_comm, smul_mul_smul_comm, mul_comm y x, ← smul_sub, he]
      by_cases hjk : j = k <;> by_cases hli : l = i
      · subst hjk hli
        simp [Matrix.single_mul_single_same, lieLin_single, smul_sub, mul_comm]
      · subst hjk
        simp [Matrix.single_mul_single_same, lieLin_single, hli]
      · subst hli
        simp [Matrix.single_mul_single_same, lieLin_single, hjk, mul_comm]
      · simp [hjk, hli]

/-- The representation `Y ↦ Σ_{p,q} Y_pq e_pq` of a family satisfying the relations. -/
def lieOf (e : Fin n → Fin n → Module.End ℂ V) (he : IsGlFamily e) :
    Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V :=
  { lieLin e with map_lie' := fun {Y Z} => lieLin_lie he Y Z }

theorem lieOf_apply (he : IsGlFamily e) (Y : Matrix (Fin n) (Fin n) ℂ) :
    lieOf e he Y = lieLin e Y := rfl

theorem lieOf_single (he : IsGlFamily e) (p q : Fin n) :
    lieOf e he (Matrix.single p q 1) = e p q := by
  rw [lieOf_apply, lieLin_single, one_smul]

theorem famOf_lieOf (he : IsGlFamily e) : famOf (lieOf e he) = e := by
  funext p q
  exact lieOf_single he p q

/-- The action of `U(𝔤𝔩_n(ℂ))` induced by a family. -/
def envOf (e : Fin n → Fin n → Module.End ℂ V) (he : IsGlFamily e) :
    VermaGL.glU n →ₐ[ℂ] Module.End ℂ V :=
  UniversalEnvelopingAlgebra.lift ℂ (lieOf e he)

theorem envOf_ι (he : IsGlFamily e) (Y : Matrix (Fin n) (Fin n) ℂ) :
    envOf e he (UniversalEnvelopingAlgebra.ι ℂ Y) = lieOf e he Y := by
  rw [envOf, UniversalEnvelopingAlgebra.lift_ι_apply]

theorem envOf_unitU (he : IsGlFamily e) (p q : Fin n) :
    envOf e he (VermaGL.unitU n p q) = e p q := by
  rw [VermaGL.unitU, envOf_ι, lieOf_single]

end Bridge

/-! ### Schur and Burnside -/

section Burnside

variable {e : Fin n → Fin n → Module.End ℂ V}

/-- **Schur's lemma.** On a finite-dimensional irreducible module an operator commuting with
every `e_pq` is a scalar. -/
theorem exists_eq_smul_of_commute [FiniteDimensional ℂ V] [Nontrivial V]
    (hirr : ∀ Z : Submodule ℂ V, IsStable e Z → Z ≠ ⊥ → Z = ⊤)
    (T : Module.End ℂ V) (hT : ∀ p q, T * e p q = e p q * T) : ∃ μ : ℂ, ∀ v, T v = μ • v := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  refine ⟨μ, ?_⟩
  have hstab : IsStable e (T.eigenspace μ) := by
    intro p q v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [← Module.End.mul_apply, hT, Module.End.mul_apply, hv, map_smul]
  have htop := hirr _ hstab (Module.End.hasEigenvalue_iff.mp hμ)
  intro v
  have hv : v ∈ T.eigenspace μ := by rw [htop]; trivial
  exact Module.End.mem_eigenspace_iff.mp hv

/-- **Burnside's theorem.** On a finite-dimensional irreducible module every linear operator is
the action of an element of `U(𝔤𝔩_n(ℂ))`. -/
theorem envOf_surjective [FiniteDimensional ℂ V] [Nontrivial V] (he : IsGlFamily e)
    (hirr : ∀ Z : Submodule ℂ V, IsStable e Z → Z ≠ ⊥ → Z = ⊤) :
    Function.Surjective (envOf e he) := by
  classical
  set ρ := envOf e he with hρ
  let _ : Module (VermaGL.glU n) V :=
    Module.compHom V (ρ : VermaGL.glU n →+* Module.End ℂ V)
  have hsmul : ∀ (r : VermaGL.glU n) (v : V), r • v = ρ r v := fun _ _ => rfl
  have halg : ∀ (c : ℂ) (v : V), (algebraMap ℂ (VermaGL.glU n) c) • v = c • v := by
    intro c v
    rw [hsmul, AlgHom.commutes, Module.algebraMap_end_apply]
  -- `V` is a simple `U`-module
  have hsimple : IsSimpleModule (VermaGL.glU n) V := by
    refine { toIsSimpleOrder := { toNontrivial := inferInstance, eq_bot_or_eq_top := fun S => ?_ } }
    let Z : Submodule ℂ V :=
      { carrier := S
        add_mem' := S.add_mem
        zero_mem' := S.zero_mem
        smul_mem' := fun c v hv => by
          have := S.smul_mem (algebraMap ℂ (VermaGL.glU n) c) hv
          rwa [halg] at this }
    have hZ : IsStable e Z := by
      intro p q v hv
      have := S.smul_mem (VermaGL.unitU n p q) hv
      rwa [hsmul, envOf_unitU] at this
    by_cases hS : S = ⊥
    · exact Or.inl hS
    · right
      have hZ0 : Z ≠ ⊥ := by
        intro h
        apply hS
        rw [eq_bot_iff]
        intro v hv
        have : v ∈ Z := hv
        rw [h] at this
        exact this
      have hZt := hirr Z hZ hZ0
      rw [eq_top_iff]
      intro v _
      have : v ∈ Z := by rw [hZt]; trivial
      exact this
  -- Burnside's theorem for the simple `U`-module `V`: the Library's
  -- `SandwichDimensionBound.action_surjective` (Schur's lemma plus Jacobson density)
  have : IsScalarTower ℂ (VermaGL.glU n) V :=
    ⟨fun c r v => by rw [Algebra.smul_def, mul_smul, halg]⟩
  intro t
  obtain ⟨r, hr⟩ := SandwichDimensionBound.action_surjective ℂ (VermaGL.glU n) V t
  exact ⟨r, LinearMap.ext fun v => by rw [← hr]; rfl⟩

/-- A central element acts on a finite-dimensional irreducible module by a scalar. -/
theorem exists_envOf_center [FiniteDimensional ℂ V] [Nontrivial V] (he : IsGlFamily e)
    (hirr : ∀ Z : Submodule ℂ V, IsStable e Z → Z ≠ ⊥ → Z = ⊤) (z : VermaGL.center n) :
    ∃ μ : ℂ, envOf e he z = μ • 1 := by
  obtain ⟨μ, hμ⟩ := exists_eq_smul_of_commute hirr (envOf e he z) fun p q => by
    rw [← envOf_unitU he, ← map_mul, ← map_mul, Subalgebra.mem_center_iff.mp z.2]
  exact ⟨μ, LinearMap.ext fun v => by rw [hμ]; rfl⟩

theorem smul_one_injective [Nontrivial V] {a b : ℂ}
    (h : a • (1 : Module.End ℂ V) = b • 1) : a = b :=
  smul_left_injective ℂ (one_ne_zero : (1 : Module.End ℂ V) ≠ 0) h

/-- The scalar by which a central element acts (`envOf_center_eq`). -/
def cScal [FiniteDimensional ℂ V] [Nontrivial V] (he : IsGlFamily e)
    (hirr : ∀ Z : Submodule ℂ V, IsStable e Z → Z ≠ ⊥ → Z = ⊤) (z : VermaGL.center n) : ℂ :=
  Classical.choose (exists_envOf_center he hirr z)

theorem envOf_center_eq [FiniteDimensional ℂ V] [Nontrivial V] (he : IsGlFamily e)
    (hirr : ∀ Z : Submodule ℂ V, IsStable e Z → Z ≠ ⊥ → Z = ⊤) (z : VermaGL.center n) :
    envOf e he (z : VermaGL.glU n) = cScal he hirr z • 1 :=
  Classical.choose_spec (exists_envOf_center he hirr z)

/-- The central character of a finite-dimensional irreducible module. -/
def centChar [FiniteDimensional ℂ V] [Nontrivial V] (he : IsGlFamily e)
    (hirr : ∀ Z : Submodule ℂ V, IsStable e Z → Z ≠ ⊥ → Z = ⊤) :
    VermaGL.center n →ₐ[ℂ] ℂ where
  toFun z := cScal he hirr z
  map_one' := by
    have h : envOf e he (1 : VermaGL.glU n) = cScal he hirr 1 • 1 := envOf_center_eq he hirr 1
    rw [map_one] at h
    exact smul_one_injective (V := V) (by rw [← h, one_smul])
  map_mul' z z' := by
    have h : envOf e he ((z : VermaGL.glU n) * z') = cScal he hirr (z * z') • 1 :=
      envOf_center_eq he hirr (z * z')
    rw [map_mul, envOf_center_eq he hirr z, envOf_center_eq he hirr z', smul_mul_smul_comm,
      one_mul] at h
    exact smul_one_injective (V := V) h.symm
  map_zero' := by
    have h : envOf e he (0 : VermaGL.glU n) = cScal he hirr 0 • 1 := envOf_center_eq he hirr 0
    rw [map_zero] at h
    exact smul_one_injective (V := V) (by rw [← h, zero_smul])
  map_add' z z' := by
    have h : envOf e he ((z : VermaGL.glU n) + z') = cScal he hirr (z + z') • 1 :=
      envOf_center_eq he hirr (z + z')
    rw [map_add, envOf_center_eq he hirr z, envOf_center_eq he hirr z', ← add_smul] at h
    exact smul_one_injective (V := V) h.symm
  commutes' c := by
    have h : envOf e he ((algebraMap ℂ (VermaGL.center n) c : VermaGL.center n) : VermaGL.glU n) =
        cScal he hirr (algebraMap ℂ _ c) • 1 := envOf_center_eq he hirr _
    rw [Subalgebra.coe_algebraMap] at h
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one] at h
    exact smul_one_injective (V := V) h.symm

theorem envOf_center_apply [FiniteDimensional ℂ V] [Nontrivial V] (he : IsGlFamily e)
    (hirr : ∀ Z : Submodule ℂ V, IsStable e Z → Z ≠ ⊥ → Z = ⊤) (z : VermaGL.center n)
    (v : V) : envOf e he z v = centChar he hirr z • v := by
  rw [envOf_center_eq he hirr z]
  rfl

end Burnside

end GLReynolds

end Langlands.Archimedean
