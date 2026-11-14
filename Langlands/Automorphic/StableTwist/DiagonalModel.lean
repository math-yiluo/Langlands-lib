import Langlands.Automorphic.StableTwistGammaMatchStatement
import Langlands.Correspondence.OperationCompatibility
import Langlands.Weil.Representation.TwistProperties
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Diagonal Weil–Deligne models

For continuous characters `η_1, …, η_n` of a topological group `G`, the diagonal action
`v ↦ (η_i(g) v_i)_i` on a universe-lifted copy of `ℂ^n`, with zero monodromy, is a
continuous Weil–Deligne pair of rank `n` and determinant `∏ η_i`. In the standard basis
every group element acts by the diagonal matrix `diag(η_1(g), …, η_n(g))`, and twisting by a
continuous character `χ` gives the diagonal pair attached to `χ η_1, …, χ η_n`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Automorphic.StableTwist

open Langlands.Correspondence

universe u uG uV

section Diagonal

variable {G : Type uG} [Group G] {n : ℕ}

/-- The diagonal operator `v ↦ (c_i v_i)_i` on a universe-lifted copy of `ℂ^n`, linear in
the diagonal entries `c`. -/
def diagonalOperator (n : ℕ) :
    (Fin n → ℂ) →ₗ[ℂ] Module.End ℂ (ULift.{uV} (Fin n → ℂ)) where
  toFun c :=
    { toFun := fun v => ⟨fun i => c i * v.down i⟩
      map_add' := fun v w => by
        apply ULift.ext
        funext i
        simp [mul_add]
      map_smul' := fun a v => by
        apply ULift.ext
        funext i
        simp [mul_left_comm] }
  map_add' c d := by
    apply LinearMap.ext
    intro v
    apply ULift.ext
    funext i
    simp [add_mul]
  map_smul' a c := by
    apply LinearMap.ext
    intro v
    apply ULift.ext
    funext i
    simp [mul_assoc]

@[simp]
theorem diagonalOperator_apply_down (c : Fin n → ℂ) (v : ULift.{uV} (Fin n → ℂ)) (i : Fin n) :
    (diagonalOperator.{uV} n c v).down i = c i * v.down i := rfl

/-- The diagonal action `v ↦ (η_i(g) v_i)_i` on a universe-lifted copy of `ℂ^n`. -/
def diagonalRepresentation (η : Fin n → G →* ℂˣ) :
    Representation ℂ G (ULift.{uV} (Fin n → ℂ)) where
  toFun g := diagonalOperator.{uV} n (fun i => (η i g : ℂ))
  map_one' := by
    apply LinearMap.ext
    intro v
    apply ULift.ext
    funext i
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply ULift.ext
    funext i
    simp [mul_assoc]

@[simp]
theorem diagonalRepresentation_apply_down (η : Fin n → G →* ℂˣ) (g : G)
    (v : ULift.{uV} (Fin n → ℂ)) (i : Fin n) :
    (diagonalRepresentation.{uG, uV} η g v).down i = (η i g : ℂ) * v.down i := rfl

/-- The standard basis of the lifted coordinate space. -/
def diagonalBasis (n : ℕ) : Module.Basis (Fin n) ℂ (ULift.{uV} (Fin n → ℂ)) :=
  (Pi.basisFun ℂ (Fin n)).map ULift.moduleEquiv.symm

@[simp]
theorem diagonalBasis_repr (v : ULift.{uV} (Fin n → ℂ)) (i : Fin n) :
    (diagonalBasis.{uV} n).repr v i = v.down i := rfl

@[simp]
theorem diagonalBasis_apply_down (j : Fin n) :
    (diagonalBasis.{uV} n j).down = Pi.single j 1 := by
  rw [diagonalBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  rfl

/-- In the standard basis the diagonal action has matrix entries `η_i(g)` on the
diagonal and zero elsewhere. -/
theorem diagonalBasis_repr_apply (η : Fin n → G →* ℂˣ) (g : G) (i j : Fin n) :
    (diagonalBasis.{uV} n).repr (diagonalRepresentation.{uG, uV} η g
      (diagonalBasis.{uV} n j)) i = if i = j then (η i g : ℂ) else 0 := by
  rw [diagonalBasis_repr, diagonalRepresentation_apply_down, diagonalBasis_apply_down]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-- The diagonal representation as a finite-dimensional representation. -/
def diagonalFinite (η : Fin n → G →* ℂˣ) : FiniteRepresentation.{0, uG, uV} ℂ G :=
  FiniteRepresentation.of (diagonalRepresentation.{uG, uV} η)

theorem diagonalFinite_rank (η : Fin n → G →* ℂˣ) :
    (diagonalFinite.{uG, uV} η).rank = n := by
  change Module.finrank ℂ (ULift.{uV} (Fin n → ℂ)) = n
  rw [finrank_ulift, Module.finrank_fin_fun]

/-- The determinant character of the diagonal representation is the product of the
characters. -/
theorem diagonalFinite_determinantCharacter (η : Fin n → G →* ℂˣ) :
    FiniteRepresentation.determinantCharacter (diagonalFinite.{uG, uV} η) = ∏ i, η i := by
  ext g
  rw [FiniteRepresentation.determinantCharacter_apply]
  change LinearMap.det (diagonalRepresentation.{uG, uV} η g) = _
  rw [← LinearMap.det_toMatrix (diagonalBasis.{uV} n)]
  have hM : LinearMap.toMatrix (diagonalBasis.{uV} n) (diagonalBasis.{uV} n)
      (diagonalRepresentation.{uG, uV} η g) = Matrix.diagonal (fun i => (η i g : ℂ)) := by
    ext i j
    rw [LinearMap.toMatrix_apply, diagonalBasis_repr_apply, Matrix.diagonal_apply]
  rw [hM, Matrix.det_diagonal]
  have key : ∀ s : Finset (Fin n), ((∏ i ∈ s, η i) g : ℂˣ) = ∏ i ∈ s, η i g := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj, MonoidHom.mul_apply, ih]
  rw [key Finset.univ, Units.coe_prod]

variable [TopologicalSpace G]

/-- Continuous characters give a continuous diagonal representation. -/
theorem diagonalFinite_isContinuous (η : Fin n → G →ₜ* ℂˣ) :
    (diagonalFinite.{uG, uV} (fun i => (η i).toMonoidHom)).IsContinuous := by
  let V := ULift.{uV} (Fin n → ℂ)
  let : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ (Module.End ℂ V)
  have : ContinuousSMul ℂ (Module.End ℂ V) := ModuleTopology.continuousSMul ℂ _
  have : ContinuousAdd (Module.End ℂ V) := ModuleTopology.continuousAdd ℂ _
  have hL : Continuous (diagonalOperator.{uV} n) :=
    IsModuleTopology.continuous_of_linearMap (diagonalOperator.{uV} n)
  have hc : Continuous (fun g : G => fun i => ((η i g : ℂˣ) : ℂ)) :=
    continuous_pi fun i => Units.continuous_val.comp (η i).continuous
  exact hL.comp hc

end Diagonal

section WeilDeligne

variable {G : Type uG} [Group G] {n : ℕ} (ν : G →* ℂˣ)

/-- The diagonal Weil–Deligne pair: the diagonal action with zero monodromy. -/
def diagonalWD (η : Fin n → G →* ℂˣ) : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν :=
  WeilDeligneRepresentation.zeroMonodromy ν (diagonalFinite.{uG, uV} η)

/-- Twisting the diagonal pair of `η` by `χ` gives the diagonal pair of `χ η_i`, by the
identity map of the common carrier. -/
def twistDiagonalWDEquiv (χ : G →* ℂˣ) (η η' : Fin n → G →* ℂˣ) (h : ∀ i, η' i = χ * η i) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.twist χ (diagonalWD.{uG, uV} ν η))
      (diagonalWD.{uG, uV} ν η') where
  representationEquiv := Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun g => by
    apply LinearMap.ext
    intro v
    apply ULift.ext
    funext i
    change (χ g : ℂ) * ((η i g : ℂ) * v.down i) = (η' i g : ℂ) * v.down i
    rw [h i, MonoidHom.mul_apply, Units.val_mul, mul_assoc])
  comm_monodromy := by
    apply LinearMap.ext
    intro v
    rfl

/-- The class of the twisted diagonal pair is the class of the diagonal pair of `χ η_i`. -/
theorem twistClass_diagonalWD (χ : G →* ℂˣ) (η η' : Fin n → G →* ℂˣ)
    (h : ∀ i, η' i = χ * η i) :
    WeilDeligneRepresentation.twistClass χ
        (WeilDeligneRepresentation.classOf (diagonalWD.{uG, uV} ν η)) =
      WeilDeligneRepresentation.classOf (diagonalWD.{uG, uV} ν η') :=
  (WeilDeligneRepresentation.classOf_eq_iff _ _).mpr ⟨twistDiagonalWDEquiv ν χ η η' h⟩

end WeilDeligne

section Local

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p) (e : ReciprocityCandidate K)

/-- Pulling back quasi-characters along `e` is multiplicative. -/
theorem weilCharacter_mul (χ η : QuasiCharacter K) :
    weilCharacter K e (χ * η) = weilCharacter K e χ * weilCharacter K e η := by
  ext w
  rfl

/-- Pulling back quasi-characters along `e` commutes with finite products. -/
theorem weilCharacter_prod {n : ℕ} (μ : Fin n → QuasiCharacter K) :
    weilCharacter K e (∏ i, μ i) = ∏ i, weilCharacter K e (μ i) := by
  classical
  have key : ∀ s : Finset (Fin n),
      weilCharacter K e (∏ i ∈ s, μ i) = ∏ i ∈ s, weilCharacter K e (μ i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      ext w
      rfl
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj, weilCharacter_mul, ih]
  exact key Finset.univ

/-- The diagonal local Weil–Deligne pair attached to quasi-characters `μ_i` of `K^×`,
pulled back to the local Weil group along `e`. -/
def localDiagonal {n : ℕ} (μ : Fin n → QuasiCharacter K) :
    Weil.Local.LocalWeilDeligneRepresentation.{u, uV} K :=
  diagonalWD.{u, uV} (Weil.Local.localNormCharacter K).toMonoidHom
    (fun i => weilCharacter K e (μ i))

/-- The diagonal local pair has rank `r + 1`, zero monodromy, continuous Weil action,
determinant `(∏ μ_i) ∘ e`, and in the standard basis every Weil element acts by the
diagonal matrix with entries `μ_i ∘ e`. -/
theorem localDiagonal_spec {r : ℕ} (μ : Fin (r + 1) → QuasiCharacter K) :
    (localDiagonal.{u, uV} K e μ).rank = r + 1 ∧ (localDiagonal.{u, uV} K e μ).monodromy = 0 ∧
      (localDiagonal.{u, uV} K e μ).toFiniteRepresentation.IsContinuous ∧
      FiniteRepresentation.determinantCharacter
          (localDiagonal.{u, uV} K e μ).toFiniteRepresentation =
        weilCharacter K e (∏ i, μ i) ∧
      ∃ (b : Module.Basis (Fin (r + 1)) ℂ (localDiagonal.{u, uV} K e μ))
        (σ : Equiv.Perm (Fin (r + 1))),
        ∀ g : Weil.Local.localWeilGroup K,
          (∀ i j : Fin (r + 1), j < i →
              b.repr ((localDiagonal.{u, uV} K e μ).representation g (b j)) i = 0) ∧
            ∀ i : Fin (r + 1), b.repr ((localDiagonal.{u, uV} K e μ).representation g (b i)) i =
              ((weilCharacter K e (μ (σ i)) g : ℂˣ) : ℂ) := by
  refine ⟨diagonalFinite_rank _, rfl, ?_, ?_, diagonalBasis.{uV} (r + 1), 1, fun g => ⟨?_, ?_⟩⟩
  · exact diagonalFinite_isContinuous.{u, uV}
      (fun i => LocalFactor.RankOne.weilCharacter K e (μ i))
  · rw [weilCharacter_prod]
    exact diagonalFinite_determinantCharacter _
  · intro i j hji
    exact (diagonalBasis_repr_apply _ g i j).trans (ite_eq_right (ne_of_gt hji))
  · intro i
    exact (diagonalBasis_repr_apply _ g i i).trans (ite_eq_left rfl)

/-- Twisting the diagonal local pair by `χ ∘ e` gives the diagonal local pair of `μ_i χ`. -/
theorem twistClass_localDiagonal {n : ℕ} (χ : QuasiCharacter K)
    (μ : Fin n → QuasiCharacter K) :
    WeilDeligneRepresentation.twistClass (weilCharacter K e χ)
        (WeilDeligneRepresentation.classOf (localDiagonal.{u, uV} K e μ)) =
      WeilDeligneRepresentation.classOf (localDiagonal.{u, uV} K e (fun i => μ i * χ)) :=
  twistClass_diagonalWD _ _ _ _ (fun i => by
    ext w
    rw [weilCharacter_mul, MonoidHom.mul_apply, MonoidHom.mul_apply, mul_comm])

end Local

end Langlands.Automorphic.StableTwist
