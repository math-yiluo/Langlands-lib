import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.GroupScheme.MatrixRepresentation.DenseRationalStability
import Langlands.GroupScheme.MatrixRepresentation.DirectSum
import Langlands.GroupScheme.MatrixRepresentation.SemisimpleDirectSum
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Actual representations as modules over the free algebra of coefficient operators -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]

/-- The index set of coefficient operators of representations of `G`: an affine test
algebra `A`, a point of `G` with coefficients in `A`, and a `k`-linear functional on `A`. -/
def OperatorIndex (G : GroupScheme (Spec (CommRingCat.of k))) : Type (u + 1) :=
  Σ A : CommAlgCat.{u} (CommRingCat.of k),
    ((algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X) × (A →ₗ[k] k)

/-- The free `k`-algebra on the coefficient operators of representations of `G`. -/
abbrev OperatorAlgebra (G : GroupScheme (Spec (CommRingCat.of k))) :=
  FreeAlgebra k (OperatorIndex G)

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Scalar extension of a coordinate vector to a test algebra. -/
def scalarVector (A : CommAlgCat.{u} (CommRingCat.of k)) : (n → k) →ₗ[k] (n → A) where
  toFun v := fun r => algebraMap k A (v r)
  map_add' v w := by ext r; exact map_add _ _ _
  map_smul' c v := by
    ext r
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, map_mul, Algebra.smul_def]

/-- The coefficient operator `v ↦ ℓ(ρ(x) v)` attached to `ξ = (A, x, ℓ)`. -/
def coefficientOperator (ρ : MatrixRepresentation G n) (ξ : OperatorIndex G) :
    (n → k) →ₗ[k] (n → k) where
  toFun v := fun i => ξ.2.2 (((ρ.affineMatrix ξ.1 ξ.2.1 : Matrix n n ξ.1) *ᵥ
    scalarVector ξ.1 v) i)
  map_add' v w := by
    ext i
    simp only [map_add, Matrix.mulVec_add, Pi.add_apply]
  map_smul' c v := by
    ext i
    simp only [map_smul, Matrix.mulVec_smul, Pi.smul_apply, RingHom.id_apply]

theorem coefficientOperator_apply (ρ : MatrixRepresentation G n) (ξ : OperatorIndex G)
    (v : n → k) :
    coefficientOperator ρ ξ v = fun i => ξ.2.2 (((ρ.affineMatrix ξ.1 ξ.2.1 :
      Matrix n n ξ.1) *ᵥ (fun j => algebraMap k ξ.1 (v j))) i) := rfl

/-- The action of the operator algebra on the coordinate space of `ρ`. -/
def operatorAction (ρ : MatrixRepresentation G n) :
    OperatorAlgebra G →ₐ[k] Module.End k (n → k) :=
  FreeAlgebra.lift k (coefficientOperator ρ)

@[simp] theorem operatorAction_ι (ρ : MatrixRepresentation G n) (ξ : OperatorIndex G) :
    operatorAction ρ (FreeAlgebra.ι k ξ) = coefficientOperator ρ ξ :=
  FreeAlgebra.lift_ι_apply _ _

/-- The coordinate space of `ρ`, regarded as a module over the operator algebra. -/
@[nolint unusedArguments]
def OperatorModule (_ρ : MatrixRepresentation G n) : Type u := n → k

variable (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)

instance : AddCommGroup (OperatorModule ρ) := inferInstanceAs (AddCommGroup (n → k))

instance : Module k (OperatorModule ρ) := inferInstanceAs (Module k (n → k))

instance : FiniteDimensional k (OperatorModule ρ) :=
  inferInstanceAs (FiniteDimensional k (n → k))

instance : Module (OperatorAlgebra G) (OperatorModule ρ) where
  smul r v := operatorAction ρ r v
  one_smul v := by
    change operatorAction ρ 1 v = v
    rw [map_one]
    rfl
  mul_smul r s v := by
    change operatorAction ρ (r * s) v = operatorAction ρ r (operatorAction ρ s v)
    rw [map_mul]
    rfl
  smul_zero r := map_zero (operatorAction ρ r)
  smul_add r v w := map_add (operatorAction ρ r) v w
  add_smul r s v := by
    change operatorAction ρ (r + s) v = operatorAction ρ r v + operatorAction ρ s v
    rw [map_add]
    rfl
  zero_smul v := by
    change operatorAction ρ 0 v = 0
    rw [map_zero]
    rfl

/-- The identification of the coordinate space of `ρ` with its module of coefficient
operators. -/
def toModule : (n → k) ≃ₗ[k] OperatorModule ρ := LinearEquiv.refl k (n → k)

theorem smul_toModule (r : OperatorAlgebra G) (v : n → k) :
    r • toModule ρ v = toModule ρ (operatorAction ρ r v) := rfl

theorem ι_smul_toModule (ξ : OperatorIndex G) (v : n → k) :
    FreeAlgebra.ι k ξ • toModule ρ v = toModule ρ (coefficientOperator ρ ξ v) := by
  rw [smul_toModule, operatorAction_ι]

instance : IsScalarTower k (OperatorAlgebra G) (OperatorModule ρ) where
  smul_assoc c r v := by
    change operatorAction ρ (c • r) v = c • operatorAction ρ r v
    rw [map_smul]
    rfl

/-! ### Stable subspaces are submodules -/

variable {ρ σ}

/-- A subspace is stable exactly when it is preserved by every coefficient operator. -/
theorem isStableSubspace_iff_coefficientOperator (V : Submodule k (n → k)) :
    ρ.IsStableSubspace V ↔ ∀ ξ v, v ∈ V → coefficientOperator ρ ξ v ∈ V := by
  constructor
  · intro h ξ v hv
    exact h ξ.1 ξ.2.1 v hv ξ.2.2
  · intro h A x v hv ℓ
    exact h ⟨A, x, ℓ⟩ v hv

theorem IsStableSubspace.operatorAction_mem {V : Submodule k (n → k)}
    (hV : ρ.IsStableSubspace V) (r : OperatorAlgebra G) {v : n → k} (hv : v ∈ V) :
    operatorAction ρ r v ∈ V := by
  induction r using FreeAlgebra.induction generalizing v with
  | grade0 c =>
    rw [AlgHom.commutes, Module.algebraMap_end_apply]
    exact V.smul_mem c hv
  | grade1 ξ =>
    rw [operatorAction_ι]
    exact (isStableSubspace_iff_coefficientOperator V).mp hV ξ v hv
  | mul a b ha hb =>
    rw [map_mul, Module.End.mul_apply]
    exact ha (hb hv)
  | add a b ha hb =>
    rw [map_add, LinearMap.add_apply]
    exact V.add_mem (ha hv) (hb hv)

/-- The submodule over the operator algebra carried by a stable subspace. -/
def IsStableSubspace.toSubmodule {V : Submodule k (n → k)} (hV : ρ.IsStableSubspace V) :
    Submodule (OperatorAlgebra G) (OperatorModule ρ) where
  carrier := {w | (toModule ρ).symm w ∈ V}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    exact V.add_mem ha hb
  zero_mem' := by simp
  smul_mem' r w hw := by
    obtain ⟨v, rfl⟩ := (toModule ρ).surjective w
    simp only [Set.mem_ofPred_eq, LinearEquiv.symm_apply_apply, smul_toModule] at hw ⊢
    exact hV.operatorAction_mem r hw

theorem IsStableSubspace.toModule_mem_toSubmodule {V : Submodule k (n → k)}
    (hV : ρ.IsStableSubspace V) (v : n → k) :
    toModule ρ v ∈ hV.toSubmodule ↔ v ∈ V := by
  change (toModule ρ).symm (toModule ρ v) ∈ V ↔ v ∈ V
  rw [LinearEquiv.symm_apply_apply]

/-- The coordinate subspace underlying a submodule over the operator algebra. -/
def coordinateSubspace (S : Submodule (OperatorAlgebra G) (OperatorModule ρ)) :
    Submodule k (n → k) :=
  (S.restrictScalars k).comap (toModule ρ).toLinearMap

theorem mem_coordinateSubspace (S : Submodule (OperatorAlgebra G) (OperatorModule ρ))
    (v : n → k) : v ∈ coordinateSubspace S ↔ toModule ρ v ∈ S := Iff.rfl

theorem isStableSubspace_coordinateSubspace
    (S : Submodule (OperatorAlgebra G) (OperatorModule ρ)) :
    ρ.IsStableSubspace (coordinateSubspace S) := by
  rw [isStableSubspace_iff_coefficientOperator]
  intro ξ v hv
  rw [mem_coordinateSubspace] at hv ⊢
  rw [← ι_smul_toModule]
  exact S.smul_mem _ hv

theorem coordinateSubspace_toSubmodule {V : Submodule k (n → k)}
    (hV : ρ.IsStableSubspace V) : coordinateSubspace hV.toSubmodule = V := by
  ext v
  rw [mem_coordinateSubspace, hV.toModule_mem_toSubmodule]

theorem toSubmodule_coordinateSubspace
    (S : Submodule (OperatorAlgebra G) (OperatorModule ρ)) :
    (isStableSubspace_coordinateSubspace S).toSubmodule = S := by
  ext w
  obtain ⟨v, rfl⟩ := (toModule ρ).surjective w
  rw [IsStableSubspace.toModule_mem_toSubmodule, mem_coordinateSubspace]

/-! ### Intertwiners are module maps -/

/-- A linear map commuting with every coefficient operator commutes with the whole
operator algebra. -/
theorem operatorAction_comm_of_coefficientOperator (f : (n → k) →ₗ[k] (m → k))
    (hf : ∀ ξ v, f (coefficientOperator ρ ξ v) = coefficientOperator σ ξ (f v))
    (r : OperatorAlgebra G) (v : n → k) :
    f (operatorAction ρ r v) = operatorAction σ r (f v) := by
  induction r using FreeAlgebra.induction generalizing v with
  | grade0 c =>
    rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul]
  | grade1 ξ =>
    rw [operatorAction_ι, operatorAction_ι]
    exact hf ξ v
  | mul a b ha hb =>
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, ha, hb]

/-- The module map attached to a linear map commuting with every coefficient operator. -/
def moduleMapOfComm (f : (n → k) →ₗ[k] (m → k))
    (hf : ∀ ξ v, f (coefficientOperator ρ ξ v) = coefficientOperator σ ξ (f v)) :
    OperatorModule ρ →ₗ[OperatorAlgebra G] OperatorModule σ where
  toFun w := toModule σ (f ((toModule ρ).symm w))
  map_add' v w := by simp only [map_add]
  map_smul' r w := by
    obtain ⟨v, rfl⟩ := (toModule ρ).surjective w
    simp only [smul_toModule, LinearEquiv.symm_apply_apply, RingHom.id_apply]
    rw [operatorAction_comm_of_coefficientOperator f hf r v]

theorem moduleMapOfComm_toModule (f : (n → k) →ₗ[k] (m → k))
    (hf : ∀ ξ v, f (coefficientOperator ρ ξ v) = coefficientOperator σ ξ (f v))
    (v : n → k) : moduleMapOfComm f hf (toModule ρ v) = toModule σ (f v) := by
  change toModule σ (f ((toModule ρ).symm (toModule ρ v))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The underlying coordinate linear map of a module map. -/
def coordinateMap (f : OperatorModule ρ →ₗ[OperatorAlgebra G] OperatorModule σ) :
    (n → k) →ₗ[k] (m → k) :=
  (toModule σ).symm.toLinearMap ∘ₗ (f.restrictScalars k) ∘ₗ (toModule ρ).toLinearMap

theorem toModule_coordinateMap
    (f : OperatorModule ρ →ₗ[OperatorAlgebra G] OperatorModule σ) (v : n → k) :
    toModule σ (coordinateMap f v) = f (toModule ρ v) := by
  change toModule σ ((toModule σ).symm (f (toModule ρ v))) = _
  rw [LinearEquiv.apply_symm_apply]

theorem coordinateMap_comm (f : OperatorModule ρ →ₗ[OperatorAlgebra G] OperatorModule σ)
    (ξ : OperatorIndex G) (v : n → k) :
    coordinateMap f (coefficientOperator ρ ξ v) =
      coefficientOperator σ ξ (coordinateMap f v) := by
  apply (toModule σ).injective
  rw [toModule_coordinateMap, ← ι_smul_toModule, f.map_smul, ← toModule_coordinateMap,
    ι_smul_toModule]

omit [Fintype m] [DecidableEq m] in
/-- Vectors over a test algebra are determined by their images under all
`k`-linear functionals. -/
theorem vector_ext_of_functionals {A : CommAlgCat.{u} (CommRingCat.of k)} {a b : m → A}
    (h : ∀ ℓ : A →ₗ[k] k, (fun i => ℓ (a i)) = fun i => ℓ (b i)) : a = b := by
  funext i
  rw [← sub_eq_zero]
  apply (Module.forall_dual_apply_eq_zero_iff k (a i - b i)).mp
  intro ℓ
  rw [map_sub, sub_eq_zero]
  exact congrFun (h ℓ) i

/-- A constant matrix intertwines exactly when it commutes with every coefficient
operator. -/
theorem intertwines_iff_coefficientOperator (C : Matrix m n k) :
    Intertwines ρ σ C ↔ ∀ ξ v, C *ᵥ coefficientOperator ρ ξ v =
      coefficientOperator σ ξ (C *ᵥ v) := by
  constructor
  · intro hC ξ v
    exact hC.linearFunctional_mulVec ξ.1 ξ.2.1 v ξ.2.2
  · intro h A x
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hs : (Pi.single j (1 : A) : n → A) = fun l => algebraMap k A
        ((Pi.single j (1 : k) : n → k) l) := by
      funext l
      by_cases hl : l = j
      · subst hl; simp
      · simp [hl]
    rw [hs]
    have hv : C.map (algebraMap k A) *ᵥ
        (fun l => algebraMap k A ((Pi.single j (1 : k) : n → k) l)) =
        (fun l => algebraMap k A ((C *ᵥ Pi.single j 1) l)) := by
      funext i
      exact ((algebraMap k A).map_mulVec C _ i).symm
    rw [hv]
    apply vector_ext_of_functionals
    intro ℓ
    rw [linearFunctional_mulVec_rectangular]
    exact h ⟨A, x, ℓ⟩ (Pi.single j 1)

/-- The module map of an intertwining matrix. -/
def Intertwines.toModuleMap {C : Matrix m n k} (hC : Intertwines ρ σ C) :
    OperatorModule ρ →ₗ[OperatorAlgebra G] OperatorModule σ :=
  moduleMapOfComm C.mulVecLin
    ((intertwines_iff_coefficientOperator C).mp hC)

theorem Intertwines.toModuleMap_toModule {C : Matrix m n k} (hC : Intertwines ρ σ C)
    (v : n → k) : hC.toModuleMap (toModule ρ v) = toModule σ (C *ᵥ v) :=
  moduleMapOfComm_toModule _ _ v

theorem coordinateMap_toModuleMap {C : Matrix m n k} (hC : Intertwines ρ σ C) :
    coordinateMap hC.toModuleMap = C.mulVecLin := by
  refine LinearMap.ext fun v => ?_
  apply (toModule σ).injective
  rw [toModule_coordinateMap, hC.toModuleMap_toModule]
  rfl

/-- The matrix of a module map intertwines. -/
theorem intertwines_toMatrix' (f : OperatorModule ρ →ₗ[OperatorAlgebra G] OperatorModule σ) :
    Intertwines ρ σ (LinearMap.toMatrix' (coordinateMap f)) := by
  rw [intertwines_iff_coefficientOperator]
  intro ξ v
  rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  exact coordinateMap_comm f ξ v

/-- An isomorphism of modules over the operator algebra gives a bijective intertwining
matrix. -/
theorem exists_intertwines_bijective_of_linearEquiv
    (e : OperatorModule ρ ≃ₗ[OperatorAlgebra G] OperatorModule σ) :
    ∃ C : Matrix m n k, Intertwines ρ σ C ∧ Function.Bijective C.mulVecLin := by
  refine ⟨LinearMap.toMatrix' (coordinateMap e.toLinearMap),
    intertwines_toMatrix' e.toLinearMap, ?_⟩
  have h : (LinearMap.toMatrix' (coordinateMap e.toLinearMap)).mulVecLin =
      coordinateMap e.toLinearMap :=
    LinearMap.ext fun v => LinearMap.toMatrix'_mulVec _ v
  rw [h]
  exact ((toModule σ).symm.bijective.comp e.bijective).comp (toModule ρ).bijective

/-- A bijective intertwining matrix gives an isomorphism of modules. -/
def Intertwines.toLinearEquiv {C : Matrix m n k} (hC : Intertwines ρ σ C)
    (hb : Function.Bijective C.mulVecLin) :
    OperatorModule ρ ≃ₗ[OperatorAlgebra G] OperatorModule σ :=
  LinearEquiv.ofBijective hC.toModuleMap (by
    have h : (hC.toModuleMap : OperatorModule ρ → OperatorModule σ) =
        toModule σ ∘ C.mulVecLin ∘ (toModule ρ).symm := by
      funext w
      obtain ⟨v, rfl⟩ := (toModule ρ).surjective w
      simp only [Function.comp_apply, LinearEquiv.symm_apply_apply,
        hC.toModuleMap_toModule, Matrix.mulVecLin_apply]
    rw [h]
    exact ((toModule σ).bijective.comp hb).comp (toModule ρ).symm.bijective)

/-! ### Irreducibility and semisimplicity -/

theorem eq_bot_of_toSubmodule_eq_bot {V : Submodule k (n → k)} (hV : ρ.IsStableSubspace V)
    (h : hV.toSubmodule = ⊥) : V = ⊥ := by
  rw [← coordinateSubspace_toSubmodule hV, h, eq_bot_iff]
  intro v hv
  rw [mem_coordinateSubspace, Submodule.mem_bot] at hv
  rw [Submodule.mem_bot]
  exact (toModule ρ).map_eq_zero_iff.mp hv

theorem eq_top_of_toSubmodule_eq_top {V : Submodule k (n → k)} (hV : ρ.IsStableSubspace V)
    (h : hV.toSubmodule = ⊤) : V = ⊤ := by
  rw [← coordinateSubspace_toSubmodule hV, h, eq_top_iff]
  intro v _
  rw [mem_coordinateSubspace]
  exact Submodule.mem_top

theorem eq_bot_of_coordinateSubspace_eq_bot
    (S : Submodule (OperatorAlgebra G) (OperatorModule ρ)) (h : coordinateSubspace S = ⊥) :
    S = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨v, rfl⟩ := (toModule ρ).surjective w
  rw [← mem_coordinateSubspace, h, Submodule.mem_bot] at hw
  rw [hw, map_zero]
  exact Submodule.zero_mem _

/-- A simple module of coefficient operators is an irreducible representation. -/
theorem isIrreducible_of_isSimpleModule
    [IsSimpleModule (OperatorAlgebra G) (OperatorModule ρ)] : ρ.IsIrreducible := by
  refine ⟨?_, ?_⟩
  · have := IsSimpleModule.nontrivial (OperatorAlgebra G) (OperatorModule ρ)
    exact (toModule ρ).toEquiv.nontrivial
  intro V hV
  rcases IsSimpleOrder.eq_bot_or_eq_top hV.toSubmodule with h | h
  · exact Or.inl (eq_bot_of_toSubmodule_eq_bot hV h)
  · exact Or.inr (eq_top_of_toSubmodule_eq_top hV h)

/-- Semisimplicity in the sense of the character statement (the simple stable subspaces
span) gives semisimplicity of the module of coefficient operators. -/
theorem isSemisimpleModule_of_sSup_eq_top
    (h : sSup {W : Submodule k (n → k) | ρ.IsStableSubspace W ∧
      W ≠ ⊥ ∧ ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W →
        U = ⊥ ∨ U = W} = ⊤) :
    IsSemisimpleModule (OperatorAlgebra G) (OperatorModule ρ) := by
  apply IsSemisimpleModule.of_sSup_simples_eq_top
  let K := sSup {S : Submodule (OperatorAlgebra G) (OperatorModule ρ) |
    IsSimpleModule (OperatorAlgebra G) S}
  have hle : sSup {W : Submodule k (n → k) | ρ.IsStableSubspace W ∧
      W ≠ ⊥ ∧ ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W →
        U = ⊥ ∨ U = W} ≤ coordinateSubspace K := by
    apply sSup_le
    rintro W ⟨hW, hne, hmin⟩
    have hsimple : IsSimpleModule (OperatorAlgebra G) hW.toSubmodule := by
      rw [isSimpleModule_iff_isAtom]
      refine ⟨fun hbot => hne (eq_bot_of_toSubmodule_eq_bot hW hbot), ?_⟩
      intro S hS
      have hSW : coordinateSubspace S ≤ W := by
        intro v hv
        rw [mem_coordinateSubspace] at hv
        exact (hW.toModule_mem_toSubmodule v).mp (hS.le hv)
      rcases hmin (coordinateSubspace S) (isStableSubspace_coordinateSubspace S) hSW
        with h0 | h1
      · exact eq_bot_of_coordinateSubspace_eq_bot S h0
      · exfalso
        apply hS.ne
        apply le_antisymm hS.le
        intro w hw
        obtain ⟨v, rfl⟩ := (toModule ρ).surjective w
        rw [← mem_coordinateSubspace, h1]
        exact (hW.toModule_mem_toSubmodule v).mp hw
    intro v hv
    rw [mem_coordinateSubspace]
    exact (le_sSup hsimple : hW.toSubmodule ≤ K) ((hW.toModule_mem_toSubmodule v).mpr hv)
  rw [h] at hle
  rw [eq_top_iff]
  intro w _
  obtain ⟨v, rfl⟩ := (toModule ρ).surjective w
  exact (mem_coordinateSubspace K v).mp (hle Submodule.mem_top)

/-! ### Coordinates on submodules -/

/-- Every submodule of coefficient operators is isomorphic to the module of a
representation in finite coordinates. -/
theorem exists_linearEquiv_submodule [IsAffineHom G.X.hom]
    (S : Submodule (OperatorAlgebra G) (OperatorModule ρ)) :
    ∃ (r : ℕ) (τ : MatrixRepresentation G (Fin r)),
      Nonempty (OperatorModule τ ≃ₗ[OperatorAlgebra G] S) := by
  let V := coordinateSubspace S
  have hV : ρ.IsStableSubspace V := isStableSubspace_coordinateSubspace S
  obtain ⟨r, B, P, hPB, hcols, hproj⟩ := exists_subspace_split_coordinates V
  have hstable := hV.isStableCoordinates B P hcols hproj
  let τ := restrictCoordinates ρ B P hPB hstable
  have hB : Intertwines τ ρ B := intertwines_restrictCoordinates ρ B P hPB hstable
  have hinj : Function.Injective hB.toModuleMap := by
    intro w w' hww'
    obtain ⟨v, rfl⟩ := (toModule τ).surjective w
    obtain ⟨v', rfl⟩ := (toModule τ).surjective w'
    rw [hB.toModuleMap_toModule, hB.toModuleMap_toModule] at hww'
    have h := congrArg (fun z : n → k => P *ᵥ z) ((toModule ρ).injective hww')
    simp only [Matrix.mulVec_mulVec, hPB, Matrix.one_mulVec] at h
    rw [h]
  have hrange : LinearMap.range hB.toModuleMap = S := by
    ext w
    obtain ⟨v, rfl⟩ := (toModule ρ).surjective w
    constructor
    · rintro ⟨w', hw'⟩
      obtain ⟨u, rfl⟩ := (toModule τ).surjective w'
      rw [hB.toModuleMap_toModule] at hw'
      rw [← hw', ← mem_coordinateSubspace]
      have hu : B *ᵥ u = ∑ j, u j • (fun a => B a j) := by
        funext a
        simp [Matrix.mulVec, dotProduct, mul_comm]
      rw [hu]
      exact V.sum_mem fun j _ => V.smul_mem _ (hcols j)
    · intro hv
      refine ⟨toModule τ (P *ᵥ v), ?_⟩
      rw [hB.toModuleMap_toModule, Matrix.mulVec_mulVec]
      rw [hproj v ((mem_coordinateSubspace S v).mpr hv)]
  exact ⟨r, τ, ⟨(LinearEquiv.ofInjective hB.toModuleMap hinj).trans
    (LinearEquiv.ofEq _ _ hrange)⟩⟩

/-! ### Direct sums -/

section DirectSum

variable {I : Type} [Fintype I] [DecidableEq I] {ν : I → Type} [∀ i, Fintype (ν i)]
  [∀ i, DecidableEq (ν i)] (τ : ∀ i, MatrixRepresentation G (ν i))

/-- The coordinate projection of a direct sum onto one block. -/
def blockProjection (i : I) : ((Σ i, ν i) → k) →ₗ[k] (ν i → k) where
  toFun v j := v ⟨i, j⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem blockProjection_coefficientOperator (i : I) (ξ : OperatorIndex G)
    (v : (Σ i, ν i) → k) :
    blockProjection i (coefficientOperator (directSum τ) ξ v) =
      coefficientOperator (τ i) ξ (blockProjection i v) := by
  funext j
  change ξ.2.2 _ = ξ.2.2 _
  rw [directSum_affineMatrix_val]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma, scalarVector, LinearMap.coe_mk,
    AddHom.coe_mk, blockProjection]
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro j' _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hb), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The projection of the module of a direct sum onto the module of one block. -/
def blockModuleMap (i : I) :
    OperatorModule (directSum τ) →ₗ[OperatorAlgebra G] OperatorModule (τ i) :=
  moduleMapOfComm (blockProjection i) (blockProjection_coefficientOperator τ i)

theorem blockModuleMap_toModule (i : I) (v : (Σ i, ν i) → k) :
    blockModuleMap τ i (toModule (directSum τ) v) =
      toModule (τ i) (fun j => v ⟨i, j⟩) :=
  moduleMapOfComm_toModule _ _ v

/-- The module of a direct sum is the product of the modules of its blocks. -/
def directSumModuleEquiv :
    OperatorModule (directSum τ) ≃ₗ[OperatorAlgebra G] ∀ i, OperatorModule (τ i) :=
  LinearEquiv.ofBijective (LinearMap.pi fun i => blockModuleMap τ i) (by
    constructor
    · intro w w' hww'
      obtain ⟨v, rfl⟩ := (toModule (directSum τ)).surjective w
      obtain ⟨v', rfl⟩ := (toModule (directSum τ)).surjective w'
      congr 1
      funext ij
      have h := congrFun hww' ij.1
      simp only [LinearMap.pi_apply, blockModuleMap_toModule] at h
      exact congrFun ((toModule (τ ij.1)).injective h) ij.2
    · intro w
      refine ⟨toModule (directSum τ) fun ij => (toModule (τ ij.1)).symm (w ij.1) ij.2, ?_⟩
      funext i
      simp only [LinearMap.pi_apply, blockModuleMap_toModule]
      apply (toModule (τ i)).symm.injective
      rw [LinearEquiv.symm_apply_apply])

end DirectSum

end Langlands.GroupScheme.MatrixRepresentation
