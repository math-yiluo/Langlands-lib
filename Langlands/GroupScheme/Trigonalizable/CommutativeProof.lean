import Langlands.GroupScheme.Trigonalizable.CommutativeStatement
import Langlands.GroupScheme.MatrixRepresentation.AffineCoefficientAlgebra
import Langlands.GroupScheme.MatrixRepresentation.NormalFixedCoordinates
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! # Commutative groups over algebraically closed fields are trigonalizable (Milne 16.14) -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace AlgClosedCommutativeTrigonalizable

section LinearAlgebra

variable {k V : Type*} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- A pairwise commuting family of endomorphisms has a common eigenvector in every nonzero
subspace that it preserves. The proof is strong induction on the dimension of the subspace. -/
theorem exists_common_eigenvector_of_le (S : Set (Module.End k V))
    (hS : ∀ f ∈ S, ∀ g ∈ S, f * g = g * f) :
    ∀ (d : ℕ) (W : Submodule k V), Module.finrank k W = d → W ≠ ⊥ →
      (∀ f ∈ S, ∀ w ∈ W, f w ∈ W) →
        ∃ w ∈ W, w ≠ 0 ∧ ∀ f ∈ S, ∃ t : k, f w = t • w := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro W hd hW hWS
  by_cases hsc : ∀ f ∈ S, ∃ t : k, ∀ w ∈ W, f w = t • w
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact ⟨w, hw, hw0, fun f hf => (hsc f hf).imp fun t ht => ht w hw⟩
  · push Not at hsc
    obtain ⟨f, hf, hnot⟩ := hsc
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
    obtain ⟨t, ht⟩ := Module.End.exists_eigenvalue (f.restrict fun w hw => hWS f hf w hw)
    obtain ⟨w₀, hw₀⟩ := ht.exists_hasEigenvector
    let W' : Submodule k V := W ⊓ LinearMap.ker (f - t • 1)
    have hmem : ∀ w, w ∈ W' ↔ w ∈ W ∧ f w = t • w := by
      intro w
      simp only [W', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    have hw₀' : (w₀ : V) ∈ W' := by
      rw [hmem]
      exact ⟨w₀.2, congrArg Subtype.val hw₀.apply_eq_smul⟩
    have hW'ne : W' ≠ ⊥ := by
      intro hbot
      rw [hbot, Submodule.mem_bot] at hw₀'
      exact hw₀.2 (Subtype.ext hw₀')
    have hW'lt : W' < W := by
      refine lt_of_le_of_ne inf_le_left fun heq => ?_
      obtain ⟨w, hw, hfw⟩ := hnot t
      exact hfw ((hmem w).1 (heq.ge hw)).2
    have hW'S : ∀ g ∈ S, ∀ w ∈ W', g w ∈ W' := by
      intro g hg w hw
      rw [hmem] at hw ⊢
      refine ⟨hWS g hg w hw.1, ?_⟩
      have hc := congrArg (fun F : Module.End k V => F w) (hS f hf g hg)
      simp only [Module.End.mul_apply] at hc
      rw [hc, hw.2, map_smul]
    obtain ⟨w, hw, hw0, hall⟩ := ih (Module.finrank k W')
      (hd ▸ Submodule.finrank_lt_finrank_of_lt hW'lt) W' rfl hW'ne hW'S
    exact ⟨w, ((hmem w).1 hw).1, hw0, hall⟩

/-- A pairwise commuting family of endomorphisms of a nonzero finite-dimensional space over an
algebraically closed field has a common eigenvector. -/
theorem exists_common_eigenvector [Nontrivial V] (S : Set (Module.End k V))
    (hS : ∀ f ∈ S, ∀ g ∈ S, f * g = g * f) :
    ∃ v : V, v ≠ 0 ∧ ∀ f ∈ S, ∃ t : k, f v = t • v := by
  obtain ⟨w, -, hw0, hall⟩ := exists_common_eigenvector_of_le S hS _ ⊤ rfl top_ne_bot
    (fun _ _ _ _ => Submodule.mem_top)
  exact ⟨w, hw0, hall⟩

end LinearAlgebra

section StableLine

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]

/-- If the matrix of one affine model point multiplies the coordinate vector `v` by an element
of the model algebra, then `v` spans a stable line on every scheme test. -/
theorem isStableLine_of_affine_model (ρ : MatrixRepresentation G n)
    {A : CommAlgCat.{u} R} (j : (algSpec R).obj (op A) ≅ G.X) (v : n → R) (c : A)
    (h : (ρ.affineMatrix A j.hom : Matrix n n A) *ᵥ (fun i => algebraMap R A (v i)) =
      c • fun i => algebraMap R A (v i)) :
    ρ.IsStableLine v := by
  intro T x
  let e := Corepresented.affineSectionsAlgEquiv A
  let c' : Γ(((algSpec R).obj (op A)).left, ⊤) := e.symm c
  have h' : ∀ i, ((ρ.pointMatrix ((algSpec R).obj (op A)) j.hom :
      Matrix n n Γ(((algSpec R).obj (op A)).left, ⊤)) *ᵥ
      (fun i => scalarMap ((algSpec R).obj (op A)) (v i))) i =
      c' * scalarMap ((algSpec R).obj (op A)) (v i) := by
    intro i
    rw [MatrixRepresentation.pointMatrix_eq_affineMatrix]
    simp only [UnipotentMatrixCriterion.scalarMap_affine]
    have hi := congrArg e.symm (congrFun h i)
    rw [Pi.smul_apply, smul_eq_mul, map_mul] at hi
    exact ((e.symm.toRingHom.map_mulVec _ _ i).symm).trans hi
  have hmat := ρ.pointMatrix_naturality (x ≫ j.inv) j.hom
  simp only [Category.assoc, j.inv_hom_id, Category.comp_id] at hmat
  refine ⟨(x ≫ j.inv).left.appTop.hom c', ?_⟩
  rw [hmat]
  funext i
  have hi := congrArg (x ≫ j.inv).left.appTop.hom (h' i)
  rw [(x ≫ j.inv).left.appTop.hom.map_mulVec, map_mul] at hi
  change (((ρ.pointMatrix ((algSpec R).obj (op A)) j.hom :
    Matrix n n Γ(((algSpec R).obj (op A)).left, ⊤)).map (x ≫ j.inv).left.appTop.hom) *ᵥ
      (fun i => scalarMap T (v i))) i =
    (x ≫ j.inv).left.appTop.hom c' * scalarMap T (v i)
  simpa only [Function.comp_def, scalarMap_naturality] using hi

end StableLine

section Coefficients

open MatrixRepresentation AffineCoefficients

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation G n)

/-- For a commutative group scheme, any two universal coefficient matrices commute. The two
pullbacks of the universal point to `O(G) ⊗ O(G)` commute, and the product functional
`a ⊗ b ↦ ℓ(a) m(b)` turns that identity into the matrix identity. -/
theorem coefficientMap_mul_comm [IsCommMonObj G.X] (ℓ m : CharacterUnits.Coord G →ₗ[k] k) :
    coefficientMap ρ ℓ * coefficientMap ρ m = coefficientMap ρ m * coefficientMap ρ ℓ := by
  let B := CharacterUnits.Coord G
  let D := CommAlgCat.of (CommRingCat.of k) (B ⊗[k] B)
  let a : B ⟶ D := CommAlgCat.ofHom Algebra.TensorProduct.includeLeft
  let b : B ⟶ D := CommAlgCat.ofHom Algebra.TensorProduct.includeRight
  let U := CharacterUnits.universalPoint G
  let x := (algSpec (CommRingCat.of k)).map a.op ≫ U
  let y := (algSpec (CommRingCat.of k)).map b.op ≫ U
  have hxy : x * y = y * x := mul_comm x y
  have hM : ρ.affineMatrix D (x * y) = ρ.affineMatrix D (y * x) := by rw [hxy]
  rw [map_mul, map_mul, ρ.affineMatrix_naturality a U, ρ.affineMatrix_naturality b U] at hM
  let Λ : D →ₗ[k] k := LinearMap.mul' k k ∘ₗ TensorProduct.map ℓ m
  have hΛ : ∀ p q : B, Λ (p ⊗ₜ q) = ℓ p * m q := fun p q => by
    dsimp only [Λ]
    rw [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply]
  let a' : B →+* D := (CommAlgCat.Hom.hom a).toRingHom
  let b' : B →+* D := (CommAlgCat.Hom.hom b).toRingHom
  have hab : ∀ p q : B, Λ (a' p * b' q) = ℓ p * m q := fun p q => by
    change Λ ((p ⊗ₜ[k] (1 : B)) * ((1 : B) ⊗ₜ[k] q)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, hΛ]
  have hba : ∀ p q : B, Λ (b' p * a' q) = m p * ℓ q := fun p q => by
    change Λ (((1 : B) ⊗ₜ[k] p) * (q ⊗ₜ[k] (1 : B))) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, hΛ, mul_comm]
  let M : Matrix n n B := ρ.universalCharacterMatrix
  have hMmat : M.map a' * M.map b' = M.map b' * M.map a' := congrArg Units.val hM
  ext i j
  change ∑ l, ℓ (M i l) * m (M l j) = ∑ l, m (M i l) * ℓ (M l j)
  calc ∑ l, ℓ (M i l) * m (M l j) = ∑ l, Λ (a' (M i l) * b' (M l j)) :=
        Finset.sum_congr rfl fun l _ => (hab _ _).symm
    _ = Λ ((M.map a' * M.map b') i j) := by
        rw [Matrix.mul_apply, map_sum]
        rfl
    _ = Λ ((M.map b' * M.map a') i j) := by rw [hMmat]
    _ = ∑ l, Λ (b' (M i l) * a' (M l j)) := by
        rw [Matrix.mul_apply, map_sum]
        rfl
    _ = ∑ l, m (M i l) * ℓ (M l j) := Finset.sum_congr rfl fun l _ => hba _ _

/-- A common eigenvector of all universal coefficient matrices is multiplied by an element of
the coordinate algebra at the universal point. -/
theorem exists_universal_smul (v : n → k) (hv : v ≠ 0)
    (ht : ∀ ℓ, ∃ t : k, coefficientMap ρ ℓ *ᵥ v = t • v) :
    ∃ c : CharacterUnits.Coord G,
      ρ.universalCharacterMatrix *ᵥ (fun i => algebraMap k (CharacterUnits.Coord G) (v i)) =
        c • (fun i => algebraMap k (CharacterUnits.Coord G) (v i)) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  set w := ρ.universalCharacterMatrix *ᵥ
    (fun i => algebraMap k (CharacterUnits.Coord G) (v i)) with hw_def
  refine ⟨(v i₀)⁻¹ • w i₀, ?_⟩
  funext i
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff k _).mp
  intro ℓ
  obtain ⟨t, htℓ⟩ := ht ℓ
  have hw : ∀ r, ℓ (w r) = t * v r := fun r => by
    have := congrFun (coefficientMap_mulVec ρ ℓ v) r
    rw [htℓ] at this
    exact this.symm
  have hs : ((v i₀)⁻¹ • w i₀) * algebraMap k (CharacterUnits.Coord G) (v i) =
      (v i * (v i₀)⁻¹) • w i₀ := by
    rw [mul_comm, ← Algebra.smul_def, smul_smul]
  rw [Pi.smul_apply, smul_eq_mul, hs, map_sub, map_smul, hw, hw, smul_eq_mul]
  field_simp
  ring

end Coefficients

end AlgClosedCommutativeTrigonalizable

open AlgClosedCommutativeTrigonalizable MatrixRepresentation AffineCoefficients in
/-- Milne 2017, Corollary 16.14: every commutative affine algebraic group over an algebraically
closed field is trigonalizable. -/
theorem algClosedCommutativeTrigonalizable :
    AlgClosedCommutativeTrigonalizableStatement.{u} := by
  intro k _ _ G _ _ _ n _ _ _ ρ
  let S : Set (Module.End k (n → k)) :=
    Set.range fun ℓ => (coefficientMap ρ ℓ).mulVecLin
  have hS : ∀ f ∈ S, ∀ g ∈ S, f * g = g * f := by
    rintro _ ⟨ℓ, rfl⟩ _ ⟨m, rfl⟩
    change (coefficientMap ρ ℓ).mulVecLin ∘ₗ (coefficientMap ρ m).mulVecLin =
      (coefficientMap ρ m).mulVecLin ∘ₗ (coefficientMap ρ ℓ).mulVecLin
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, coefficientMap_mul_comm]
  obtain ⟨v, hv, ht⟩ := exists_common_eigenvector S hS
  have ht' : ∀ ℓ, ∃ t : k, coefficientMap ρ ℓ *ᵥ v = t • v := fun ℓ => ht _ ⟨ℓ, rfl⟩
  obtain ⟨c, hc⟩ := exists_universal_smul ρ v hv ht'
  refine ⟨v, hv, isStableLine_of_affine_model ρ (Lie.coordinateIso G) v c ?_⟩
  rw [← CharacterUnits.universalPoint_eq]
  exact hc

end Langlands.GroupScheme
