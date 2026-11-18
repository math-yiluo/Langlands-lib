import Langlands.GroupScheme.MatrixRepresentation.GaloisTwist
import Langlands.GroupScheme.MatrixRepresentation.AffineCoefficientAlgebra

/-! # Universal coefficients of representations of a scalar-extended group -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

section Naturality

variable {S S' : Type u} [CommRing S] [Algebra K S] [Algebra k S] [IsScalarTower k K S]
  [CommRing S'] [Algebra K S'] [Algebra k S'] [IsScalarTower k K S']

/-- Scalar-extension points are natural in the compatible test algebra. -/
theorem scalarExtensionPoint_naturality (f : S →ₐ[K] S')
    (y : G.affinePoints (CommAlgCat.of (CommRingCat.of k) S)) :
    (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom f).op ≫ scalarExtensionPoint S y =
      scalarExtensionPoint S'
        ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (f.restrictScalars k)).op ≫ y) := by
  apply (baseChangePointsEquiv (algebraBaseMap k K) G _).injective
  rw [baseChangePointsEquiv_naturality]
  simp only [scalarExtensionPoint, MulEquiv.apply_symm_apply]
  have h := CocharacterSplitting.testIso_hom_comp_map (k := k) K f
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ y) h.symm

/-- The point of `G` underlying a point of `G_K` over a compatible algebra. -/
def scalarBasePoint (x : ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).affinePoints
      (CommAlgCat.of (CommRingCat.of K) S)) :
    G.affinePoints (CommAlgCat.of (CommRingCat.of k) S) :=
  (CocharacterSplitting.testIso K S).inv ≫ baseChangePointsEquiv (algebraBaseMap k K) G _ x

theorem scalarExtensionPoint_scalarBasePoint
    (x : ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).affinePoints
      (CommAlgCat.of (CommRingCat.of K) S)) :
    scalarExtensionPoint S (scalarBasePoint x) = x := by
  apply (baseChangePointsEquiv (algebraBaseMap k K) G _).injective
  simp only [scalarExtensionPoint, scalarBasePoint, MulEquiv.apply_symm_apply,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end Naturality

section Universal

variable [IsAffineHom G.X.hom]

variable (K G) in
/-- The universal point of `G`, seen as a point of `G_K` over `K ⊗[k] O(G)`. -/
abbrev universalScalarPoint :
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).affinePoints
      (CommAlgCat.of (CommRingCat.of K) (K ⊗[k] CharacterUnits.Coord G)) :=
  scalarPoint (CharacterUnits.Coord G) (CharacterUnits.universalPoint G)

/-- The universal matrix of a representation of `G_K`, with entries in `K ⊗[k] O(G)`. -/
def universalMatrix
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n) :
    Matrix n n (K ⊗[k] CharacterUnits.Coord G) :=
  (ρ.affineMatrix _ (universalScalarPoint K G) : Matrix n n _)

variable {A : Type u} [CommRing A] [Algebra K A] [Algebra k A] [IsScalarTower k K A]

/-- The `K`-algebra map `K ⊗[k] O(G) → A` classifying a point of `G_K` over `A`. -/
def universalEval (x : ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).affinePoints
      (CommAlgCat.of (CommRingCat.of K) A)) :
    K ⊗[k] CharacterUnits.Coord G →ₐ[K] A :=
  Algebra.TensorProduct.lift (Algebra.ofId K A) (Lie.pointCoordinates G (scalarBasePoint x))
    (fun _ _ => Commute.all _ _)

/-- Every point of `G_K` is the image of the universal scalar point. -/
theorem universalScalarPoint_eval
    (x : ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).affinePoints
      (CommAlgCat.of (CommRingCat.of K) A)) :
    (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (universalEval x)).op ≫
      universalScalarPoint K G = x := by
  rw [universalScalarPoint, scalarPoint, scalarExtensionPoint_naturality]
  conv_rhs => rw [← scalarExtensionPoint_scalarBasePoint x]
  congr 1
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp, ← CommAlgCat.ofHom_comp]
  have hcomp : ((universalEval x).restrictScalars k).comp
      (Algebra.TensorProduct.includeRight : CharacterUnits.Coord G →ₐ[k] _) =
        Lie.pointCoordinates G (scalarBasePoint x) :=
    Algebra.TensorProduct.lift_comp_includeRight _ _ _
  rw [hcomp]
  rw [← GroupScheme.affinePointMap_apply]
  exact CharacterUnits.affinePointMap_universalPoint G (scalarBasePoint x)

omit [Algebra k A] [IsScalarTower k K A] in
theorem commAlgCat_ofHom_apply (f : K ⊗[k] CharacterUnits.Coord G →ₐ[K] A)
    (z : K ⊗[k] CharacterUnits.Coord G) :
    (CommAlgCat.ofHom (R := CommRingCat.of K) f).hom.toRingHom z = f z :=
  rfl

/-- Every affine matrix of a representation of `G_K` is an evaluation of its universal
matrix. -/
theorem affineMatrix_eq_universalEval
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (x : ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).affinePoints
      (CommAlgCat.of (CommRingCat.of K) A)) (i j : n) :
    (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of K) A) x : Matrix n n A) i j =
      universalEval x (universalMatrix ρ i j) := by
  have h := ρ.affineMatrix_naturality (CommAlgCat.ofHom (universalEval x))
    (universalScalarPoint K G)
  rw [universalScalarPoint_eval] at h
  have h2 := congrArg (fun M : GL n A => (M : Matrix n n A) i j) h
  simp only [Matrix.GeneralLinearGroup.map_apply] at h2
  rw [commAlgCat_ofHom_apply] at h2
  rw [universalMatrix]
  exact h2

omit [Algebra k A] [IsScalarTower k K A] [DecidableEq n] in
/-- A `K`-linear functional applied to a matrix acting on a constant vector. -/
theorem functional_mulVec_algebraMap (M : Matrix n n A) (L : A →ₗ[K] K) (v : n → K) :
    (fun i => L ((M *ᵥ fun j => algebraMap K A (v j)) i)) = M.map L *ᵥ v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/-- The affine matrix at a point is the universal matrix evaluated at the classifying map. -/
theorem affineMatrix_eq_map_universalEval
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (x : ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).affinePoints
      (CommAlgCat.of (CommRingCat.of K) A)) :
    (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of K) A) x : Matrix n n A) =
      (universalMatrix ρ).map (universalEval x) := by
  ext i j
  exact affineMatrix_eq_universalEval ρ x i j

end Universal

section Characterizations

variable [IsAffineHom G.X.hom] {m : Type} [Fintype m] [DecidableEq m]

/-- Actual stability over `K` is stability under every `K`-linear coefficient of the
universal matrix. -/
theorem isStableSubspace_iff_universalMatrix
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (V : Submodule K (n → K)) :
    ρ.IsStableSubspace V ↔
      ∀ L : K ⊗[k] CharacterUnits.Coord G →ₗ[K] K, ∀ v ∈ V,
        (universalMatrix ρ).map L *ᵥ v ∈ V := by
  constructor
  · intro h L v hv
    have := h (CommAlgCat.of (CommRingCat.of K) (K ⊗[k] CharacterUnits.Coord G))
      (universalScalarPoint K G) v hv L
    rwa [functional_mulVec_algebraMap] at this
  · intro h A x v hv ℓ
    let : Algebra k A := Algebra.compHom A (algebraMap k K)
    have : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
    have hM := affineMatrix_eq_map_universalEval (A := A) ρ x
    rw [functional_mulVec_algebraMap, hM, Matrix.map_map]
    exact h (ℓ.comp (universalEval (A := A) x).toLinearMap) v hv

/-- Actual intertwining over `K` is the intertwining identity for the universal matrices. -/
theorem intertwines_iff_universalMatrix
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (τ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) m)
    (C : Matrix m n K) :
    ρ.Intertwines τ C ↔
      C.map (algebraMap K (K ⊗[k] CharacterUnits.Coord G)) * universalMatrix ρ =
        universalMatrix τ * C.map (algebraMap K (K ⊗[k] CharacterUnits.Coord G)) := by
  constructor
  · intro h
    exact h (CommAlgCat.of (CommRingCat.of K) (K ⊗[k] CharacterUnits.Coord G))
      (universalScalarPoint K G)
  · intro h S x
    let : Algebra k S := Algebra.compHom S (algebraMap k K)
    have : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' rfl
    let f := universalEval (A := S) x
    have hC (p q : Type) (D : Matrix p q K) :
        D.map (algebraMap K S) = (D.map (algebraMap K (K ⊗[k] CharacterUnits.Coord G))).map
          f := by
      ext i j
      exact (f.commutes (D i j)).symm
    rw [affineMatrix_eq_map_universalEval (A := S) ρ x,
      affineMatrix_eq_map_universalEval (A := S) τ x, hC]
    have h' := congrArg (fun M => M.map f.toRingHom) h
    simp only [Matrix.map_mul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h'
    exact h'

end Characterizations

section Twist

variable [IsAffineHom G.X.hom] {m : Type} [Fintype m] [DecidableEq m]

/-- The universal matrix of a Galois twist is the universal matrix with `σ ⊗ id` applied to
its entries. -/
theorem universalMatrix_galoisTwist (σ : K ≃ₐ[k] K)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n) :
    universalMatrix (galoisTwist σ ρ) =
      (universalMatrix ρ).map (galoisTensor (CharacterUnits.Coord G) σ) := by
  ext i j
  rw [universalMatrix, universalMatrix, Matrix.map_apply]
  exact affineMatrix_galoisTwist_scalarPoint (CharacterUnits.Coord G) σ ρ
    (CharacterUnits.universalPoint G) i j

variable (R : Type u) [CommRing R] [Algebra k R]

theorem galoisTensor_symm_galoisTensor (σ : K ≃ₐ[k] K) (z : K ⊗[k] R) :
    galoisTensor R σ.symm (galoisTensor R σ z) = z := by
  induction z with
  | tmul c r => simp only [galoisTensor_tmul, AlgEquiv.symm_apply_apply]
  | add z w hz hw => simp only [map_add, hz, hw]

theorem galoisTensor_galoisTensor_symm (σ : K ≃ₐ[k] K) (z : K ⊗[k] R) :
    galoisTensor R σ (galoisTensor R σ.symm z) = z := by
  simpa only [AlgEquiv.symm_symm] using galoisTensor_symm_galoisTensor R σ.symm z

theorem galoisTensor_smul (σ : K ≃ₐ[k] K) (c : K) (z : K ⊗[k] R) :
    galoisTensor R σ (c • z) = σ c • galoisTensor R σ z := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

/-- The `K`-linear functional `σ ∘ L ∘ (σ⁻¹ ⊗ id)`. -/
def untwistFunctional (σ : K ≃ₐ[k] K) (L : K ⊗[k] R →ₗ[K] K) : K ⊗[k] R →ₗ[K] K where
  toFun z := σ (L (galoisTensor R σ.symm z))
  map_add' z w := by simp only [map_add]
  map_smul' c z := by
    rw [galoisTensor_smul, map_smul, smul_eq_mul, map_mul, AlgEquiv.apply_symm_apply,
      RingHom.id_apply, smul_eq_mul]

theorem untwistFunctional_galoisTensor (σ : K ≃ₐ[k] K) (L : K ⊗[k] R →ₗ[K] K)
    (z : K ⊗[k] R) :
    untwistFunctional R σ L (galoisTensor R σ z) = σ (L z) := by
  change σ (L (galoisTensor R σ.symm (galoisTensor R σ z))) = σ (L z)
  rw [galoisTensor_symm_galoisTensor]

end Twist

section TwistIrreducible

variable [IsAffineHom G.X.hom] {m : Type} [Fintype m] [DecidableEq m]

/-- Coefficients of the twisted universal matrix are the `σ`-conjugates of the coefficients of
the original universal matrix. -/
theorem universalMatrix_galoisTwist_map_untwist (σ : K ≃ₐ[k] K)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (L : K ⊗[k] CharacterUnits.Coord G →ₗ[K] K) :
    (universalMatrix (galoisTwist σ ρ)).map (untwistFunctional (CharacterUnits.Coord G) σ L) =
      ((universalMatrix ρ).map L).map σ := by
  rw [universalMatrix_galoisTwist]
  ext i j
  exact untwistFunctional_galoisTensor _ σ L _

/-- The `σ`-preimage `{w | σ ∘ w ∈ V}` of a subspace of `Kⁿ`. -/
def galoisComap (σ : K ≃ₐ[k] K) (V : Submodule K (n → K)) : Submodule K (n → K) where
  carrier := {w | (fun i => σ (w i)) ∈ V}
  add_mem' {v w} hv hw := by
    change (fun i => σ (v i + w i)) ∈ V
    simp only [map_add]
    exact V.add_mem hv hw
  zero_mem' := by
    change (fun i => σ ((0 : n → K) i)) ∈ V
    simp only [Pi.zero_apply, map_zero]
    exact V.zero_mem
  smul_mem' c w hw := by
    change (fun i => σ (c * w i)) ∈ V
    simp only [map_mul]
    exact V.smul_mem (σ c) hw

omit [Fintype n] [DecidableEq n] in
theorem mem_galoisComap (σ : K ≃ₐ[k] K) (V : Submodule K (n → K)) (w : n → K) :
    w ∈ galoisComap σ V ↔ (fun i => σ (w i)) ∈ V :=
  Iff.rfl

/-- A Galois twist of an irreducible representation is irreducible. -/
theorem IsIrreducible.galoisTwist (σ : K ≃ₐ[k] K)
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    (hρ : ρ.IsIrreducible) : (galoisTwist σ ρ).IsIrreducible := by
  refine ⟨hρ.1, fun V hV => ?_⟩
  rw [isStableSubspace_iff_universalMatrix] at hV
  have hW : ρ.IsStableSubspace (galoisComap σ V) := by
    rw [isStableSubspace_iff_universalMatrix]
    intro L w hw
    rw [mem_galoisComap]
    have h := hV (untwistFunctional (CharacterUnits.Coord G) σ L) _ hw
    rw [universalMatrix_galoisTwist_map_untwist] at h
    convert h using 1
    funext i
    exact RingHom.map_mulVec σ.toRingHom _ _ i
  have hinv (v : n → K) : (fun i => σ.symm (v i)) ∈ galoisComap σ V ↔ v ∈ V := by
    rw [mem_galoisComap]
    simp only [AlgEquiv.apply_symm_apply]
  rcases hρ.2 _ hW with h | h
  · left
    rw [eq_bot_iff]
    intro v hv
    have h0 := (hinv v).mpr hv
    rw [h, Submodule.mem_bot] at h0
    rw [Submodule.mem_bot]
    funext i
    have := congrFun h0 i
    simpa using this
  · right
    rw [eq_top_iff]
    intro v _
    rw [← hinv v, h]
    exact Submodule.mem_top

/-- A Galois twist carries intertwiners to their `σ`-conjugates. -/
theorem Intertwines.galoisTwist (σ : K ≃ₐ[k] K)
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {τ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) m}
    {C : Matrix m n K} (hC : ρ.Intertwines τ C) :
    (galoisTwist σ ρ).Intertwines (galoisTwist σ τ) (C.map σ) := by
  rw [intertwines_iff_universalMatrix] at hC ⊢
  rw [universalMatrix_galoisTwist, universalMatrix_galoisTwist]
  have hmap (p q : Type) (D : Matrix p q K) :
      (D.map σ).map (algebraMap K (K ⊗[k] CharacterUnits.Coord G)) =
        (D.map (algebraMap K (K ⊗[k] CharacterUnits.Coord G))).map
          (galoisTensor (CharacterUnits.Coord G) σ) := by
    ext i j
    rfl
  rw [hmap]
  have h' := congrArg (fun M => M.map (galoisTensor (CharacterUnits.Coord G) σ).toRingHom) hC
  simp only [Matrix.map_mul] at h'
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using h'

end TwistIrreducible



end Langlands.GroupScheme.MatrixRepresentation
