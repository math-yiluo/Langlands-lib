import Langlands.GroupScheme.Reductive.AffineInducedRegular
import Langlands.GroupScheme.Chevalley.CoefficientEmbedding
import Langlands.GroupScheme.Chevalley.ActualRepresentationExtension
import Langlands.GroupScheme.MatrixRepresentationTensor
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Multiplication of covariant coordinate spaces -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.Chevalley

open AffineLinearEmbedding MatrixRepresentation

section Algebra

variable {k B C : Type*} [Field k] [CommRing B] [Algebra k B]
  [CommRing C] [Algebra k C]

/-- Multiplication of two coordinate subspaces on their full tensor product. -/
def coordinateProduct (V W : Submodule k B) : V ⊗[k] W →ₗ[k] B :=
  LinearMap.mul' k B ∘ₗ TensorProduct.map V.subtype W.subtype

@[simp]
theorem coordinateProduct_tmul (V W : Submodule k B) (v : V) (w : W) :
    coordinateProduct V W (v ⊗ₜ[k] w) = (v : B) * (w : B) := rfl

/-- The multiplication image is precisely the usual product of submodules. -/
theorem range_coordinateProduct (V W : Submodule k B) :
    LinearMap.range (coordinateProduct V W) = V * W := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul v w => exact Submodule.mul_mem_mul v.2 w.2
    | add z t hz ht => simpa only [map_add] using (V * W).add_mem hz ht
  · apply Submodule.mul_le.mpr
    intro v hv w hw
    exact ⟨(⟨v, hv⟩ : V) ⊗ₜ[k] (⟨w, hw⟩ : W), rfl⟩

/-- Coordinates, in a basis of the product subspace, of the products of basis vectors. -/
def productMatrix (V W : Submodule k B) {a b c : ℕ}
    (bV : Basis (Fin a) k V) (bW : Basis (Fin b) k W) (bP : Basis (Fin c) k (V * W)) :
    Matrix (Fin c) (Fin a × Fin b) k :=
  Matrix.of fun i l => extendedCoord (V * W) bP i ((bV l.1 : B) * (bW l.2 : B))

/-- Products of finite coordinate subspaces are finite. -/
theorem finite_coordinateProduct (V W : Submodule k B)
    [Module.Finite k V] [Module.Finite k W] : Module.Finite k (V * W) := by
  rw [← range_coordinateProduct V W]
  infer_instance

end Algebra

section Bialgebra

variable {k B C : Type*} [Field k] [CommRing B] [Bialgebra k B]
  [CommRing C] [Algebra k C]

private theorem rTensor_mul (r : B →ₐ[k] C) (x y : B ⊗[k] B) :
    r.toLinearMap.rTensor B (x * y) =
      r.toLinearMap.rTensor B x * r.toLinearMap.rTensor B y :=
  (Algebra.TensorProduct.map r (AlgHom.id k B)).map_mul x y

/-- Multiplication adds covariance weights, expressed multiplicatively in the
restricted coordinate algebra. No group-like hypothesis is needed. -/
theorem mul_mem_leftCovariantSubspace (r : B →ₐ[k] C) (χ ψ : C)
    {v w : B} (hv : v ∈ leftCovariantSubspace r.toLinearMap χ)
    (hw : w ∈ leftCovariantSubspace r.toLinearMap ψ) :
    v * w ∈ leftCovariantSubspace r.toLinearMap (χ * ψ) := by
  rw [mem_leftCovariantSubspace] at hv hw ⊢
  rw [Bialgebra.comul_mul, rTensor_mul, hv, hw,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- Every linear combination of products has the product covariance weight. -/
theorem mul_le_leftCovariantSubspace (r : B →ₐ[k] C) (χ ψ : C)
    {V W : Submodule k B}
    (hV : V ≤ leftCovariantSubspace r.toLinearMap χ)
    (hW : W ≤ leftCovariantSubspace r.toLinearMap ψ) :
    V * W ≤ leftCovariantSubspace r.toLinearMap (χ * ψ) :=
  Submodule.mul_le.mpr fun _ hv _ hw =>
    mul_mem_leftCovariantSubspace r χ ψ (hV hv) (hW hw)

variable (V W : Submodule k B) {a b : ℕ}
  (bV : Basis (Fin a) k V) (bW : Basis (Fin b) k W)
  (hV : ∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V)
  (hW : ∀ (f : Module.Dual k B) (w : B), w ∈ W → rightAct f w ∈ W)

include hV hW in
/-- The actual coaction on a product of basis coordinates. -/
theorem comul_basis_mul (i : Fin a) (j : Fin b) :
    comul (R := k) ((bV i : B) * (bW j : B)) =
      ∑ l : Fin a × Fin b,
        ((bV l.1 : B) * (bW l.2 : B)) ⊗ₜ[k]
          (subspaceMatrix V bV l.1 i * subspaceMatrix W bW l.2 j) := by
  rw [Bialgebra.comul_mul, comul_basis V bV hV, comul_basis W bW hW]
  simp only [Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

include hV hW in
/-- Contracting the product coaction gives a linear combination of basis products. -/
theorem rightAct_basis_mul (f : Module.Dual k B) (i : Fin a) (j : Fin b) :
    rightAct f ((bV i : B) * (bW j : B)) =
      ∑ l : Fin a × Fin b,
        f (subspaceMatrix V bV l.1 i * subspaceMatrix W bW l.2 j) •
          ((bV l.1 : B) * (bW l.2 : B)) := by
  rw [rightAct_apply, comul_basis_mul V W bV bW hV hW, map_sum, map_sum]
  simp

include hV hW in
/-- The product of two finite regular subspaces is itself regular. -/
theorem rightAct_mem_mul [Module.Finite k V] [Module.Finite k W]
    (f : Module.Dual k B) {z : B} (hz : z ∈ V * W) :
    rightAct f z ∈ V * W := by
  let bV := Module.finBasis k V
  let bW := Module.finBasis k W
  refine Submodule.mul_induction_on hz (fun v hv w hw => ?_) (fun x y hx hy => ?_)
  · rw [← basis_expand V bV hv, ← basis_expand W bW hw, Finset.sum_mul_sum, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_mul_smul_comm, map_smul, rightAct_basis_mul V W bV bW hV hW]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem _ _ (Submodule.mul_mem_mul (bV l.1).2 (bW l.2).2))
  · rw [map_add]
    exact Submodule.add_mem _ hx hy

end Bialgebra

section Actual

variable {k : Type u} [Field k]
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- The universal matrix of an actual tensor representation is the Kronecker product. -/
theorem universalMatrix_tensor {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n)
    (σ : MatrixRepresentation (Corepresented.groupScheme F e) m) (i i' : n) (j j' : m) :
    Unipotent.universalMatrix e (ρ.tensor σ) (i, j) (i', j') =
      Unipotent.universalMatrix e ρ i i' * Unipotent.universalMatrix e σ j j' :=
  tensor_affineMatrix_entry ρ σ B _ i i' j j'

variable (V W : Submodule k B) {a b c : ℕ}
  (bV : Basis (Fin a) k V) (bW : Basis (Fin b) k W) (bP : Basis (Fin c) k (V * W))

variable (hV : letI := (bialgebra e).toCoalgebra
    ∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V)
  (hW : letI := (bialgebra e).toCoalgebra
    ∀ (f : Module.Dual k B) (w : B), w ∈ W → rightAct f w ∈ W)
  (hP : letI := (bialgebra e).toCoalgebra
    ∀ (f : Module.Dual k B) (z : B), z ∈ V * W → rightAct f z ∈ V * W)

/-- Multiplication of coordinates is an actual equivariant map from the tensor
product of two finite regular representations to the regular representation on
their product subspace. -/
theorem intertwines_productMatrix :
    Intertwines
      ((regularRepresentation e (Field.toIsField k) V bV hV).tensor
        (regularRepresentation e (Field.toIsField k) W bW hW))
      (regularRepresentation e (Field.toIsField k) (V * W) bP hP)
      (productMatrix V W bV bW bP) := by
  let := bialgebra e
  apply intertwines_of_universalMatrix e
  have hT : Unipotent.universalMatrix e
      ((regularRepresentation e (Field.toIsField k) V bV hV).tensor
        (regularRepresentation e (Field.toIsField k) W bW hW)) =
      Matrix.of fun l l' : Fin a × Fin b =>
        subspaceMatrix V bV l.1 l'.1 * subspaceMatrix W bW l.2 l'.2 := by
    ext ⟨i, j⟩ ⟨i', j'⟩
    rw [universalMatrix_tensor, regularRepresentation_universalMatrix,
      regularRepresentation_universalMatrix]
    rfl
  rw [hT, regularRepresentation_universalMatrix]
  exact coactionCoordinates_mul (V * W) bP _ _
    (fun l => Submodule.mul_mem_mul (bV l.1).2 (bW l.2).2)
    (fun l => comul_basis_mul V W bV bW hV hW l.1 l.2)

end Actual

section Affine

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
  (V W : Submodule k (AffineCoordinates.algebra G)) {a b c : ℕ}
  (bV : Basis (Fin a) k V) (bW : Basis (Fin b) k W) (bP : Basis (Fin c) k (V * W))
  (hV : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
    ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (v : AffineCoordinates.algebra G),
      v ∈ V → rightAct f v ∈ V)
  (hW : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
    ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (w : AffineCoordinates.algebra G),
      w ∈ W → rightAct f w ∈ W)

include bV bW hV hW in
/-- The product of two finite regular coordinate subspaces of an actual affine group
is again regular. -/
theorem affine_rightAct_mem_mul :
    letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
    ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (z : AffineCoordinates.algebra G),
      z ∈ V * W → rightAct f z ∈ V * W := by
  let := bialgebra (AffineCoordinates.corepresentation G)
  have : Module.Finite k V := Module.Finite.of_basis bV
  have : Module.Finite k W := Module.Finite.of_basis bW
  exact fun f _ hz => rightAct_mem_mul V W hV hW f hz

variable (hP : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
    ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (z : AffineCoordinates.algebra G),
      z ∈ V * W → rightAct f z ∈ V * W)

/-- On an arbitrary affine group, multiplication of coordinates intertwines the
actual tensor product of two finite regular representations with the finite
regular representation on the product subspace. -/
theorem intertwines_affine_productMatrix :
    Intertwines
      ((affineRegularRepresentation G V bV hV).tensor (affineRegularRepresentation G W bW hW))
      (affineRegularRepresentation G (V * W) bP hP) (productMatrix V W bV bW bP) := by
  have h := Intertwines.restrict (intertwines_productMatrix (AffineCoordinates.corepresentation G)
    V W bV bW bP hV hW hP) (AffineCoordinates.groupSchemeIso G).inv
  rw [← tensor_restrict] at h
  exact h

end Affine

end Langlands.GroupScheme.Chevalley

namespace Langlands.GroupScheme.AffineCoordinates

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance covariantProductsInst1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance covariantProductsInst2 : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

set_option backward.isDefEq.respectTransparency false in
/-- Products of covariant coordinates for an actual affine group morphism have the
product covariance coordinate. -/
theorem mul_mem_leftCovariantSubspace (i : H ⟶ G) (χ ψ : algebra H)
    {v w : algebra G} (hv : v ∈ leftCovariantSubspace i χ)
    (hw : w ∈ leftCovariantSubspace i ψ) :
    v * w ∈ leftCovariantSubspace i (χ * ψ) := by
  let := AffineLinearEmbedding.bialgebra (corepresentation G)
  exact Chevalley.mul_mem_leftCovariantSubspace (k := k) (B := algebra G) (C := algebra H)
    (AffineHomImageHopfAdapter.pullback i).hom.toAlgHom χ ψ hv hw

/-- Products of subspaces of covariant coordinates have the product covariance
coordinate. -/
theorem mul_le_leftCovariantSubspace (i : H ⟶ G) (χ ψ : algebra H)
    {V W : Submodule k (algebra G)} (hV : V ≤ leftCovariantSubspace i χ)
    (hW : W ≤ leftCovariantSubspace i ψ) :
    V * W ≤ leftCovariantSubspace i (χ * ψ) :=
  Submodule.mul_le.mpr fun _ hv _ hw =>
    mul_mem_leftCovariantSubspace i χ ψ (hV hv) (hW hw)

end Langlands.GroupScheme.AffineCoordinates
