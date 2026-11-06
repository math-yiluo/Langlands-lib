import Langlands.GroupScheme.Reductive.FrobeniusRegularSubspace
import Langlands.GroupScheme.MatrixRepresentation.DenseRationalStability
import Langlands.GroupScheme.MatrixRepresentation.MinimalStableSubrepresentation

/-! # Multiplication with Frobenius-powered regular coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Module TensorProduct
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}
  {C : Matrix m n k}

/-- The kernel of an actual intertwiner is stable on every affine test. -/
theorem Intertwines.isStableSubspace_ker (hC : Intertwines ρ σ C) :
    ρ.IsStableSubspace (LinearMap.ker C.mulVecLin) :=
  (isStableSubspace_bot σ).comap hC

/-- A nonzero actual intertwiner with irreducible source is injective. -/
theorem Intertwines.injective_of_isIrreducible (hC : Intertwines ρ σ C)
    (hρ : ρ.IsIrreducible) (hC0 : C.mulVecLin ≠ 0) :
    Function.Injective C.mulVecLin := by
  apply LinearMap.ker_eq_bot.mp
  rcases hρ.2 _ hC.isStableSubspace_ker with h | h
  · exact h
  · exact False.elim (hC0 (LinearMap.ker_eq_top.mp h))

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.Chevalley

open AffineLinearEmbedding MatrixRepresentation

section Algebra

variable {k B : Type u} [Field k] [CommRing B] [Algebra k B]
  (V W : Submodule k B)

/-- Coordinate multiplication with its image as codomain. -/
def coordinateProductToSubmodule : V ⊗[k] W →ₗ[k] (V * W) :=
  (coordinateProduct V W).codRestrict (V * W) fun z => by
    rw [← range_coordinateProduct]
    exact ⟨z, rfl⟩

@[simp]
theorem coordinateProductToSubmodule_coe (z : V ⊗[k] W) :
    (coordinateProductToSubmodule V W z : B) = coordinateProduct V W z := rfl

/-- Multiplication is always onto the product subspace. -/
theorem coordinateProductToSubmodule_surjective :
    Function.Surjective (coordinateProductToSubmodule V W) := by
  rintro ⟨z, hz⟩
  obtain ⟨t, ht⟩ := (range_coordinateProduct V W).symm ▸ hz
  exact ⟨t, Subtype.ext ht⟩

variable {a b c : ℕ}
  (bV : Basis (Fin a) k V) (bW : Basis (Fin b) k W)
  (bP : Basis (Fin c) k (V * W))

/-- The existing product matrix is the matrix of multiplication in tensor bases. -/
theorem productMatrix_eq_toMatrix :
    productMatrix V W bV bW bP =
      LinearMap.toMatrix (bV.tensorProduct bW) bP (coordinateProductToSubmodule V W) := by
  ext i j
  have hp := LinearMap.congr_fun (subspaceRetraction_comp_subtype (V * W))
    (coordinateProductToSubmodule V W ((bV j.1) ⊗ₜ[k] (bW j.2)))
  change subspaceRetraction (V * W) ((bV j.1 : B) * (bW j.2 : B)) = _ at hp
  simp only [productMatrix, Matrix.of_apply, extendedCoord, LinearMap.comp_apply,
    LinearMap.toMatrix_apply, Basis.tensorProduct_apply', Basis.coord_apply, hp,
    LinearMap.id_apply]

/-- The product matrix computes coordinates of multiplication for every tensor. -/
theorem productMatrix_mulVec_equivFun (z : V ⊗[k] W) :
    productMatrix V W bV bW bP *ᵥ (bV.tensorProduct bW).equivFun z =
      bP.equivFun (coordinateProductToSubmodule V W z) := by
  rw [productMatrix_eq_toMatrix]
  exact LinearMap.toMatrix_mulVec_repr _ _ _ _

/-- The product matrix is onto the coordinate space of the product subspace. -/
theorem productMatrix_mulVecLin_surjective :
    Function.Surjective (productMatrix V W bV bW bP).mulVecLin := by
  intro v
  obtain ⟨z, hz⟩ := coordinateProductToSubmodule_surjective V W (bP.equivFun.symm v)
  refine ⟨(bV.tensorProduct bW).equivFun z, ?_⟩
  change productMatrix V W bV bW bP *ᵥ _ = _
  rw [productMatrix_mulVec_equivFun, hz, LinearEquiv.apply_symm_apply]

/-- Injectivity of the multiplication matrix implies injectivity on the full tensor product. -/
theorem coordinateProduct_injective_of_productMatrix
    (hinj : Function.Injective (productMatrix V W bV bW bP).mulVecLin) :
    Function.Injective (coordinateProduct V W) := by
  intro z t hzt
  apply (bV.tensorProduct bW).equivFun.injective
  apply hinj
  change productMatrix V W bV bW bP *ᵥ _ = productMatrix V W bV bW bP *ᵥ _
  rw [productMatrix_mulVec_equivFun, productMatrix_mulVec_equivFun]
  congr 1
  exact Subtype.ext hzt

/-- A single nonzero product makes the multiplication matrix nonzero. -/
theorem productMatrix_mulVecLin_ne_zero (v : V) (w : W)
    (hvw : (v : B) * (w : B) ≠ 0) :
    (productMatrix V W bV bW bP).mulVecLin ≠ 0 := by
  intro hzero
  have hz := productMatrix_mulVec_equivFun V W bV bW bP (v ⊗ₜ[k] w)
  have he : bP.equivFun (coordinateProductToSubmodule V W (v ⊗ₜ[k] w)) = 0 := by
    rw [← hz]
    change (productMatrix V W bV bW bP).mulVecLin _ = 0
    rw [hzero, LinearMap.zero_apply]
  have he' : coordinateProductToSubmodule V W (v ⊗ₜ[k] w) = 0 :=
    bP.equivFun.injective (by simpa only [map_zero] using he)
  exact hvw (congrArg Subtype.val he')

end Algebra

section Affine

variable {k : Type u} [Field k] (p : ℕ) [ExpChar k p] [PerfectRing k p]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left] [IsReduced G.X.left]
  (V W : Submodule k (AffineCoordinates.algebra G)) {a b c : ℕ}
  (bV : Basis (Fin a) k V) (bW : Basis (Fin b) k W)
  (hV : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
    ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (v : AffineCoordinates.algebra G),
      v ∈ V → rightAct f v ∈ V)
  (hW : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
    ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (w : AffineCoordinates.algebra G),
      w ∈ W → rightAct f w ∈ W)

local instance frobeniusProductsReducedAlgebra :
    _root_.IsReduced (AffineCoordinates.algebra G) := by
  have : IsIso (AffineCoordinates.groupSchemeIso G).hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso
      (AffineCoordinates.groupSchemeIso G))).hom)
  have h := isReduced_of_isOpenImmersion (AffineCoordinates.groupSchemeIso G).hom.hom.hom.left
  exact (affine_isReduced_iff (CommRingCat.of (AffineCoordinates.algebra G))).mp h

variable (e : ℕ)

/-- The multiplication matrix on a tensor factor and powered coordinates. -/
def frobeniusProductMatrix
    (bP : Basis (Fin c) k (V * frobeniusCoordinateSpan p e W)) :
    Matrix (Fin c) (Fin a × Fin b) k :=
  productMatrix V (frobeniusCoordinateSpan p e W) bV
    (frobeniusCoordinateBasis p e W bW) bP

include bV bW hV hW in
/-- Products with powered coordinates are regular. -/
theorem affine_rightAct_mem_mul_frobeniusCoordinateSpan :
    letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
    ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (z : AffineCoordinates.algebra G),
      z ∈ V * frobeniusCoordinateSpan p e W →
        rightAct f z ∈ V * frobeniusCoordinateSpan p e W := by
  let := bialgebra (AffineCoordinates.corepresentation G)
  exact affine_rightAct_mem_mul G V (frobeniusCoordinateSpan p e W) bV
    (frobeniusCoordinateBasis p e W bW) hV
    (fun f _ hw => rightAct_mem_frobeniusCoordinateSpan p e W bW hW f hw)

variable (bP : Basis (Fin c) k (V * frobeniusCoordinateSpan p e W))
  (hP : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
    ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (z : AffineCoordinates.algebra G),
      z ∈ V * frobeniusCoordinateSpan p e W →
        rightAct f z ∈ V * frobeniusCoordinateSpan p e W)

/-- Multiplication intertwines the actual tensor with matrix Frobenius and the
regular representation on the product, including over nonreduced test algebras. -/
theorem intertwines_affine_frobeniusProductMatrix :
    Intertwines
      ((affineRegularRepresentation G V bV hV).tensor
        ((affineRegularRepresentation G W bW hW).frobeniusPower p e))
      (affineRegularRepresentation G (V * frobeniusCoordinateSpan p e W) bP hP)
      (frobeniusProductMatrix p G V W bV bW e bP) := by
  let := bialgebra (AffineCoordinates.corepresentation G)
  have h := intertwines_affine_productMatrix G V (frobeniusCoordinateSpan p e W) bV
    (frobeniusCoordinateBasis p e W bW) bP hV
    (fun f _ hw => rightAct_mem_frobeniusCoordinateSpan p e W bW hW f hw) hP
  intro A x
  have hF :
      ((affineRegularRepresentation G V bV hV).tensor
        ((affineRegularRepresentation G W bW hW).frobeniusPower p e)).affineMatrix A x =
      ((affineRegularRepresentation G V bV hV).tensor
        (affineFrobeniusRegularRepresentation p G W bW hW e)).affineMatrix A x := by
    apply Units.ext
    ext ⟨i, j⟩ ⟨i', j'⟩
    rw [tensor_affineMatrix_entry, tensor_affineMatrix_entry,
      affineFrobeniusRegularRepresentation_affineMatrix, frobeniusPower_affineMatrix]
  rw [hF]
  exact h A x

include hP in
/-- A nonzero product and irreducibility of the supplied tensor make its actual
multiplication matrix injective. -/
theorem frobeniusProductMatrix_injective_of_isIrreducible
    (hρ : ((affineRegularRepresentation G V bV hV).tensor
      ((affineRegularRepresentation G W bW hW).frobeniusPower p e)).IsIrreducible)
    (hnonzero : ∃ v ∈ V, ∃ w ∈ W,
      v * w ^ p ^ e ≠ (0 : AffineCoordinates.algebra G)) :
    Function.Injective (frobeniusProductMatrix p G V W bV bW e bP).mulVecLin := by
  have hM := intertwines_affine_frobeniusProductMatrix p G V W bV bW hV hW e bP hP
  apply hM.injective_of_isIrreducible hρ
  obtain ⟨v, hv, w, hw, hvw⟩ := hnonzero
  exact productMatrix_mulVecLin_ne_zero V (frobeniusCoordinateSpan p e W) bV
    (frobeniusCoordinateBasis p e W bW) bP ⟨v, hv⟩
    ⟨w ^ p ^ e, pow_mem_frobeniusCoordinateSpan p e W hw⟩ hvw

include bV bW hV hW in
/-- Under supplied tensor irreducibility and nonzero multiplication, multiplication
is injective on the full tensor product, independently of product coordinates. -/
theorem coordinateProduct_injective_of_frobeniusTensor_isIrreducible
    (hρ : ((affineRegularRepresentation G V bV hV).tensor
      ((affineRegularRepresentation G W bW hW).frobeniusPower p e)).IsIrreducible)
    (hnonzero : ∃ v ∈ V, ∃ w ∈ W,
      v * w ^ p ^ e ≠ (0 : AffineCoordinates.algebra G)) :
    Function.Injective (coordinateProduct V (frobeniusCoordinateSpan p e W)) := by
  let := bialgebra (AffineCoordinates.corepresentation G)
  have : Module.Finite k V := Module.Finite.of_basis bV
  have : Module.Finite k W := Module.Finite.of_basis bW
  have : Module.Finite k (frobeniusCoordinateSpan p e W) :=
    finite_frobeniusCoordinateSpan p e W
  have : Module.Finite k (V * frobeniusCoordinateSpan p e W) :=
    finite_coordinateProduct V (frobeniusCoordinateSpan p e W)
  let bP := Module.finBasis k (V * frobeniusCoordinateSpan p e W)
  apply coordinateProduct_injective_of_productMatrix V (frobeniusCoordinateSpan p e W) bV
    (frobeniusCoordinateBasis p e W bW) bP
  exact frobeniusProductMatrix_injective_of_isIrreducible p G V W bV bW hV hW e bP
    (affine_rightAct_mem_mul_frobeniusCoordinateSpan p G V W bV bW hV hW e) hρ hnonzero

/-- Actual tensor multiplication as a linear equivalence onto its product image,
when tensor irreducibility and a nonzero product are supplied. -/
def frobeniusCoordinateProductEquiv
    (hρ : ((affineRegularRepresentation G V bV hV).tensor
      ((affineRegularRepresentation G W bW hW).frobeniusPower p e)).IsIrreducible)
    (hnonzero : ∃ v ∈ V, ∃ w ∈ W,
      v * w ^ p ^ e ≠ (0 : AffineCoordinates.algebra G)) :
    (V ⊗[k] frobeniusCoordinateSpan p e W) ≃ₗ[k] (V * frobeniusCoordinateSpan p e W) :=
  LinearEquiv.ofBijective (coordinateProductToSubmodule V (frobeniusCoordinateSpan p e W))
    ⟨fun _ _ h => coordinateProduct_injective_of_frobeniusTensor_isIrreducible
      p G V W bV bW hV hW e hρ hnonzero (congrArg Subtype.val h),
      coordinateProductToSubmodule_surjective V (frobeniusCoordinateSpan p e W)⟩

@[simp]
theorem frobeniusCoordinateProductEquiv_tmul
    (hρ : ((affineRegularRepresentation G V bV hV).tensor
      ((affineRegularRepresentation G W bW hW).frobeniusPower p e)).IsIrreducible)
    (hnonzero : ∃ v ∈ V, ∃ w ∈ W,
      v * w ^ p ^ e ≠ (0 : AffineCoordinates.algebra G))
    (v : V) (w : frobeniusCoordinateSpan p e W) :
    (frobeniusCoordinateProductEquiv p G V W bV bW hV hW e hρ hnonzero
      (v ⊗ₜ[k] w) : AffineCoordinates.algebra G) =
      (v : AffineCoordinates.algebra G) * (w : AffineCoordinates.algebra G) := rfl

include bV bW hV hW in
/-- Counit-one coordinates supply the nonzero product premise for injectivity. -/
theorem coordinateProduct_injective_of_frobeniusTensor_isIrreducible_counit
    (hρ : ((affineRegularRepresentation G V bV hV).tensor
      ((affineRegularRepresentation G W bW hW).frobeniusPower p e)).IsIrreducible)
    {v w : AffineCoordinates.algebra G} (hv : v ∈ V) (hw : w ∈ W)
    (hv1 : counit (AffineCoordinates.corepresentation G) v = 1)
    (hw1 : counit (AffineCoordinates.corepresentation G) w = 1) :
    Function.Injective (coordinateProduct V (frobeniusCoordinateSpan p e W)) := by
  apply coordinateProduct_injective_of_frobeniusTensor_isIrreducible
    p G V W bV bW hV hW e hρ
  refine ⟨v, hv, w, hw, ?_⟩
  intro he
  have hc := congrArg (counit (AffineCoordinates.corepresentation G)) he
  simp only [map_mul, map_pow, hv1, hw1, one_pow, mul_one, map_zero] at hc
  exact one_ne_zero hc

end Affine

end Langlands.GroupScheme.Chevalley

namespace Langlands.GroupScheme.AffineCoordinates

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- A product with a powered covariant subspace has the expected product weight. -/
theorem mul_frobeniusCoordinateSpan_le_leftCovariantSubspace
    (p e : ℕ) (i : H ⟶ G) (χ ψ : algebra H)
    {V W : Submodule k (algebra G)}
    (hV : V ≤ leftCovariantSubspace i χ) (hW : W ≤ leftCovariantSubspace i ψ) :
    V * Chevalley.frobeniusCoordinateSpan p e W ≤ leftCovariantSubspace i (χ * ψ ^ p ^ e) :=
  mul_le_leftCovariantSubspace i χ (ψ ^ p ^ e) hV
    (frobeniusCoordinateSpan_le_leftCovariantSubspace p e i ψ hW)

end Langlands.GroupScheme.AffineCoordinates
