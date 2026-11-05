import Langlands.GroupScheme.Reductive.ReynoldsRegularCoefficient
import Langlands.GroupScheme.Reductive.AffineInducedRegular

/-! # Diagonalizable-invariant regular maps for actual affine groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem productMap_rTensor {K B C A : Type*} [CommSemiring K]
    [CommSemiring B] [CommSemiring C] [CommSemiring A]
    [Algebra K B] [Algebra K C] [Algebra K A]
    (r : B →ₐ[K] C) (f : C →ₐ[K] A) (g : B →ₐ[K] A) (z : B ⊗[K] B) :
    Algebra.TensorProduct.productMap f g (r.toLinearMap.rTensor B z) =
      Algebra.TensorProduct.productMap (f.comp r) g z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

namespace AffineCoordinates

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
  {Λ : Type u} [AddCommGroup Λ]

set_option backward.isDefEq.respectTransparency false in
/-- Actual diagonalizable restriction in the coalgebra of the regular representation. -/
def corepresentationDiagonalizableRestriction
    (j : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G) :
    letI := AffineLinearEmbedding.bialgebra (corepresentation G)
    algebra G →ₐc[k] AddMonoidAlgebra k Λ := by
  let := AffineLinearEmbedding.bialgebra (corepresentation G)
  refine { toLinearMap := (diagonalizableRestriction j).toAlgHom.toLinearMap
           map_one' := (diagonalizableRestriction j).map_one
           map_mul' := (diagonalizableRestriction j).map_mul
           counit_comp := ?_
           map_comp_comul := ?_ }
  · rw [corepresentation_counit G]
    exact (diagonalizableRestriction j).counit_comp
  · rw [corepresentation_comul G]
    exact (diagonalizableRestriction j).map_comp_comul

set_option backward.isDefEq.respectTransparency false in
theorem corepresentationDiagonalizableRestriction_toAlgHom
    (j : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G) :
    letI := AffineLinearEmbedding.bialgebra (corepresentation G)
    (corepresentationDiagonalizableRestriction j).toAlgHom =
      (diagonalizableRestriction j).toAlgHom := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Spectrum of actual diagonalizable restriction recovers the original homomorphism. -/
theorem algSpec_map_diagonalizableRestriction
    (j : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G) :
    (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (diagonalizableRestriction j).toAlgHom).op =
      (Diagonalizable.hopfSpecIso (CommRingCat.of k) Λ).hom.hom.hom ≫ j.hom.hom ≫
        (groupSchemeIso G).inv.hom.hom := by
  have h := congrArg (fun z => z.hom.hom) (hopfSpec.fullyFaithful.map_preimage
    ((Diagonalizable.hopfSpecIso (CommRingCat.of k) Λ).hom ≫ j ≫ (hopfSpecIso G).inv))
  change (algSpec (CommRingCat.of k)).map
      (CommAlgCat.ofHom (diagonalizableRestriction j).toAlgHom).op =
    (Diagonalizable.hopfSpecIso (CommRingCat.of k) Λ).hom.hom.hom ≫ j.hom.hom ≫
      (hopfSpecIso G).inv.hom.hom at h
  rw [hopfSpecIso_inv_hom_hom, ← groupSchemeIso_inv_hom_hom] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation after the actual diagonalizable homomorphism is restriction of coordinates. -/
theorem pointAlgebraHom_diagonalizableRestriction
    (j : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G)
    (T : Over (Spec (CommRingCat.of k)))
    (h : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp.X) :
    pointAlgebraHom G T (h ≫ j.hom.hom) =
      (((algΓAlgSpecAdjunction (CommRingCat.of k)).homEquiv T
        (op (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra k Λ)))).symm
          (h ≫ (Diagonalizable.hopfSpecIso (CommRingCat.of k) Λ).inv.hom.hom)).unop.hom.comp
            (diagonalizableRestriction j).toAlgHom := by
  rw [pointAlgebraHom_eq]
  have hfac : (h ≫ j.hom.hom) ≫ (groupSchemeIso G).inv.hom.hom =
      (h ≫ (Diagonalizable.hopfSpecIso (CommRingCat.of k) Λ).inv.hom.hom) ≫
        (algSpec (CommRingCat.of k)).map
          (CommAlgCat.ofHom (diagonalizableRestriction j).toAlgHom).op := by
    rw [algSpec_map_diagonalizableRestriction]
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id_assoc]
  rw [hfac, (algΓAlgSpecAdjunction (CommRingCat.of k)).homEquiv_naturality_right_symm]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Tensor invariance under actual diagonalizable restriction implies invariance on every test. -/
theorem pointAlgebraHom_diagonalizableInvariant
    (j : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G)
    {w : algebra G}
    (hw : letI := (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
      (corepresentationDiagonalizableRestriction j).toAlgHom.toLinearMap.rTensor
        (algebra G) (comul (R := k) (A := algebra G) w) = (1 : AddMonoidAlgebra k Λ) ⊗ₜ[k] w)
    (T : Over (Spec (CommRingCat.of k)))
    (h : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp.X)
    (g : T ⟶ G.X) :
    pointAlgebraHom G T ((h ≫ j.hom.hom) * g) w = pointAlgebraHom G T g w := by
  let : Coalgebra k (algebra G) :=
    (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
  let r : algebra G →ₐ[k] AddMonoidAlgebra k Λ :=
    (corepresentationDiagonalizableRestriction j).toAlgHom
  let f : AddMonoidAlgebra k Λ →ₐ[k] ((algΓ (CommRingCat.of k)).obj T).unop :=
    (((algΓAlgSpecAdjunction (CommRingCat.of k)).homEquiv T
      (op (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra k Λ)))).symm
        (h ≫ (Diagonalizable.hopfSpecIso (CommRingCat.of k) Λ).inv.hom.hom)).unop.hom
  have he := congrArg (Algebra.TensorProduct.productMap f (pointAlgebraHom G T g)) hw
  change Algebra.TensorProduct.productMap f (pointAlgebraHom G T g)
    (r.toLinearMap.rTensor (algebra G) (comul (R := k) (A := algebra G) w)) = _ at he
  rw [productMap_rTensor] at he
  rw [pointAlgebraHom_mul, pointAlgebraHom_diagonalizableRestriction]
  change Algebra.TensorProduct.productMap (f.comp (diagonalizableRestriction j).toAlgHom)
    (pointAlgebraHom G T g) ((AffineLinearEmbedding.comul (corepresentation G)) w) = _
  dsimp only [r] at he
  rw [corepresentationDiagonalizableRestriction_toAlgHom j] at he
  simp only [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul] at he
  convert he using 1
  congr 1

end AffineCoordinates

namespace Chevalley

open AffineLinearEmbedding MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
  {Λ : Type u} [AddCommGroup Λ]
  {n : Type} [Fintype n] [DecidableEq n]

/-- An actual diagonalizable homomorphism gives a normalized finite covariant regular map. -/
theorem exists_affine_finite_diagonalizable_regular_map_to_one
    (j : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G)
    (ρ : MatrixRepresentation G n) (v : n → k) (hv0 : v ≠ 0)
    (hv : ρ.IsFixedVector v) :
    letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
    ∃ (V : Submodule k (AffineCoordinates.algebra G)) (d : ℕ)
      (b : Basis (Fin d) k V)
      (hV : ∀ (ψ : Module.Dual k (AffineCoordinates.algebra G))
        (w : AffineCoordinates.algebra G), w ∈ V → rightAct ψ w ∈ V)
      (C : Matrix (Fin d) n k),
      Intertwines ρ (affineRegularRepresentation G V b hV) C ∧
        (∀ w ∈ V,
          (AffineCoordinates.corepresentationDiagonalizableRestriction j).toAlgHom.toLinearMap.rTensor
            (AffineCoordinates.algebra G)
              (comul (R := k) (A := AffineCoordinates.algebra G) w) =
              (1 : AddMonoidAlgebra k Λ) ⊗ₜ[k] w) ∧
        (∀ w ∈ V, ∀ (T : Over (Spec (CommRingCat.of k)))
          (h : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp.X)
          (g : T ⟶ G.X),
          AffineCoordinates.pointAlgebraHom G T ((h ≫ j.hom.hom) * g) w =
            AffineCoordinates.pointAlgebraHom G T g w) ∧
        ∑ l, (C *ᵥ v) l • (b l : AffineCoordinates.algebra G) = 1 := by
  let e := AffineCoordinates.groupSchemeIso G
  have hv' : (ρ.restrict e.hom).IsFixedVector v := by
    intro T g
    rw [pointMatrix_restrict]
    exact hv T (g ≫ e.hom.hom.hom)
  obtain ⟨V, d, b, hV, C, hC, hcov, h1⟩ :=
    exists_finite_diagonalizable_regular_map_to_one (AffineCoordinates.corepresentation G)
      (AffineCoordinates.corepresentationDiagonalizableRestriction j)
      (ρ.restrict e.hom) v hv0 hv'
  refine ⟨V, d, b, hV, C, ?_, hcov, ?_, h1⟩
  · intro A g
    have h := hC A (g ≫ e.inv.hom.hom)
    rw [affineMatrix_restrict] at h
    have he : (g ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = g := by
      simp only [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom,
        Category.comp_id]
    rw [he] at h
    exact h
  · intro w hw T h g
    exact AffineCoordinates.pointAlgebraHom_diagonalizableInvariant j (hcov w hw) T h g

end Chevalley

end Langlands.GroupScheme
