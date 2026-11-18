import Langlands.GroupScheme.Torus.MultiplicativeTypeSemisimplePointsStatement
import Langlands.GroupScheme.Torus.SemisimplePointsCoefficients
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof
import Langlands.GroupScheme.Unipotent.CoordinateBialgebra
import Langlands.GroupScheme.AffineCoordinateEvaluation
import Langlands.GroupScheme.AffineLinearEmbedding.Comodule
import Langlands.GroupScheme.Rational.SmoothHopfCoordinates

/-! # Proof: smooth commutative groups with semisimple geometric points (Milne 12.21) -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.SemisimplePoints

section Coordinates

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- The matrix of a representation at an affine point is the universal matrix of the
corepresented model, with the classifying algebra map applied to its entries. -/
theorem affineMatrix_eq_map_universalMatrix {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (S : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶ G.X) :
    (ρ.affineMatrix S x : Matrix n n S) =
      (Unipotent.universalMatrix (AffineCoordinates.corepresentation G)
        (ρ.restrict (AffineCoordinates.groupSchemeIso G).hom)).map
        (algSpec.fullyFaithful.preimage (X := op S) (Y := op (AffineCoordinates.algebra G))
          (x ≫ (AffineCoordinates.groupSchemeIso G).inv.hom.hom)).unop.hom := by
  rw [← Unipotent.affineMatrix_classifiedPoint, MatrixRepresentation.affineMatrix_restrict]
  have hy : Unipotent.classifiedPoint (AffineCoordinates.corepresentation G)
      (algSpec.fullyFaithful.preimage (X := op S) (Y := op (AffineCoordinates.algebra G))
        (x ≫ (AffineCoordinates.groupSchemeIso G).inv.hom.hom)).unop =
      x ≫ (AffineCoordinates.groupSchemeIso G).inv.hom.hom :=
    algSpec.fullyFaithful.map_preimage _
  rw [hy, Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id]
  rfl

variable {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation (Corepresented.groupScheme (AffineCoordinates.functor G)
    (AffineCoordinates.corepresentation G)) n)

/-- The universal matrix consists of matrix coefficients for the Hopf comultiplication. -/
theorem comul_universalMatrix_hopf (i j : n) :
    Coalgebra.comul (R := k)
        (Unipotent.universalMatrix (AffineCoordinates.corepresentation G) ρ i j :
          AffineCoordinates.hopfAlgebra G) =
      ∑ l, (Unipotent.universalMatrix (AffineCoordinates.corepresentation G) ρ i l :
          AffineCoordinates.hopfAlgebra G) ⊗ₜ[k]
        (Unipotent.universalMatrix (AffineCoordinates.corepresentation G) ρ l j :
          AffineCoordinates.hopfAlgebra G) :=
  (LinearMap.congr_fun (AffineCoordinates.corepresentation_comul G) _).symm.trans
    (Unipotent.comul_universalMatrix _ ρ i j)

/-- The Hopf counit of the universal matrix is the identity matrix. -/
theorem counit_universalMatrix_hopf (i j : n) :
    Coalgebra.counit (R := k)
        (Unipotent.universalMatrix (AffineCoordinates.corepresentation G) ρ i j :
          AffineCoordinates.hopfAlgebra G) = (1 : Matrix n n k) i j :=
  (LinearMap.congr_fun (AffineCoordinates.corepresentation_counit G) _).symm.trans
    (Unipotent.counit_universalMatrix _ ρ i j)

end Coordinates

section Forward

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- Over the algebraic closure, a group of multiplicative type has a coordinate Hopf algebra
spanned by group-like elements after scalar extension. -/
theorem span_algebraicClosure_of_isMultiplicativeType (hM : IsMultiplicativeType G) :
    Submodule.span (AlgebraicClosure k)
      {a : AlgebraicClosure k ⊗[k] AffineCoordinates.hopfAlgebra G |
        IsGroupLikeElem (AlgebraicClosure k) a} = ⊤ := by
  have hMK := MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic k
    (AlgebraicClosure k) G hM
  obtain ⟨Λ, hΛ, hfg, ⟨d⟩⟩ := MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed _ hMK
  exact SplittingAssembly.span_of_hopfSpecIso
    (HopfCoordinates.scalarExtension k (AlgebraicClosure k) (AffineCoordinates.hopfAlgebra G))
    (Diagonalizable.hopfAlgebra (CommRingCat.of (AlgebraicClosure k)) Λ)
    (SplittingAssembly.scalarExtensionCoordinatesIso G ≪≫ d ≪≫
      (Diagonalizable.hopfSpecIso (CommRingCat.of (AlgebraicClosure k)) Λ).symm)
    AddMonoidAlgebra.span_isGroupLikeElem

/-- (⇒) Every geometric point of a group of multiplicative type acts semisimply in every
representation. -/
theorem isSemisimple_of_isMultiplicativeType (hM : IsMultiplicativeType G) {n : ℕ}
    (ρ : MatrixRepresentation G (Fin n))
    (x : (algSpec (CommRingCat.of k)).obj
      (op (CommAlgCat.of (CommRingCat.of k) (AlgebraicClosure k))) ⟶ G.X) :
    Module.End.IsSemisimple (Matrix.toLin'
      (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) (AlgebraicClosure k)) x :
        Matrix (Fin n) (Fin n) (AlgebraicClosure k))) := by
  rw [affineMatrix_eq_map_universalMatrix]
  exact isSemisimple_of_span_baseChange (span_algebraicClosure_of_isMultiplicativeType G hM)
    _ (comul_universalMatrix_hopf G _) (counit_universalMatrix_hopf G _) _

end Forward

section Backward

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- The algebraic-closure point of `G` classified by an algebra map out of its coordinate
Hopf algebra. -/
def closurePoint (f : AffineCoordinates.hopfAlgebra G →ₐ[k] AlgebraicClosure k) :
    (algSpec (CommRingCat.of k)).obj
      (op (CommAlgCat.of (CommRingCat.of k) (AlgebraicClosure k))) ⟶ G.X :=
  Unipotent.classifiedPoint (AffineCoordinates.corepresentation G)
      (CommAlgCat.ofHom f : AffineCoordinates.algebra G ⟶
        CommAlgCat.of (CommRingCat.of k) (AlgebraicClosure k)) ≫
    (AffineCoordinates.groupSchemeIso G).hom.hom.hom

variable {N : ℕ} (M : Matrix (Fin N) (Fin N) (AffineCoordinates.hopfAlgebra G))
  (hcomul : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
  (hcounit : ∀ i j, Coalgebra.counit (R := k) (M i j) = (1 : Matrix (Fin N) (Fin N) k) i j)

/-- The representation of `G` attached to a matrix of Hopf matrix coefficients. -/
def coefficientRepresentation : MatrixRepresentation G (Fin N) :=
  (AffineCoordinates.groupSchemeIso G).inv ≫
    AffineLinearEmbedding.toGLHom (AffineCoordinates.corepresentation G)
      (M : Matrix (Fin N) (Fin N) (AffineCoordinates.algebra G))
      (fun i j => (LinearMap.congr_fun (AffineCoordinates.corepresentation_comul G)
        (M i j)).trans (hcomul i j))
      (fun i j => (LinearMap.congr_fun (AffineCoordinates.corepresentation_counit G)
        (M i j)).trans (hcounit i j))

/-- At the point classified by `f`, the coefficient representation is `M` with `f` applied to
its entries. -/
theorem affineMatrix_coefficientRepresentation
    (f : AffineCoordinates.hopfAlgebra G →ₐ[k] AlgebraicClosure k) :
    ((coefficientRepresentation G M hcomul hcounit).affineMatrix
        (CommAlgCat.of (CommRingCat.of k) (AlgebraicClosure k)) (closurePoint G f) :
          Matrix (Fin N) (Fin N) (AlgebraicClosure k)) = M.map f := by
  ext i j
  rw [MatrixRepresentation.affineMatrix_apply]
  have hx : closurePoint G f ≫ (coefficientRepresentation G M hcomul hcounit).hom.hom =
      Unipotent.classifiedPoint (AffineCoordinates.corepresentation G)
          (CommAlgCat.ofHom f : AffineCoordinates.algebra G ⟶
            CommAlgCat.of (CommRingCat.of k) (AlgebraicClosure k)) ≫
        (AffineLinearEmbedding.toGLHom (AffineCoordinates.corepresentation G)
          (M : Matrix (Fin N) (Fin N) (AffineCoordinates.algebra G))
          (fun i j => (LinearMap.congr_fun (AffineCoordinates.corepresentation_comul G)
            (M i j)).trans (hcomul i j))
          (fun i j => (LinearMap.congr_fun (AffineCoordinates.corepresentation_counit G)
            (M i j)).trans (hcounit i j))).hom.hom := by
    simp only [closurePoint, coefficientRepresentation, Grp.comp_hom_hom, Category.assoc]
    rw [← Category.assoc (AffineCoordinates.groupSchemeIso G).hom.hom.hom, ← Grp.comp_hom_hom,
      Iso.hom_inv_id]
    rfl
  rw [hx]
  erw [Corepresented.groupSchemeMap_affinePoints, Corepresented.affinePointsEquiv_map]
  change ((AffineCoordinates.corepresentation G).homEquiv.symm
    ((AffineCoordinates.corepresentation G).homEquiv (CommAlgCat.ofHom f))).hom (M i j) = _
  rw [Equiv.symm_apply_apply]
  rfl

include hcomul hcounit in
/-- (⇐) If every geometric point acts semisimply in every representation, then the matrices
of coefficient representations at algebraic-closure points commute and are semisimple. -/
theorem commute_and_isSemisimple (hcomm : IsCommMonObj G.X)
    (hss : ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n))
      (x : (algSpec (CommRingCat.of k)).obj
          (op (CommAlgCat.of (CommRingCat.of k) (AlgebraicClosure k))) ⟶ G.X),
      Module.End.IsSemisimple (Matrix.toLin'
        (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) (AlgebraicClosure k)) x :
          Matrix (Fin n) (Fin n) (AlgebraicClosure k)))) :
    (∀ f f' : AffineCoordinates.hopfAlgebra G →ₐ[k] AlgebraicClosure k,
      Commute (M.map f) (M.map f')) ∧
      ∀ f : AffineCoordinates.hopfAlgebra G →ₐ[k] AlgebraicClosure k,
        Module.End.IsSemisimple (Matrix.toLin' (M.map f)) := by
  have := hcomm
  set ρ := coefficientRepresentation G M hcomul hcounit
  refine ⟨fun f f' => ?_, fun f => ?_⟩
  · rw [← affineMatrix_coefficientRepresentation G M hcomul hcounit f,
      ← affineMatrix_coefficientRepresentation G M hcomul hcounit f']
    have h := congrArg (fun g => (ρ.affineMatrix
      (CommAlgCat.of (CommRingCat.of k) (AlgebraicClosure k)) g :
        Matrix (Fin N) (Fin N) (AlgebraicClosure k))) (mul_comm (closurePoint G f)
          (closurePoint G f'))
    simp only [map_mul, Units.val_mul] at h
    exact h
  · rw [← affineMatrix_coefficientRepresentation G M hcomul hcounit f]
    exact hss N ρ _

end Backward

section Assembly

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
  [Smooth G.X.hom]

/-- (⇐) A smooth commutative affine group whose geometric points act semisimply in every
representation is of multiplicative type. -/
theorem isMultiplicativeType_of_isSemisimple (hcomm : IsCommMonObj G.X)
    (hss : ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n))
      (x : (algSpec (CommRingCat.of k)).obj
          (op (CommAlgCat.of (CommRingCat.of k) (AlgebraicClosure k))) ⟶ G.X),
      Module.End.IsSemisimple (Matrix.toLin'
        (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) (AlgebraicClosure k)) x :
          Matrix (Fin n) (Fin n) (AlgebraicClosure k)))) :
    IsMultiplicativeType G := by
  classical
  let K := AlgebraicClosure k
  let H := AffineCoordinates.hopfAlgebra G
  have : IsReduced (K ⊗[k] H) := AffineCoordinates.hopfAlgebraBaseChangeReduced G K
  have : Algebra.FiniteType K (K ⊗[k] H) := AffineCoordinates.hopfAlgebraBaseChange_finiteType G K
  have hspan : Submodule.span K {c : K ⊗[k] H | IsGroupLikeElem K c} = ⊤ := by
    refine span_baseChange_of_isSemisimple (k := k) (H := H) (K := K) (fun b => ?_)
      (fun N M hcomul hcounit => commute_and_isSemisimple G M hcomul hcounit hcomm hss)
    obtain ⟨N, M, hcomul, hcounit, hb⟩ :=
      AffineLinearEmbedding.exists_matrix_coefficients (K := k) ({b} : Finset H)
    exact ⟨N, M, hcomul, hcounit, hb (Finset.mem_singleton_self b)⟩
  let eRec : (K ⊗[k] H) ≃ₐc[K] AddMonoidAlgebra K (Additive (GroupLike K (K ⊗[k] H))) :=
    (Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike hspan).symm.trans
      (MonoidAlgebra.toAdditiveBialgEquiv K K (GroupLike K (K ⊗[k] H)))
  refine ⟨K, inferInstance, inferInstance, Additive (GroupLike K (K ⊗[k] H)), inferInstance,
    addGroupFG_groupLike hspan, ⟨?_⟩⟩
  exact (SplittingAssembly.scalarExtensionCoordinatesIso G).symm ≪≫
    ((hopfSpec (CommRingCat.of K)).mapIso (CommHopfAlgCat.isoMk eRec).op).symm ≪≫
    Diagonalizable.hopfSpecIso (CommRingCat.of K) (Additive (GroupLike K (K ⊗[k] H)))

end Assembly

end SemisimplePoints

/-- **Milne, Corollary 12.21.** A smooth commutative affine group scheme over a field is of
multiplicative type if and only if every point with values in the algebraic closure acts by a
semisimple matrix in every representation. -/
theorem multiplicativeTypeSemisimplePoints : MultiplicativeTypeSemisimplePointsStatement.{u} := by
  intro k _ G _ _ hcomm
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact ⟨fun hM n ρ x => SemisimplePoints.isSemisimple_of_isMultiplicativeType G hM ρ x,
    SemisimplePoints.isMultiplicativeType_of_isSemisimple G hcomm⟩

end Langlands.GroupScheme
