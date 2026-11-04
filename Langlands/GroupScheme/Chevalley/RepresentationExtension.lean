import Langlands.GroupScheme.Chevalley.RegularQuotient
import Langlands.GroupScheme.Chevalley.ReindexRepresentation
import Langlands.GroupScheme.Chevalley.ActualLineStabilizer

/-! # Actual ambient representation subquotients for closed subgroups -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra Module
open scoped Matrix Kronecker CategoryTheory.MonObj

namespace Langlands.GroupScheme.Chevalley

open AffineLinearEmbedding MatrixRepresentation

section Coordinates

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n m I J P Q : Type}
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

/-- Apply a matrix independently to each of finitely many copies. -/
def copyMatrix (C : Matrix m n k) : Matrix (m × I) (n × I) k :=
  C ⊗ₖ (1 : Matrix I I k)

omit [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype J] [DecidableEq J]
  [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem copyMatrix_mulVec (C : Matrix m n k) (v : n × I → k) (i : m) (t : I) :
    (copyMatrix (I := I) C *ᵥ v) (i, t) = ∑ j, C i j * v (j, t) := by
  classical
  simp [copyMatrix, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.one_apply]

omit [Fintype m] [DecidableEq m] [Fintype J] [DecidableEq J]
  [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem tensor_trivial_affineMatrix (ρ : MatrixRepresentation G n)
    (S : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶ G.X) :
    ((ρ.tensor (trivial G I)).affineMatrix S x : Matrix (n × I) (n × I) S) =
      (ρ.affineMatrix S x : Matrix n n S) ⊗ₖ (1 : Matrix I I S) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  calc
    _ = ρ.affineMatrix S x a c * (trivial G I).affineMatrix S x b d :=
      tensor_affineMatrix_entry ρ (trivial G I) S x a c b d
    _ = _ := by rw [trivial_affineMatrix]; rfl

omit [Fintype J] [DecidableEq J] [Fintype P] [DecidableEq P]
  [Fintype Q] [DecidableEq Q] in
/-- Finite copies preserve an actual intertwiner. -/
theorem intertwines_copyMatrix (ρ : MatrixRepresentation G n)
    (σ : MatrixRepresentation G m) (C : Matrix m n k)
    (hC : Intertwines ρ σ C) :
    Intertwines (ρ.tensor (trivial G I)) (σ.tensor (trivial G I))
      (copyMatrix (I := I) C) := by
  intro S x
  rw [tensor_trivial_affineMatrix, tensor_trivial_affineMatrix]
  ext ⟨i, t⟩ ⟨j, s⟩
  have h := congrArg (fun M : Matrix m n S => M i j) (hC S x)
  by_cases hts : t = s
  · subst s
    simpa [copyMatrix, Matrix.mul_apply, Matrix.map_apply,
      Fintype.sum_prod_type, Matrix.one_apply] using h
  · simp [copyMatrix, Matrix.mul_apply, Matrix.map_apply,
      Fintype.sum_prod_type, Matrix.one_apply, hts]

omit [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype J] [DecidableEq J]
  [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
/-- A surjection remains surjective on finitely many copies. -/
theorem copyMatrix_surjective (C : Matrix m n k)
    (hs : Function.Surjective C.mulVecLin) :
    Function.Surjective (copyMatrix (I := I) C).mulVecLin := by
  classical
  intro y
  choose v hv using fun t : I => hs (fun i => y (i, t))
  refine ⟨fun jt => v jt.2 jt.1, ?_⟩
  funext ⟨i, t⟩
  change (copyMatrix C *ᵥ _) (i, t) = _
  rw [copyMatrix_mulVec]
  exact congrFun (hv t) i

omit [Fintype m] [DecidableEq m] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype P] [DecidableEq P]
  [Fintype Q] [DecidableEq Q] in
/-- The trivial representation commutes with restriction. -/
theorem trivial_restrict (f : H ⟶ G) :
    (trivial G n).restrict f = trivial H n := by
  apply Grp.hom_ext
  change f.hom.hom ≫ (CartesianMonoidalCategory.toUnit G.X ≫ η[_]) =
    CartesianMonoidalCategory.toUnit H.X ≫ η[_]
  rw [← Category.assoc, CartesianMonoidalCategory.comp_toUnit]

omit [Fintype m] [DecidableEq m] [Fintype I] [DecidableEq I]
  [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
/-- Reindexing of an actual representation acts entrywise on affine matrices. -/
theorem reindexRepresentation_affineMatrix (e : n ≃ J)
    (ρ : MatrixRepresentation G n) (S : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶ G.X) :
    (reindexRepresentation e (CommRingCat.of k) ρ).affineMatrix S x =
      reindexGL e (ρ.affineMatrix S x) := by
  exact Corepresented.groupSchemeMap_affinePoints
    (GeneralLinear.corepresentableBy n (CommRingCat.of k))
    (GeneralLinear.corepresentableBy J (CommRingCat.of k))
    (reindexNat e (CommRingCat.of k)) (x ≫ ρ.hom.hom)

omit [Fintype I] [DecidableEq I] [Fintype Q] [DecidableEq Q] in
/-- Reindex both sides of an actual intertwiner by arbitrary finite equivalences. -/
theorem intertwines_reindex (e : n ≃ J) (f : m ≃ P)
    (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
    (C : Matrix m n k) (hC : Intertwines ρ σ C) :
    Intertwines (reindexRepresentation e (CommRingCat.of k) ρ)
      (reindexRepresentation f (CommRingCat.of k) σ) (Matrix.reindex f e C) := by
  intro S x
  rw [reindexRepresentation_affineMatrix, reindexRepresentation_affineMatrix]
  change (C.map (algebraMap k S)).submatrix f.symm e.symm *
      (ρ.affineMatrix S x : Matrix n n S).submatrix e.symm e.symm =
    (σ.affineMatrix S x : Matrix m m S).submatrix f.symm f.symm *
      (C.map (algebraMap k S)).submatrix f.symm e.symm
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hC S x]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype Q] [DecidableEq Q] in
/-- Reindex just the target of an actual intertwiner. -/
theorem intertwines_reindex_target (f : m ≃ P)
    (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
    (C : Matrix m n k) (hC : Intertwines ρ σ C) :
    Intertwines ρ (reindexRepresentation f (CommRingCat.of k) σ)
      (Matrix.reindex f (Equiv.refl n) C) := by
  intro S x
  rw [reindexRepresentation_affineMatrix]
  change (C.map (algebraMap k S)).submatrix f.symm (Equiv.refl n) *
      (ρ.affineMatrix S x : Matrix n n S).submatrix (Equiv.refl n) (Equiv.refl n) =
    (σ.affineMatrix S x : Matrix m m S).submatrix f.symm f.symm *
      (C.map (algebraMap k S)).submatrix f.symm (Equiv.refl n)
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hC S x]

omit [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype I] [DecidableEq I]
  [DecidableEq J] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
/-- Reindexing preserves injectivity of a coordinate matrix. -/
theorem reindexMatrix_injective (e : n ≃ J) (f : m ≃ P)
    (C : Matrix m n k) (hi : Function.Injective C.mulVecLin) :
    Function.Injective (Matrix.reindex f e C).mulVecLin := by
  rw [Matrix.mulVecLin_reindex]
  exact (LinearEquiv.funCongrLeft k k f.symm).injective.comp
    (hi.comp (LinearEquiv.funCongrLeft k k e).injective)

omit [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype I] [DecidableEq I]
  [DecidableEq J] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
/-- Reindexing preserves surjectivity of a coordinate matrix. -/
theorem reindexMatrix_surjective (e : n ≃ J) (f : m ≃ P)
    (C : Matrix m n k) (hs : Function.Surjective C.mulVecLin) :
    Function.Surjective (Matrix.reindex f e C).mulVecLin := by
  rw [Matrix.mulVecLin_reindex]
  exact (LinearEquiv.funCongrLeft k k f.symm).surjective.comp
    (hs.comp (LinearEquiv.funCongrLeft k k e).surjective)

omit [Fintype m] [DecidableEq m] [Fintype I] [DecidableEq I]
  [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
/-- Coordinate reindexing commutes with restriction. -/
theorem reindexRepresentation_restrict (e : n ≃ J)
    (ρ : MatrixRepresentation G n) (f : H ⟶ G) :
    (reindexRepresentation e (CommRingCat.of k) ρ).restrict f =
      reindexRepresentation e (CommRingCat.of k) (ρ.restrict f) :=
  (Category.assoc f ρ (reindexGroupHom e (CommRingCat.of k))).symm

end Coordinates

section Corepresented

variable {k : Type u} [Field k]
  {F H : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B C : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (d : (H ⋙ forget GrpCat).CorepresentableBy C) (α : H ⟶ F)

/-- Every representation of an actual corepresented closed subgroup is a
subquotient of a restricted actual ambient representation. -/
theorem exists_corepresented_ambient_subquotient
    (hc : IsClosedSubgroup (Corepresented.groupSchemeMap d e α))
    {n : ℕ} (σ : MatrixRepresentation (Corepresented.groupScheme H d) (Fin n)) :
    ∃ (m : ℕ) (ρ : MatrixRepresentation (Corepresented.groupScheme F e) (Fin m)),
      IsSubquotientOf σ (ρ.restrict (Corepresented.groupSchemeMap d e α)) := by
  classical
  have : IsAffineHom (Corepresented.groupScheme H d).X.hom := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k C)))
    infer_instance
  let := (bialgebra e).toCoalgebra
  let := (bialgebra d).toCoalgebra
  obtain ⟨V, hfinite, hV, hN⟩ := exists_finite_regular_lift e d α hc
    (fun ij : Fin n × Fin n => Unipotent.universalMatrix d σ ij.1 ij.2)
  let := hfinite
  let W := V.map (coordinateRestriction e d α).toLinearMap
  have hW : ∀ (f : Module.Dual k C) (v : C), v ∈ W → rightAct f v ∈ W :=
    fun f _ hv => rightAct_mem_map
      (coordinateRestrictionBialgHom e d α).toCoalgHom V hV f hv
  let bV := Module.finBasis k V
  let bW := Module.finBasis k W
  let ρV := regularRepresentation e (Field.toIsField k) V bV hV
  let ρW := regularRepresentation d (Field.toIsField k) W bW hW
  let ρ₀ := ρV.tensor (trivial (Corepresented.groupScheme F e) (Fin n))
  let π₀ := ρW.tensor (trivial (Corepresented.groupScheme H d) (Fin n))
  let E := coefficientEmbedding d σ W bW
  have hcoeff : ∀ i j, Unipotent.universalMatrix d σ i j ∈ W :=
    fun i j => hN (i, j)
  have hE : Intertwines σ π₀ E :=
    intertwines_coefficientEmbedding d σ W bW hW hcoeff
  have hiE : Function.Injective E.mulVecLin :=
    coefficientEmbedding_injective d σ W bW hcoeff
  let Q := regularQuotientMatrix (coordinateRestriction e d α).toLinearMap V bV W bW
  have hQ : Intertwines (ρV.restrict (Corepresented.groupSchemeMap d e α)) ρW Q :=
    intertwines_regularQuotient e d α V bV W bW hV hW le_rfl
  have hsQ : Function.Surjective Q.mulVecLin :=
    regularQuotientMatrix_surjective (coordinateRestriction e d α).toLinearMap
      V bV W bW rfl
  have hcopies : Intertwines
      (ρ₀.restrict (Corepresented.groupSchemeMap d e α)) π₀
      (copyMatrix (I := Fin n) Q) := by
    dsimp only [ρ₀, π₀]
    rw [← tensor_restrict, trivial_restrict]
    exact intertwines_copyMatrix _ _ Q hQ
  let eV := Fintype.equivFin (Fin (Module.finrank k V) × Fin n)
  let eW := Fintype.equivFin (Fin (Module.finrank k W) × Fin n)
  let ρ := reindexRepresentation eV (CommRingCat.of k) ρ₀
  let π := reindexRepresentation eW (CommRingCat.of k) π₀
  refine ⟨_, ρ, isSubquotientOf_of_common_quotient
    (ρ.restrict (Corepresented.groupSchemeMap d e α)) σ π
    (Matrix.reindex eW eV (copyMatrix (I := Fin n) Q))
    (Matrix.reindex eW (Equiv.refl (Fin n)) E) ?_ ?_ ?_ ?_⟩
  · rw [reindexRepresentation_restrict]
    exact intertwines_reindex eV eW _ _ _ hcopies
  · exact reindexMatrix_surjective eV eW _ (copyMatrix_surjective Q hsQ)
  · exact intertwines_reindex_target eW σ π₀ E hE
  · exact reindexMatrix_injective (Equiv.refl (Fin n)) eW E hiE

end Corepresented

end Langlands.GroupScheme.Chevalley
