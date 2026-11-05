import Langlands.GroupScheme.MatrixRepresentation.NormalCharacterSpan
import Langlands.GroupScheme.MatrixRepresentationConjugate
import Langlands.GroupScheme.Reductive.GeneralLinearDiagonal
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Closed split-torus embeddings from spanning character spaces -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Module CategoryTheory.MonoidalCategory
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Spanning character spaces admit a basis consisting of character vectors. -/
theorem exists_characterBasis (ρ : MatrixRepresentation G n)
    (hspan : ρ.characterSpan = ⊤) :
    ∃ (b : Basis n k (n → k)) (χ : n → rationalCharacters G),
      ∀ j, b j ∈ ρ.characterSpace (χ j) := by
  let S : Set (n → k) := ⋃ χ, (ρ.characterSpace χ : Set (n → k))
  have hS : Submodule.span k S = ⊤ := by
    simpa only [S, Submodule.span_iUnion, Submodule.span_eq, characterSpan] using hspan
  obtain ⟨t, ht, hst, hli⟩ := exists_linearIndependent k S
  have htop : ⊤ ≤ Submodule.span k (Set.range (Subtype.val : t → n → k)) := by
    simp only [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hst, hS, le_refl]
  let b₀ := Basis.mk hli htop
  let e := b₀.indexEquiv (Pi.basisFun k n)
  let b := b₀.reindex e
  have hb (j : n) : b j ∈ S := by
    rw [show b j = ((e.symm j : t) : n → k) by
      simp only [b, Basis.reindex_apply, b₀, Basis.mk_apply]]
    exact ht (e.symm j).property
  have hc (j : n) : ∃ χ, b j ∈ ρ.characterSpace χ := Set.mem_iUnion.mp (hb j)
  choose χ hχ using hc
  exact ⟨b, χ, hχ⟩

/-- The invertible matrix sending a vector to its coordinates in the chosen basis. -/
def basisCoordinateGL (b : Basis n k (n → k)) : GL n k where
  val := b.toMatrix (Pi.basisFun k n)
  inv := (Pi.basisFun k n).toMatrix b
  val_inv := Basis.toMatrix_mul_toMatrix_flip _ _
  inv_val := Basis.toMatrix_mul_toMatrix_flip _ _

/-- The corresponding constant change of coordinates as an actual point of `GL`. -/
def basisCoordinatePoint (b : Basis n k (n → k)) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (GeneralLinear.groupScheme n (CommRingCat.of k)).X :=
  (GeneralLinear.pointsEquiv n (CommRingCat.of k) _).symm
    (Matrix.GeneralLinearGroup.map
      (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k))))) (basisCoordinateGL b))

theorem rationalMatrix_basisCoordinatePoint (b : Basis n k (n → k)) :
    (standard n (CommRingCat.of k)).rationalMatrix (basisCoordinatePoint b) =
      basisCoordinateGL b := by
  change Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    (GeneralLinear.pointsEquiv n (CommRingCat.of k) _
      (basisCoordinatePoint b ≫ 𝟙 _)) = _
  rw [Category.comp_id, basisCoordinatePoint, MulEquiv.apply_symm_apply]
  apply Units.ext
  ext r s
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ((basisCoordinateGL b : Matrix n n k) r s)) = _
  simp

/-- In a character basis the conjugate matrix is diagonal over every test
algebra, including nonreduced ones. -/
theorem conjugate_basisCoordinatePoint_affineMatrix (ρ : MatrixRepresentation G n)
    (b : Basis n k (n → k)) (χ : n → rationalCharacters G)
    (hb : ∀ j, b j ∈ ρ.characterSpace (χ j))
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A) :
    ((ρ.conjugate (basisCoordinatePoint b)).affineMatrix A x : Matrix n n A) =
      Matrix.diagonal (fun j =>
        (Gm.affineUnitsEquiv (CommRingCat.of k) A (x ≫ (χ j).toMul.hom.hom) : A)) := by
  let U := Matrix.GeneralLinearGroup.map (algebraMap k A) (basisCoordinateGL b)
  let D : Matrix n n A := Matrix.diagonal (fun j =>
    (Gm.affineUnitsEquiv (CommRingCat.of k) A (x ≫ (χ j).toMul.hom.hom) : A))
  have hcol :
      (ρ.affineMatrix A x : Matrix n n A) * (↑U⁻¹ : Matrix n n A) =
        (↑U⁻¹ : Matrix n n A) * D := by
    ext r s
    have he := congrFun (characterSpace_affine (hb s) A x) r
    rw [Matrix.mul_diagonal]
    change ((ρ.affineMatrix A x : Matrix n n A) *ᵥ
        (fun t => algebraMap k A (b s t))) r =
      algebraMap k A (b s r) *
        (Gm.affineUnitsEquiv (CommRingCat.of k) A (x ≫ (χ s).toMul.hom.hom) : A)
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using he
  rw [conjugate_affineMatrix, affineMatrix_constantPoint,
    rationalMatrix_basisCoordinatePoint]
  change (↑U : Matrix n n A) * (ρ.affineMatrix A x : Matrix n n A) *
      (↑U⁻¹ : Matrix n n A) = D
  rw [Matrix.mul_assoc, hcol, ← Matrix.mul_assoc, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.one_mul]

/-- A representation diagonal at the universal affine point factors through
the diagonal torus on the underlying relative schemes. -/
def universalDiagonalFactorOver (ρ : MatrixRepresentation G n)
    (hρ : GeneralLinear.IsDiagonalGL
      (ρ.affineMatrix (CharacterUnits.Coord G) (CharacterUnits.universalPoint G))) :
    G.X ⟶ (splitTorus (Spec (CommRingCat.of k)) (ULift.{u} n)).X :=
  (Lie.coordinateIso G).inv ≫
    GeneralLinear.diagonalLocusLift
      (CharacterUnits.universalPoint G ≫ ρ.hom.hom) (by
        rw [GeneralLinear.pointsEquiv_eq_affinePointsEquiv]
        exact hρ.map _) ≫
    GeneralLinear.locusToDiagonalTorus n (CommRingCat.of k)

theorem universalDiagonalFactorOver_comp (ρ : MatrixRepresentation G n)
    (hρ : GeneralLinear.IsDiagonalGL
      (ρ.affineMatrix (CharacterUnits.Coord G) (CharacterUnits.universalPoint G))) :
    universalDiagonalFactorOver ρ hρ ≫
      (GeneralLinear.diagonalTorus n (CommRingCat.of k)).hom.hom = ρ.hom.hom := by
  simp only [universalDiagonalFactorOver, Category.assoc,
    GeneralLinear.locusToDiagonalTorus_comp, GeneralLinear.diagonalLocusLift_comp,
    CharacterUnits.universalPoint_eq, Iso.inv_hom_id_assoc]

/-- The universal diagonal factor respects the group law, since the diagonal
torus inclusion is a monomorphism. -/
def universalDiagonalFactor (ρ : MatrixRepresentation G n)
    (hρ : GeneralLinear.IsDiagonalGL
      (ρ.affineMatrix (CharacterUnits.Coord G) (CharacterUnits.universalPoint G))) :
    G ⟶ (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift.{u} n)).toGrp := by
  let f := universalDiagonalFactorOver ρ hρ
  let j := GeneralLinear.diagonalTorus n (CommRingCat.of k)
  have hf : f ≫ j.hom.hom = ρ.hom.hom := universalDiagonalFactorOver_comp ρ hρ
  letI : IsMonHom f := {
    one_hom := by
      apply (cancel_mono j.hom.hom).mp
      rw [Category.assoc, hf, IsMonHom.one_hom, IsMonHom.one_hom]
    mul_hom := by
      apply (cancel_mono j.hom.hom).mp
      rw [Category.assoc, hf, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
        tensorHom_comp_tensorHom_assoc, hf] }
  exact Grp.homMk f

theorem universalDiagonalFactor_comp (ρ : MatrixRepresentation G n)
    (hρ : GeneralLinear.IsDiagonalGL
      (ρ.affineMatrix (CharacterUnits.Coord G) (CharacterUnits.universalPoint G))) :
    universalDiagonalFactor ρ hρ ≫ GeneralLinear.diagonalTorus n (CommRingCat.of k) = ρ :=
  Grp.hom_ext _ _ (universalDiagonalFactorOver_comp ρ hρ)

/-- If the diagonal representation is a closed immersion, its factor through
the diagonal torus is a closed immersion as well. -/
theorem isClosedSubgroup_universalDiagonalFactor (ρ : MatrixRepresentation G n)
    (hρ : GeneralLinear.IsDiagonalGL
      (ρ.affineMatrix (CharacterUnits.Coord G) (CharacterUnits.universalPoint G)))
    (hclosed : IsClosedSubgroup ρ) :
    IsClosedSubgroup (universalDiagonalFactor ρ hρ) := by
  have hcomp := congrArg (fun f => f.hom.hom.left) (universalDiagonalFactor_comp ρ hρ)
  change (universalDiagonalFactor ρ hρ).hom.hom.left ≫
    (GeneralLinear.diagonalTorus n (CommRingCat.of k)).hom.hom.left =
      ρ.hom.hom.left at hcomp
  have : IsClosedImmersion ((universalDiagonalFactor ρ hρ).hom.hom.left ≫
      (GeneralLinear.diagonalTorus n (CommRingCat.of k)).hom.hom.left) := by
    rw [hcomp]
    exact hclosed
  have : IsClosedImmersion
      (GeneralLinear.diagonalTorus n (CommRingCat.of k)).hom.hom.left :=
    GeneralLinear.isClosedSubgroup_diagonalTorus n _
  exact IsClosedImmersion.of_comp_isClosedImmersion
    (universalDiagonalFactor ρ hρ).hom.hom.left
    (GeneralLinear.diagonalTorus n (CommRingCat.of k)).hom.hom.left

/-- The split-torus morphism obtained by choosing a basis of character vectors. -/
def characterSpanEmbedding (ρ : MatrixRepresentation G n) (hspan : ρ.characterSpan = ⊤) :
    G ⟶ (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift.{u} n)).toGrp := by
  let b := Classical.choose (exists_characterBasis ρ hspan)
  let χ := Classical.choose (Classical.choose_spec (exists_characterBasis ρ hspan))
  have hb : ∀ j, b j ∈ ρ.characterSpace (χ j) :=
    Classical.choose_spec (Classical.choose_spec (exists_characterBasis ρ hspan))
  apply universalDiagonalFactor (ρ.conjugate (basisCoordinatePoint b))
  intro r s hrs
  rw [conjugate_basisCoordinatePoint_affineMatrix ρ b χ hb]
  exact Matrix.diagonal_apply_ne _ hrs

/-- The constructed torus morphism recovers the conjugate representation. -/
theorem characterSpanEmbedding_comp (ρ : MatrixRepresentation G n)
    (hspan : ρ.characterSpan = ⊤) :
    characterSpanEmbedding ρ hspan ≫ GeneralLinear.diagonalTorus n (CommRingCat.of k) =
      ρ.conjugate (basisCoordinatePoint (Classical.choose (exists_characterBasis ρ hspan))) :=
  universalDiagonalFactor_comp _ _

/-- A closed finite matrix representation spanned by character vectors gives
a closed immersion into a split torus, with no smoothness assumption. -/
theorem isClosedSubgroup_characterSpanEmbedding (ρ : MatrixRepresentation G n)
    (hspan : ρ.characterSpan = ⊤) (hclosed : IsClosedSubgroup ρ) :
    IsClosedSubgroup (characterSpanEmbedding ρ hspan) := by
  apply isClosedSubgroup_universalDiagonalFactor
  have : IsClosedImmersion ρ.hom.hom.left := hclosed
  have : IsIso
      ((GeneralLinear.groupScheme n (CommRingCat.of k)).innerIso
        (basisCoordinatePoint (Classical.choose (exists_characterBasis ρ hspan)))).hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map
      ((GeneralLinear.groupScheme n (CommRingCat.of k)).innerIso
        (basisCoordinatePoint (Classical.choose (exists_characterBasis ρ hspan)))).hom.hom.hom))
  change IsClosedImmersion (ρ.hom.hom.left ≫ _)
  infer_instance

/-- The existence form of the construction, for consumers that do not need
the selected character basis or factorization. -/
theorem exists_closed_splitTorus_embedding_of_characterSpan (ρ : MatrixRepresentation G n)
    (hspan : ρ.characterSpan = ⊤) (hclosed : IsClosedSubgroup ρ) :
    ∃ j : G ⟶ (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift.{u} n)).toGrp,
      IsClosedSubgroup j :=
  ⟨characterSpanEmbedding ρ hspan, isClosedSubgroup_characterSpanEmbedding ρ hspan hclosed⟩

end Langlands.GroupScheme.MatrixRepresentation
