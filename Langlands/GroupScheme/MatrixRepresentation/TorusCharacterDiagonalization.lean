import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.MatrixRepresentation.CharacterSpanEmbedding
import Langlands.GroupScheme.MatrixRepresentation.CoordinateLineWeightPositivity
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OppositeUnipotentDisplacement

/-! # Simultaneous torus-character diagonalization

One fixed coordinate change diagonalizes every cocharacter of a split torus.
The diagonal exponents are the actual integral lattice pairings.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- A representation restricts to the displayed diagonal algebraic characters
of the torus, on every coefficient algebra. -/
def HasTorusCharacterDiagonal (ρ : MatrixRepresentation G n)
    (i : T.toGrp ⟶ G) (χ : n → rationalCharacters T.toGrp) : Prop :=
  ∀ (A : CommAlgCat.{u} (CommRingCat.of k)) (x : GroupScheme.affinePoints T.toGrp A),
    (ρ.affineMatrix A (x ≫ i.hom.hom) : Matrix n n A) =
      Matrix.diagonal (fun j =>
        (Gm.affineUnitsEquiv (CommRingCat.of k) A (x ≫ (χ j).toMul.hom.hom) : A))

/-- A single constant coordinate change diagonalizes the whole split torus. -/
theorem exists_hasTorusCharacterDiagonal
    (ρ : MatrixRepresentation G n) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) :
    ∃ (q : rationalPoints (GeneralLinear.groupScheme n (CommRingCat.of k)))
      (χ : n → rationalCharacters T.toGrp),
      HasTorusCharacterDiagonal (ρ.conjugate q) i χ := by
  let : IsAffineHom T.X.hom := hT.isAffineHom
  obtain ⟨b, χ, hb⟩ := exists_characterBasis (ρ.restrict i)
    (iSup_characterSpace_eq_top_of_isSplitTorus hT (ρ.restrict i))
  refine ⟨basisCoordinatePoint b, χ, ?_⟩
  intro A x
  exact conjugate_basisCoordinatePoint_affineMatrix (ρ.restrict i) b χ hb A x

/-- The actual diagonal characters determine every cocharacter composite
in the same fixed coordinates. -/
theorem HasTorusCharacterDiagonal.cocharacter
    {ρ : MatrixRepresentation G n} {i : T.toGrp ⟶ G}
    {χ : n → rationalCharacters T.toGrp}
    (h : HasTorusCharacterDiagonal ρ i χ) (c : cocharacterLattice T) :
    CommGroupScheme.groupHom c ≫ i ≫ ρ =
      GeneralLinear.diagonalCocharacter n (CommRingCat.of k)
        (fun j => latticePairing T ((rationalCharacters.equivCharacterLattice T) (χ j)) c) := by
  let R := CommRingCat.of k
  let A := CommAlgCat.of R (LaurentPolynomial k)
  let Z := (algSpec R).obj (op A)
  let x : Z ⟶ (Gm (Spec R)).X := Gm.universalPoint R
  apply Gm.hom_ext_universalPoint R
  apply (GeneralLinear.affinePointsEquiv n R A).injective
  rw [GeneralLinear.CocharacterDiagonal.affinePointsEquiv_diagonalCocharacter]
  apply Units.ext
  change (ρ.affineMatrix A ((x ≫ (CommGroupScheme.groupHom c).hom.hom) ≫ i.hom.hom) :
      Matrix n n A) = _
  rw [h A (x ≫ (CommGroupScheme.groupHom c).hom.hom)]
  apply congrArg Matrix.diagonal
  funext j
  let α := (rationalCharacters.equivCharacterLattice T) (χ j)
  have he :
      (x ≫ (CommGroupScheme.groupHom c).hom.hom) ≫ (χ j).toMul.hom.hom =
        x ^ latticePairing T α c := by
    rw [Category.assoc]
    change x ≫ (CommGroupScheme.groupHom (c ≫ α)).hom.hom = _
    conv_lhs => rw [← (gmEndEquiv k).symm_apply_apply (c ≫ α)]
    rw [gmEndEquiv_symm_comp, latticePairing_apply]
  rw [he, map_zpow]
  rfl

/-- In these same fixed coordinates, every intrinsic uniformizer-section
point is the diagonal matrix of the corresponding integral pairing powers. -/
theorem HasTorusCharacterDiagonal.latticeSection
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ρ : MatrixRepresentation G n} {i : T.toGrp ⟶ G}
    {χ : n → rationalCharacters T.toGrp}
    (h : HasTorusCharacterDiagonal ρ i χ) (c : cocharacterLattice T) :
    ρ.rationalMatrix (rationalPoints.map i
      (CocharacterUniformizer.latticeSection k T (Multiplicative.ofAdd c))) =
      GeneralLinear.diagonalUnits k
        (fun j => latticePairing T ((rationalCharacters.equivCharacterLattice T) (χ j)) c)
        (SplitTorusValuation.uniformizerUnit k) := by
  have hc : (CommGroupScheme.groupHom c ≫ i) ≫ ρ =
      GeneralLinear.diagonalCocharacter n (CommRingCat.of k)
        (fun j => latticePairing T ((rationalCharacters.equivCharacterLattice T) (χ j)) c) :=
    (Category.assoc _ _ _).trans (h.cocharacter c)
  have he := rationalMatrix_gmRationalPoint_comp hc (SplitTorusValuation.uniformizerUnit k)
  change ρ.rationalMatrix
    ((gmRationalPoint (SplitTorusValuation.uniformizerUnit k) ≫
      (CommGroupScheme.groupHom c).hom.hom) ≫ i.hom.hom) = _
  rw [Category.assoc]
  exact he

end Langlands.GroupScheme.MatrixRepresentation
