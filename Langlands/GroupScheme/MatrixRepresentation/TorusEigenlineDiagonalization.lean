import Langlands.GroupScheme.MatrixRepresentation.CoordinateLineWeightPositivity
import Langlands.GroupScheme.MatrixRepresentation.TorusCharacterDiagonalization
import Langlands.GroupScheme.Rational.RankOneStandardParabolicLineCharacter

/-! # Simultaneous torus diagonalization retaining an actual coordinate eigenline -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- A prescribed nonzero universal character vector can be retained in
a basis consisting entirely of universal character vectors. -/
theorem exists_characterBasis_containing [IsAffineHom G.X.hom]
    (ρ : MatrixRepresentation G n) (hspan : ρ.characterSpan = ⊤)
    (χv : rationalCharacters G) (v : n → k) (hv : v ≠ 0)
    (hχv : v ∈ ρ.characterSpace χv) :
    ∃ (b : Module.Basis n k (n → k)) (χ : n → rationalCharacters G) (a : n),
      b a = v ∧ χ a = χv ∧ ∀ j, b j ∈ ρ.characterSpace (χ j) := by
  classical
  let S : Set (n → k) := ⋃ χ, (ρ.characterSpace χ : Set (n → k))
  have hS : Submodule.span k S = ⊤ := by
    simpa only [S, Submodule.span_iUnion, Submodule.span_eq, characterSpan] using hspan
  have hli : LinearIndepOn k id {v} := (linearIndepOn_singleton_iff k).mpr hv
  have hsub : ({v} : Set (n → k)) ⊆ S :=
    Set.singleton_subset_iff.mpr (Set.mem_iUnion.mpr ⟨χv, hχv⟩)
  have htop : ⊤ ≤ Submodule.span k S := hS.ge
  let b₀ := Module.Basis.extendLe hli hsub htop
  let e := b₀.indexEquiv (Pi.basisFun k n)
  let b := b₀.reindex e
  have hbS (j : n) : b j ∈ S := by
    apply Module.Basis.extendLe_subset hli hsub htop
    exact ⟨e.symm j, (b₀.reindex_apply e j).symm⟩
  obtain ⟨a₀, ha₀⟩ :=
    Module.Basis.subset_extendLe hli hsub htop (Set.mem_singleton v)
  let a := e a₀
  have ha : b a = v := by
    simpa only [b, a, Module.Basis.reindex_apply, Equiv.symm_apply_apply] using ha₀
  have hex : ∀ j : n, ∃ χ, b j ∈ ρ.characterSpace χ :=
    fun j => Set.mem_iUnion.mp (hbS j)
  choose χ hχ using hex
  refine ⟨b, Function.update χ a χv, a, ha, by simp, ?_⟩
  intro j
  by_cases hj : j = a
  · subst j
    simpa only [Function.update_self, ha] using hχv
  · simpa only [Function.update_of_ne hj] using hχ j

/-- The character-basis point is the usual rational matrix point of its
coordinate matrix. -/
theorem basisCoordinatePoint_eq_rationalMatrixPoint
    (b : Module.Basis n k (n → k)) :
    basisCoordinatePoint b =
      GeneralLinear.CocharacterDiagonal.rationalMatrixPoint (basisCoordinateGL b) := by
  let : Mono (standard n (CommRingCat.of k)).hom.hom := by
    change Mono (𝟙 (GeneralLinear.groupScheme n (CommRingCat.of k)).X)
    infer_instance
  apply rationalMatrix_injective (standard n (CommRingCat.of k))
  rw [rationalMatrix_basisCoordinatePoint, standard_rationalMatrix_rationalMatrixPoint]

/-- One simultaneous torus diagonalization can preserve the originally
chosen coordinate eigenline, in the all-test sense. -/
theorem exists_torusDiagonal_retaining_coordinateLine
    (ρ : MatrixRepresentation G n) (i : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (j : n)
    (hline : (ρ.restrict i).PreservesCoordinateLine j) :
    ∃ (B : GL n k) (a : n) (χ : n → rationalCharacters T.toGrp),
      IsCoordinateLineBasis B a j ∧
      (ρ.basisConjugate B).HasTorusCharacterDiagonal i χ := by
  classical
  let : IsAffineHom T.X.hom := hT.isAffineHom
  let χv := (ρ.restrict i).coordinateLineRationalCharacter j hline
  have hv : (Pi.single j (1 : k) : n → k) ≠ 0 := by
    intro hz
    have h := congrFun hz j
    simp at h
  obtain ⟨b, χ, a, ha, _, hb⟩ := exists_characterBasis_containing (ρ.restrict i)
    (iSup_characterSpace_eq_top_of_isSplitTorus hT (ρ.restrict i))
    χv (Pi.single j 1) hv (coordinateLine_mem_characterSpace (ρ.restrict i) j hline)
  let B := (basisCoordinateGL b)⁻¹
  refine ⟨B, a, χ, ?_, ?_⟩
  · ext r
    change (Pi.basisFun k n).toMatrix b r a = (Pi.single j 1 : n → k) r
    simpa only [Module.Basis.toMatrix_apply, Pi.basisFun_repr] using congrFun ha r
  · change HasTorusCharacterDiagonal
      (ρ.conjugate (GeneralLinear.CocharacterDiagonal.rationalMatrixPoint B⁻¹)) i χ
    have hB : B⁻¹ = basisCoordinateGL b := inv_inv _
    rw [hB, ← basisCoordinatePoint_eq_rationalMatrixPoint b]
    intro A x
    exact conjugate_basisCoordinatePoint_affineMatrix (ρ.restrict i) b χ hb A x

/-- The retained coordinate change preserves the exact subgroup-functor
line stabilizer, including nonreduced scheme tests. -/
theorem HasExactCoordinateLineStabilizer.basisConjugate
    {ρ : MatrixRepresentation G n} {P : SubgroupFunctor G} {j : n}
    (h : ρ.HasExactCoordinateLineStabilizer P j)
    (B : GL n k) (a : n) (hB : IsCoordinateLineBasis B a j) :
    (ρ.basisConjugate B).HasExactCoordinateLineStabilizer P a := by
  intro Z g
  exact (h Z g).trans (exists_congr fun c =>
    (ρ.basisConjugate_coordinateScalar_iff B a j hB Z g c).symm)

/-- A fixed simultaneous torus diagonalization together with the exact
retention of the selected coordinate line. -/
structure TorusEigenlineDiagonalization (ρ : MatrixRepresentation G n)
    (i : T.toGrp ⟶ G) (j : n) where
  basisMatrix : GL n k
  lineIndex : n
  characters : n → rationalCharacters T.toGrp
  lineBasis : IsCoordinateLineBasis basisMatrix lineIndex j
  diagonal : (ρ.basisConjugate basisMatrix).HasTorusCharacterDiagonal i characters

/-- Choose the proved simultaneous diagonalization retaining the given
coordinate eigenline; there is no extra diagonalization hypothesis. -/
def torusEigenlineDiagonalization
    (ρ : MatrixRepresentation G n) (i : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (j : n)
    (hline : (ρ.restrict i).PreservesCoordinateLine j) :
    TorusEigenlineDiagonalization ρ i j := by
  have hne : Nonempty (TorusEigenlineDiagonalization ρ i j) := by
    obtain ⟨B, a, χ, hB, hdiag⟩ := exists_torusDiagonal_retaining_coordinateLine ρ i hT j hline
    exact ⟨⟨B, a, χ, hB, hdiag⟩⟩
  exact Classical.choice hne

end Langlands.GroupScheme.MatrixRepresentation
