import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocyclePinning
import Langlands.GroupScheme.SimplyConnected.NormOneMatrixRepresentation
import Langlands.GroupScheme.Reductive.SpecialLinearFundamentalWeights
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.MatrixRepresentation.SeparatingWeightCoefficients

/-! # The first fundamental highest weight of the standard special-linear representation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.SpecialLinear.FinSucc

open MatrixRepresentation

variable {n : ℕ} {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))

variable (n k) in
/-- The standard column representation restricted to the actual diagonal torus. -/
def diagonalRepresentation : MatrixRepresentation (𝔻).toGrp (Fin (n + 1)) :=
  MatrixRepresentation.restrict (inclusion (Fin (n + 1)) (CommRingCat.of k))
    (diagonalTorus n (CommRingCat.of k))

theorem characterValue_weightChar (a : Fin (n + 1))
    {S : Type u} [CommRing S] [Algebra k S] (x : Lie.AffinePoints (𝔻).toGrp S) :
    Lie.characterValue (weightChar n k a) x =
      torusEntry (GeneralLinear.torusCoords x) a := by
  rw [characterValue_eq_prod]
  simp only [weightChar, LinearEquiv.apply_symm_apply]
  rfl

theorem diagonalRepresentation_affineMatrix (S : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶ (𝔻).toGrp.X) :
    ((diagonalRepresentation n k).affineMatrix S x :
      Matrix (Fin (n + 1)) (Fin (n + 1)) S) =
        Matrix.diagonal (fun a => (torusEntry (GeneralLinear.torusCoords x) a : S)) := by
  change (GeneralLinear.affinePointsEquiv (Fin (n + 1)) (CommRingCat.of k) S
    ((x ≫ (diagonalTorus n (CommRingCat.of k)).hom.hom) ≫
      (inclusion (Fin (n + 1)) (CommRingCat.of k)).hom.hom) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) S) = _
  rw [Category.assoc, ← Grp.comp_hom_hom,
    affinePointsEquiv_diagonalTorus_inclusion]
  rfl

private theorem coefficientExtension_id (S : Type*) [CommRing S] [Algebra k S]
    (v : Fin (n + 1) → S) (a : Fin (n + 1)) :
    coefficientExtension (LinearMap.id : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k))
      S v a = v a := by
  simp [coefficientExtension, Pi.single_apply]

/-- The original coordinates have exactly the actual diagonal characters as coefficients. -/
theorem diagonalRepresentation_hasCharacterCoefficients :
    (diagonalRepresentation n k).HasCharacterCoefficients
      (LinearMap.id : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k))
      (fun a => (rationalCharacters.equivCharacterLattice 𝔻).symm (weightChar n k a)) := by
  intro v a
  rw [coefficientExtension_id]
  change (((diagonalRepresentation n k).affineMatrix (CharacterUnits.Coord (𝔻).toGrp)
    (CharacterUnits.universalPoint (𝔻).toGrp) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (CharacterUnits.Coord (𝔻).toGrp)) *ᵥ
        (fun j => algebraMap k (CharacterUnits.Coord (𝔻).toGrp) (v j))) a =
      (Lie.characterValue (A := CharacterUnits.Coord (𝔻).toGrp)
        (weightChar n k a) (CharacterUnits.universalPoint (𝔻).toGrp)).val *
          algebraMap k (CharacterUnits.Coord (𝔻).toGrp) (v a)
  rw [diagonalRepresentation_affineMatrix, Matrix.mulVec_diagonal,
    characterValue_weightChar]

/-- Each coordinate vector is a vector for its corresponding actual character. -/
theorem single_mem_diagonalCharacterSpace (a : Fin (n + 1)) :
    (Pi.single a (1 : k)) ∈ (diagonalRepresentation n k).characterSpace
      ((rationalCharacters.equivCharacterLattice 𝔻).symm (weightChar n k a)) := by
  apply (mem_characterSpace_iff_affine _ _ _).mpr
  intro S x
  change ((diagonalRepresentation n k).affineMatrix S x :
    Matrix (Fin (n + 1)) (Fin (n + 1)) S) *ᵥ
      (fun j => algebraMap k S ((Pi.single a (1 : k) : Fin (n + 1) → k) j)) =
    (Lie.characterValue (A := S) (weightChar n k a) x : S) •
      (fun j => algebraMap k S ((Pi.single a (1 : k) : Fin (n + 1) → k) j))
  rw [diagonalRepresentation_affineMatrix, characterValue_weightChar]
  ext j
  rw [Matrix.mulVec_diagonal]
  by_cases h : j = a <;> simp [h]

/-- Every occurring character in the column representation is one diagonal character. -/
theorem exists_weightChar_of_diagonalCharacterSpace_ne_bot
    (mu : characterLattice 𝔻)
    (hmu : (diagonalRepresentation n k).characterSpace
      ((rationalCharacters.equivCharacterLattice 𝔻).symm mu) ≠ ⊥) :
    ∃ a : Fin (n + 1), mu = weightChar n k a := by
  obtain ⟨a, ha⟩ := exists_coefficient_character (diagonalRepresentation n k)
    (LinearMap.id : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k))
    (fun a => (rationalCharacters.equivCharacterLattice 𝔻).symm (weightChar n k a))
    diagonalRepresentation_hasCharacterCoefficients Function.injective_id hmu
  exact ⟨a, (rationalCharacters.equivCharacterLattice 𝔻).symm.injective ha⟩

/-- The coordinate characters are distinct on the actual integral lattice. -/
theorem weightChar_injective : Function.Injective (weightChar n k) := by
  intro a b h
  apply weightCoord_injective
  simpa only [weightChar, LinearEquiv.apply_symm_apply] using
    congrArg (GeneralLinear.characterCoordEquiv (Fin n) k) h

/-- Each occurring diagonal character has multiplicity exactly one. -/
theorem finrank_diagonalCharacterSpace_weightChar (a : Fin (n + 1)) :
    Module.finrank k ((diagonalRepresentation n k).characterSpace
      ((rationalCharacters.equivCharacterLattice 𝔻).symm (weightChar n k a))) = 1 := by
  apply finrank_characterSpace_eq_one (diagonalRepresentation n k)
    (LinearMap.id : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k))
    (fun a => (rationalCharacters.equivCharacterLattice 𝔻).symm (weightChar n k a))
    diagonalRepresentation_hasCharacterCoefficients Function.injective_id _ a
  · intro b hb
    exact (weightChar_injective
      ((rationalCharacters.equivCharacterLattice 𝔻).symm.injective hb)).symm
  · apply (Submodule.ne_bot_iff _).mpr
    exact ⟨Pi.single a 1, single_mem_diagonalCharacterSpace a, by
      intro h
      have := congrFun h a
      exact one_ne_zero (by simpa only [Pi.single_eq_same, Pi.zero_apply] using this)⟩

section CoordinatePinning

variable {J : Type u} [Finite J]
    (P : RootDatum J
      (characterLattice (splitTorus.commGroupScheme
        (Spec (CommRingCat.of k)) (ULift (Fin n))))
      (cocharacterLattice (splitTorus.commGroupScheme
        (Spec (CommRingCat.of k)) (ULift (Fin n)))))
    (hP : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P)
    (hred : P.IsReduced) (B : P.Base)

/-- Retain the actual diagonal torus when completing coordinate root data to a pinning. -/
def coordinatePinning : SplitPinning (groupScheme (Fin (n + 1)) (CommRingCat.of k)) :=
  SpecialLinearTitsCocycle.coordinatePinning n P hP hred B

variable (e : B.support ≃ Fin n)
    (hnumber : ∀ a : B.support,
      P.root a.val = rootChar n k (e a).castSucc (e a).succ)

include hnumber in
/-- The first diagonal weight dominates every diagonal weight for adjacent-root numbering. -/
theorem first_sub_weightChar_mem_positiveRootMonoid (a : Fin (n + 1)) :
    weightChar n k 0 - weightChar n k a ∈
      (coordinatePinning P hP hred B).positiveRootMonoid := by
  induction a using Fin.induction with
  | zero =>
    simpa only [sub_self] using (coordinatePinning P hP hred B).positiveRootMonoid.zero_mem
  | succ a ih =>
    have hr := (coordinatePinning P hP hred B).simpleRoot_mem_positiveRootMonoid (e.symm a)
    change P.root (e.symm a).val ∈ _ at hr
    rw [hnumber, e.apply_symm_apply, rootChar_eq_weightChar_sub] at hr
    simpa only [sub_add_sub_cancel] using
      (coordinatePinning P hP hred B).positiveRootMonoid.add_mem ih hr

include hnumber in
/-- The standard column representation has the first diagonal character as highest weight. -/
theorem inclusion_isHighestWeight :
    (coordinatePinning P hP hred B).IsHighestWeight
      (inclusion (Fin (n + 1)) (CommRingCat.of k)) (weightChar n k 0) := by
  refine ⟨inclusion_isIrreducible,
    (coordinatePinning P hP hred B).iSup_representationWeightSpace_eq_top _, ?_, ?_⟩
  · change Module.finrank k ((diagonalRepresentation n k).characterSpace
      ((rationalCharacters.equivCharacterLattice (splitTorus.commGroupScheme
        (Spec (CommRingCat.of k)) (ULift (Fin n)))).symm (weightChar n k 0))) = 1
    exact finrank_diagonalCharacterSpace_weightChar 0
  · intro mu hmu
    change (diagonalRepresentation n k).characterSpace
      ((rationalCharacters.equivCharacterLattice (splitTorus.commGroupScheme
        (Spec (CommRingCat.of k)) (ULift (Fin n)))).symm mu) ≠ ⊥ at hmu
    obtain ⟨a, rfl⟩ := exists_weightChar_of_diagonalCharacterSpace_ne_bot mu hmu
    exact first_sub_weightChar_mem_positiveRootMonoid P hP hred B e hnumber a

end CoordinatePinning

end Langlands.GroupScheme.SpecialLinear.FinSucc

namespace Langlands.GroupScheme

/-- The actual standard column representation has first fundamental highest weight
for an actual diagonal pinning with adjacent-root numbering. -/
def SpecialLinearFirstFundamentalHighestWeightStatement : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    let T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin (n + 1)))
    ∃ (J : Type u) (hJ : Finite J),
      letI := hJ
      ∃ (P : RootDatum J (characterLattice T) (cocharacterLattice T))
        (hP : IsRootDatumOf
          (SpecialLinear.FinSucc.diagonalTorus (n + 1) (CommRingCat.of k)) P)
        (hred : P.IsReduced) (B : P.Base) (e : B.support ≃ Fin (n + 1))
        (hspan : P.corootSpan ℤ = ⊤),
        (∀ a : B.support, P.root a.val =
          SpecialLinear.FinSucc.rootChar (n + 1) k (e a).castSucc (e a).succ) ∧
        (SpecialLinear.FinSucc.coordinatePinning P hP hred B).IsHighestWeight
          (SpecialLinear.inclusion (Fin (n + 1 + 1)) (CommRingCat.of k))
          (Langlands.RootDatum.fundamentalWeightBasis P B hspan (e.symm 0))

theorem specialLinearFirstFundamentalHighestWeight :
    SpecialLinearFirstFundamentalHighestWeightStatement.{u} := by
  intro k _ n
  obtain ⟨J, hJ, P, hP, hred, B, e, hspan, hnumber, _⟩ :=
    SpecialLinear.FinSucc.exists_coordinateRootDatum (n + 1) k
  have : Finite J := hJ
  refine ⟨J, hJ, P, hP, hred, B, e, hspan, hnumber, ?_⟩
  rw [SpecialLinear.FinSucc.first_fundamentalWeightBasis hP B e hnumber hspan]
  exact SpecialLinear.FinSucc.inclusion_isHighestWeight P hP hred B e hnumber

end Langlands.GroupScheme
