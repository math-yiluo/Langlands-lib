import Langlands.GroupScheme.MatrixRepresentation.CharacterSpaces
import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Langlands.GroupScheme.Torus.ExponentCharacters
import Langlands.GroupScheme.Rational.FundamentalRepresentations
import Mathlib.Algebra.DirectSum.Module

/-! # Complete character-space decomposition for split-torus representations -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj Classical

namespace Langlands.GroupScheme.MatrixRepresentation

attribute [local instance] isAffineHom_splitTorus_spec

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The universal character-space equation is equivalent to its all-affine-test form. -/
theorem mem_characterSpace_iff_affine (ρ : MatrixRepresentation G n)
    (χ : rationalCharacters G) (v : n → k) :
    v ∈ ρ.characterSpace χ ↔
      ∀ (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A),
        (ρ.affineMatrix A x : Matrix n n A) *ᵥ
            (fun r => algebraMap k A (v r)) =
          (Gm.affineUnitsEquiv (CommRingCat.of k) A (x ≫ χ.toMul.hom.hom) : A) •
            (fun r => algebraMap k A (v r)) := by
  constructor
  · exact fun hv A x => characterSpace_affine hv A x
  · intro h
    exact h (CharacterUnits.Coord G) (CharacterUnits.universalPoint G)

/-- Pulling back both a representation and a character preserves its character vectors. -/
theorem characterSpace_le_restrict (ρ : MatrixRepresentation G n)
    (f : H ⟶ G) (χ : rationalCharacters G) :
    ρ.characterSpace χ ≤ (ρ.restrict f).characterSpace (characterRestrict f χ) := by
  intro v hv
  apply (mem_characterSpace_iff_affine _ _ _).mpr
  intro A x
  rw [affineMatrix_restrict]
  simpa only [characterRestrict_apply, Grp.comp_hom_hom,
    Category.assoc] using characterSpace_affine hv A (x ≫ f.hom.hom)

/-- Transport along an actual group-scheme isomorphism preserves the whole character space. -/
theorem characterSpace_restrict_iso (ρ : MatrixRepresentation G n)
    (e : G ≅ H) (χ : rationalCharacters H) :
    (ρ.restrict e.inv).characterSpace χ =
      ρ.characterSpace (characterRestrict e.hom χ) := by
  apply le_antisymm
  · have h := characterSpace_le_restrict (ρ.restrict e.inv) e.hom χ
    simpa only [restrict_comp, Iso.hom_inv_id, restrict_id] using h
  · have h := characterSpace_le_restrict ρ e.inv (characterRestrict e.hom χ)
    have hc : characterRestrict e.inv (characterRestrict e.hom χ) = χ := by
      change (characterRestrict e.inv).comp (characterRestrict e.hom) χ = χ
      rw [← characterRestrict_comp, Iso.inv_hom_id, characterRestrict_id]
      rfl
    simpa only [hc] using h

variable (I : Type u) [Fintype I] [DecidableEq I]

/-- A universal coefficient column is in the character space of its integral exponent. -/
theorem coefficientColumn_mem_characterSpace
    (ρ : MatrixRepresentation (splitTorus (Spec (CommRingCat.of k)) I) n)
    (m : I → ℤ) (j : n) :
    GeneralLinear.CocharacterDiagonal.coefficientColumn I ρ m j ∈
      ρ.characterSpace ((rationalCharacters.equivCharacterLattice
        (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)).symm
          (splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m)) := by
  apply (mem_characterSpace_iff_affine _ _ _).mpr
  intro A x
  have h := GeneralLinear.CocharacterDiagonal.coefficientColumn_weight I ρ
    (splitTorus.algebraPointsEquiv I A x) m j
  rw [GeneralLinear.CocharacterDiagonal.matrixAt, MulEquiv.symm_apply_apply,
    ← splitTorus.characterValue_exponentCharacter] at h
  exact h

/-- Character spaces span every finite representation of a standard split torus. -/
theorem iSup_characterSpace_eq_top_splitTorus
    (ρ : MatrixRepresentation (splitTorus (Spec (CommRingCat.of k)) I) n) :
    (⨆ χ : rationalCharacters (splitTorus (Spec (CommRingCat.of k)) I),
      ρ.characterSpace χ) = ⊤ := by
  apply top_unique
  rw [← GeneralLinear.CocharacterDiagonal.span_coefficientColumn I ρ]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨m, j⟩, rfl⟩
  exact Submodule.mem_iSup_of_mem _ (coefficientColumn_mem_characterSpace I ρ m j)

/-- Character spaces span every finite representation of any supplied split torus. -/
theorem iSup_characterSpace_eq_top_of_isSplitTorus
    (hG : IsSplitTorus G) (ρ : MatrixRepresentation G n) :
    (⨆ χ : rationalCharacters G, ρ.characterSpace χ) = ⊤ := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hG
  let := Fintype.ofFinite I
  apply top_unique
  rw [← iSup_characterSpace_eq_top_splitTorus I (ρ.restrict e.inv)]
  apply iSup_le
  intro χ
  rw [characterSpace_restrict_iso]
  exact le_iSup _ _

/-- The all-algebra character spaces form an internal direct sum. -/
theorem isInternal_characterSpace_of_isSplitTorus
    (hG : IsSplitTorus G) (ρ : MatrixRepresentation G n) :
    DirectSum.IsInternal ρ.characterSpace :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (characterSpace_iSupIndep ρ) (iSup_characterSpace_eq_top_of_isSplitTorus hG ρ)

/-- Summing the character components identifies their direct sum with the original space. -/
def characterDecomposition (hG : IsSplitTorus G) (ρ : MatrixRepresentation G n) :
    (DirectSum (rationalCharacters G) fun χ => ρ.characterSpace χ) ≃ₗ[k] (n → k) :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap ρ.characterSpace)
    (isInternal_characterSpace_of_isSplitTorus hG ρ)

/-- A single character component maps to the original vector. -/
@[simp] theorem characterDecomposition_lof (hG : IsSplitTorus G)
    (ρ : MatrixRepresentation G n) (χ : rationalCharacters G)
    (v : ρ.characterSpace χ) :
    characterDecomposition hG ρ
      (DirectSum.lof k (rationalCharacters G) (fun ψ => ρ.characterSpace ψ) χ v) = v :=
  DirectSum.coeLinearMap_lof ρ.characterSpace χ v

/-- Decomposing a character vector recovers it in its own component. -/
@[simp] theorem characterDecomposition_symm_apply_same (hG : IsSplitTorus G)
    (ρ : MatrixRepresentation G n) (χ : rationalCharacters G)
    (v : ρ.characterSpace χ) :
    (characterDecomposition hG ρ).symm v χ = v :=
  (isInternal_characterSpace_of_isSplitTorus hG ρ).ofBijective_coeLinearMap_same v

/-- Decomposing a character vector has zero component at every other character. -/
@[simp] theorem characterDecomposition_symm_apply_ne (hG : IsSplitTorus G)
    (ρ : MatrixRepresentation G n) (χ ψ : rationalCharacters G) (hne : χ ≠ ψ)
    (v : ρ.characterSpace χ) :
    (characterDecomposition hG ρ).symm v ψ = 0 :=
  (isInternal_characterSpace_of_isSplitTorus hG ρ).ofBijective_coeLinearMap_of_ne hne v

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G) {n : Type} [Fintype n] [DecidableEq n]

/-- The torus-weight decomposition conjunct of highest weight holds for every representation. -/
theorem iSup_representationWeightSpace_eq_top (ρ : MatrixRepresentation G n) :
    (⨆ lam : characterLattice p.torus, p.representationWeightSpace ρ lam) = ⊤ := by
  let := p.isSplitTorus.isAffineHom
  change (⨆ lam : characterLattice p.torus,
    (ρ.restrict p.inclusion).characterSpace
      ((rationalCharacters.equivCharacterLattice p.torus).symm lam)) = ⊤
  exact MatrixRepresentation.iSup_characterSpace_eq_top_of_isSplitTorus
    p.isSplitTorus (ρ.restrict p.inclusion)

end Langlands.GroupScheme.SplitPinning
