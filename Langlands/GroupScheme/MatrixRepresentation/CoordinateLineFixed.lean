import Langlands.GroupScheme.MatrixRepresentation.CoordinateLineCharacter
import Langlands.GroupScheme.Rational.CharacterLine
import Langlands.GroupScheme.Absolute.QuotientNormalizer
import Langlands.GroupScheme.SchemeActionRationalPoints
import Langlands.GroupScheme.HomConjugacy

/-! # Fixed coordinate vectors from commutators and unipotent factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

section CharacterDetection

variable {k : Type u} [Field k] [IsAlgClosed k]
    {B U H N : GroupScheme (Spec (CommRingCat.of k))}

/-- Multiply the images of base points from two group-scheme factors. Its
surjectivity expresses rational factorization without asserting arbitrary-test
point surjectivity. -/
def rationalPointProductMap (a : U ⟶ B) (t : H ⟶ B) :
    rationalPoints U × rationalPoints H → rationalPoints B :=
  fun p => (p.1 ≫ a.hom.hom) * (p.2 ≫ t.hom.hom)

/-- A character of a reduced group locally of finite type is zero if its values
on algebraically closed base points are one. -/
theorem rationalCharacters.eq_zero_of_characterEval_base
    [IsReduced B.X.left] [LocallyOfFiniteType B.X.hom]
    (χ : rationalCharacters B)
    (hχ : ∀ b : rationalPoints B,
      characterEval χ (Over.mk (𝟙 (Spec (CommRingCat.of k)))) b = 1) :
    χ = 0 := by
  have : IsSeparated (Gm (Spec (CommRingCat.of k))).X.hom := by
    have : IsSeparated Gm.overSpecZ.{u}.hom := by
      change IsSeparated (Spec.map _)
      infer_instance
    change IsSeparated (Limits.pullback.snd _ (Gm.toSpecZ _))
    infer_instance
  apply congrArg Additive.ofMul
  apply Grp.hom_ext
  apply hom_ext_rationalPoints
  intro b
  apply (Gm.pointsEquiv (Spec (CommRingCat.of k)) _).injective
  change characterEval χ _ b = characterEval 0 _ b
  rw [hχ, characterEval_zero]

/-- A scheme-surjective commutator endomorphism forces a character of its
ambient group to be zero on the subgroup. Only rational-point commutator
identities are needed. -/
theorem characterRestrict_eq_zero_of_surjective_commutator
    [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom]
    (χ : rationalCharacters N) (i : H ⟶ N) (φ : H ⟶ H)
    [LocallyOfFiniteType φ.hom.hom.left] [Surjective φ.hom.hom.left]
    (x : rationalPoints N)
    (hcomm : ∀ t : rationalPoints H,
      (t ≫ φ.hom.hom) ≫ i.hom.hom =
        x * (t ≫ i.hom.hom) * x⁻¹ * (t ≫ i.hom.hom)⁻¹) :
    characterRestrict i χ = 0 := by
  apply rationalCharacters.eq_zero_of_characterEval_base
  intro t
  obtain ⟨s, rfl⟩ := exists_rationalPointLift φ t
  rw [characterEval_characterRestrict, hcomm, characterEval_commutator]

/-- Characters vanish on a group generated on algebraically closed base
points by a unipotent factor and a subgroup on which they vanish. -/
theorem rationalCharacters.eq_zero_of_unipotent_mul
    [IsReduced B.X.left] [LocallyOfFiniteType B.X.hom]
    (χ : rationalCharacters B) (a : U ⟶ B) (t : H ⟶ B)
    (hU : IsUnipotent U) (ht : characterRestrict t χ = 0)
    (hfactor : Function.Surjective (rationalPointProductMap a t)) :
    χ = 0 := by
  apply rationalCharacters.eq_zero_of_characterEval_base
  intro b
  obtain ⟨⟨v, s⟩, rfl⟩ := hfactor b
  change characterEval χ _ ((v ≫ a.hom.hom) * (s ≫ t.hom.hom)) = 1
  rw [map_mul, ← characterEval_characterRestrict a χ,
    hU.characterEval_eq_one, ← characterEval_characterRestrict t χ,
    ht, characterEval_zero, one_mul]

end CharacterDetection

namespace MatrixRepresentation

section FixedVector

variable {R : CommRingCat.{u}} {N B : GroupScheme (Spec R)}
    {n : Type} [Fintype n] [DecidableEq n]

/-- Triviality of the coordinate-line character on a subgroup fixes the
chosen coordinate vector on every scheme test. -/
theorem isFixedVector_coordinateVector_of_characterRestrict_eq_zero
    (ρ : MatrixRepresentation N n) (j : n)
    (hline : ρ.StabilizesCoordinateLine j) (i : B ⟶ N)
    (hχ : characterRestrict i (ρ.coordinateLineRationalCharacter j hline) = 0) :
    (ρ.restrict i).IsFixedVector (Pi.single j 1) := by
  intro T b
  have hs : (fun l => scalarMap T ((Pi.single j 1 : n → R) l)) =
      (Pi.single j 1 : n → Γ(T.left, ⊤)) := by
    funext l
    by_cases hl : l = j <;> simp [hl]
  rw [hs, pointMatrix_restrict, ρ.coordinateLineCharacter_action j hline]
  have hval : characterEval (ρ.coordinateLineRationalCharacter j hline) T
      (b ≫ i.hom.hom) = 1 := by
    rw [← characterEval_characterRestrict, hχ, characterEval_zero]
  rw [hval]
  simp only [Units.val_one, one_smul]

end FixedVector

section CommutatorFixedVector

variable {k : Type u} [Field k] [IsAlgClosed k]
    {N B U H : GroupScheme (Spec (CommRingCat.of k))}
    {n : Type} [Fintype n] [DecidableEq n]

/-- A stabilized coordinate line is fixed pointwise by a subgroup admitting
a unipotent-times-subgroup rational factorization, when the second factor is
the image of a surjective commutator endomorphism in the line stabilizer. -/
theorem isFixedVector_coordinateVector_of_surjective_commutator
    [IsReduced B.X.left] [LocallyOfFiniteType B.X.hom]
    [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom]
    (ρ : MatrixRepresentation N n) (j : n)
    (hline : ρ.StabilizesCoordinateLine j) (i : B ⟶ N)
    (a : U ⟶ B) (t : H ⟶ B) (hU : IsUnipotent U)
    (φ : H ⟶ H)
    [LocallyOfFiniteType φ.hom.hom.left] [Surjective φ.hom.hom.left]
    (x : rationalPoints N)
    (hcomm : ∀ s : rationalPoints H,
      (s ≫ φ.hom.hom) ≫ (t ≫ i).hom.hom =
        x * (s ≫ (t ≫ i).hom.hom) * x⁻¹ * (s ≫ (t ≫ i).hom.hom)⁻¹)
    (hfactor : Function.Surjective (rationalPointProductMap a t)) :
    (ρ.restrict i).IsFixedVector (Pi.single j 1) := by
  let χ := ρ.coordinateLineRationalCharacter j hline
  have ht : characterRestrict t (characterRestrict i χ) = 0 := by
    have h := characterRestrict_eq_zero_of_surjective_commutator χ (t ≫ i) φ x hcomm
    simpa only [characterRestrict_comp, AddMonoidHom.comp_apply] using h
  apply ρ.isFixedVector_coordinateVector_of_characterRestrict_eq_zero j hline i
  exact (characterRestrict i χ).eq_zero_of_unipotent_mul a t hU ht hfactor

end CommutatorFixedVector

end MatrixRepresentation
end Langlands.GroupScheme
