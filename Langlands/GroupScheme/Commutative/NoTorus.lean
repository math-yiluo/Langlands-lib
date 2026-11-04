import Langlands.GroupScheme.Absolute.CharacterUnipotence
import Langlands.GroupScheme.CentralSurjectionImage.SurjectiveCharacterPoint
import Langlands.GroupScheme.Rational.CharacterFpqcProof
import Langlands.GroupScheme.Torus.NoTorusBaseChangeReduction
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.Geometry

/-! # Characters and unipotence of commutative groups without cocharacters -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Every nonzero rational character of a smooth connected affine group over
an arbitrary field is surjective on underlying schemes. -/
theorem rationalCharacters.surjective_of_ne_zero
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (χ : rationalCharacters H) (hχ : χ ≠ 0) : Surjective χ.toMul.hom.hom.left := by
  obtain ⟨D, q, m, hD, _, hfac, hq⟩ :=
    isSplitTorus_gm.exists_fppfQuotient_factor χ.toMul
  let D' : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { D with comm := hD.isCommMonObj }
  let α : characterLattice D' := Additive.ofMul m
  have hα : α ≠ 0 := by
    intro hα
    have hm : m = 0 := congrArg Additive.toMul hα
    apply hχ
    change χ.toMul = 0
    rw [← hfac, hm, CategoryTheory.Limits.comp_zero]
  have hsurj := RelativeRoot.characterFpqc k D' hD α hα
  have : Surjective m.hom.hom.left := hsurj.2.2
  have : Surjective q.hom.hom.left := hq.2.1
  have hleft : χ.toMul.hom.hom.left = q.hom.hom.left ≫ m.hom.hom.left :=
    congrArg (fun f : H ⟶ (Gm (Spec (CommRingCat.of k))).toGrp => f.hom.hom.left) hfac.symm
  rw [hleft]
  infer_instance

namespace CommutativeNoTorus

variable (Z : CommGroupScheme (Spec (CommRingCat.of k)))
    [Smooth Z.toGrp.X.hom] [IsAffineHom Z.toGrp.X.hom]
    [ConnectedSpace Z.toGrp.X.left]

/-- Choose a base-field cocharacter detecting the given nonzero rational
character of a smooth connected affine commutative group. -/
def detectingCocharacter (χ : rationalCharacters Z.toGrp) (hχ : χ ≠ 0) :
    (Gm (Spec (CommRingCat.of k))).toGrp ⟶ Z.toGrp :=
  Classical.choose
    (CentralSurjectionImage.exists_gm_characterRestrict_ne_zero_of_surjective χ
      (χ.surjective_of_ne_zero hχ))

/-- The chosen cocharacter has nonzero restriction of the original character. -/
theorem characterRestrict_detectingCocharacter_ne_zero
    (χ : rationalCharacters Z.toGrp) (hχ : χ ≠ 0) :
    characterRestrict (detectingCocharacter Z χ hχ) χ ≠ 0 :=
  Classical.choose_spec
    (CentralSurjectionImage.exists_gm_characterRestrict_ne_zero_of_surjective χ
      (χ.surjective_of_ne_zero hχ))

/-- With no nontrivial base-field cocharacters, all rational characters vanish. -/
theorem character_eq_zero_of_gm_hom_eq_zero
    (hZ : ∀ φ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ Z.toGrp, φ = 0)
    (χ : rationalCharacters Z.toGrp) : χ = 0 := by
  by_contra hχ
  have h := characterRestrict_detectingCocharacter_ne_zero Z χ hχ
  apply h
  change detectingCocharacter Z χ hχ ≫ χ.toMul = 0
  rw [hZ (detectingCocharacter Z χ hχ), zero_comp]

/-- Over an algebraically closed field, a smooth connected affine commutative
group with no nontrivial cocharacters is unipotent. -/
theorem isUnipotent_of_gm_hom_eq_zero [IsAlgClosed k]
    (hZ : ∀ φ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ Z.toGrp, φ = 0) :
    IsUnipotent Z.toGrp :=
  (isSolvableGroupScheme_of_isCommMonObj Z.toGrp).isUnipotent_of_characters_eq_zero
    (character_eq_zero_of_gm_hom_eq_zero Z hZ)

/-- The commutative algebraically closed instance of the no-torus implication. -/
theorem isUnipotent_of_no_torus [IsAlgClosed k]
    (hZ : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))),
      IsTorus T.toGrp → ∀ φ : T.toGrp ⟶ Z.toGrp, SubgroupFunctor.range φ = ⊥) :
    IsUnipotent Z.toGrp := by
  apply isUnipotent_of_gm_hom_eq_zero Z
  intro φ
  exact SubgroupFunctor.eq_zero_of_range_eq_bot
    (hZ (Gm (Spec (CommRingCat.of k))) isSplitTorus_gm.isTorus φ)

end CommutativeNoTorus

end Langlands.GroupScheme
