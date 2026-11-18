import Langlands.GroupScheme.Unipotent.MultiplicativeTrivialityStatement
import Langlands.GroupScheme.Rational.CharacterLine
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeUnipotentHom

/-! # Unipotent groups and groups of multiplicative type: proof -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem hom_eq_zero_to_multiplicativeType
    {k : Type u} [Field k] {U M : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] (hU : IsUnipotent U) (hM : IsMultiplicativeType M)
    (f : U ⟶ M) : f = 0 := by
  obtain ⟨K, _, _, Λ, _, _, ⟨e⟩⟩ := hM
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  have hUK : IsUnipotent (B.obj U) := hU.baseChange (K := K)
  let g := B.map f ≫ e.hom
  have hg : g = 0 := by
    apply hom_ext_points
    intro T x
    change x ≫ g.hom.hom = x ≫ (1 : (B.obj U).X ⟶ _)
    rw [MonObj.comp_one]
    apply (Diagonalizable.characterPointsEquiv (CommRingCat.of K) Λ T).injective
    rw [map_one]
    apply MonoidHom.ext
    intro m
    let χ : rationalCharacters (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp :=
      Additive.ofMul
        (CommGroupScheme.groupHom (DiagonalizableCharacter.evalCharacter _ Λ m.toAdd))
    have h := hUK.characterEval_eq_one (characterRestrict g χ) T x
    rw [characterEval_characterRestrict, characterEval_apply] at h
    change Gm.pointsEquiv _ T
      ((x ≫ g.hom.hom) ≫
        (CommGroupScheme.groupHom (DiagonalizableCharacter.evalCharacter _ Λ m.toAdd)).hom.hom) =
          1 at h
    simpa only [DiagonalizableCharacter.evalCharacter_apply, ofAdd_toAdd,
      MonoidHom.one_apply] using h
  let : (Over.pullback b).Faithful := GaloisCocharacterDescent.faithful_algebraPullback k K
  apply (GroupScheme.baseChange b).map_injective
  rw [Functor.map_zero]
  calc B.map f = g ≫ e.inv := by simp [g]
    _ = 0 := by rw [hg, zero_comp]

/-- Triviality, scheme-theoretic intersection, and both directions of homomorphism
vanishing for unipotent groups and groups of multiplicative type (Milne 14.16–14.18). -/
theorem unipotentMultiplicativeTriviality : UnipotentMultiplicativeTrivialityStatement.{u} := by
  intro k _
  refine ⟨?_, ?_, ?_⟩
  · intro G _ _ hM hU
    rw [hM.hom_eq_zero_of_isUnipotent hU (𝟙 G), SubgroupFunctor.range_zero]
  · intro G U M _ _ i j hi _ hU hM
    let : IsClosedImmersion i.hom.hom.left := hi
    let : IsAffineHom U.X.hom := by
      rw [← Over.w i.hom.hom]
      infer_instance
    have hsnd : IsClosedSubgroup (subgroupIntersectionSnd i j) :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (subgroupIntersection_isPullback_scheme i j) hi
    have hIntersection := hM.of_isClosedSubgroup (subgroupIntersectionSnd i j) hsnd
    have hfst := hIntersection.hom_eq_zero_of_isUnipotent hU (subgroupIntersectionFst i j)
    rw [← range_subgroupIntersectionHom, subgroupIntersectionHom, hfst, zero_comp,
      SubgroupFunctor.range_zero]
  · intro U M _ _ _ _ hU hM
    constructor <;> intro f
    · rw [hom_eq_zero_to_multiplicativeType hU hM f, SubgroupFunctor.range_zero]
    · rw [hM.hom_eq_zero_of_isUnipotent hU f, SubgroupFunctor.range_zero]

end Langlands.GroupScheme
