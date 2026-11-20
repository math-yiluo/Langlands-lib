import Langlands.GroupScheme.Unipotent.MultiplicativeTrivialityStatement
import Langlands.GroupScheme.Rational.CharacterLine
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof
import Langlands.GroupScheme.Absolute.SolvableUnipotentKernelAssembly
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.Absolute.CocharacterDescentGroup

/-! # Unipotent closed subgroups lie in a unipotent kernel with multiplicative quotient -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Every homomorphism from an affine unipotent group to a group of multiplicative type is
trivial (Milne 14.18), with no finiteness hypothesis on the target. -/
theorem IsUnipotent.hom_eq_zero_of_isMultiplicativeType
    {U M : GroupScheme (Spec (CommRingCat.of k))}
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

/-- Milne 16.6, uniqueness part: if `i : U ⟶ G` has an fppf quotient `q : G ⟶ M` onto a group of
multiplicative type, then every unipotent closed subgroup `j : V ⟶ G` lies in the range of `i`.
Indeed `j ≫ q` is trivial by Milne 14.18, so `j` factors through the kernel of `q`. -/
theorem IsUnipotent.range_le_of_isFppfQuotient
    {G U M V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : U ⟶ G) (q : G ⟶ M) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hM : IsMultiplicativeType M) (j : V ⟶ G) (hj : IsClosedSubgroup j)
    (hV : IsUnipotent V) :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range i := by
  have := hj.isAffineHom
  rw [← hq.2.2.2]
  exact range_le_kernelι_of_comp_eq_zero j q (hV.hom_eq_zero_of_isMultiplicativeType hM _)

end Langlands.GroupScheme
