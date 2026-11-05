import Langlands.GroupScheme.Torus.SplitPartCharacters
import Langlands.Representation.Plancherel.TorusNormKernelCompactnessProof

/-! # Rational characters and compactness of anisotropic tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A closed subgroup of an anisotropic group is anisotropic. -/
theorem IsAnisotropic.of_isClosedSubgroup
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsAnisotropic G) {j : H ⟶ G} (hj : IsClosedSubgroup j) :
    IsAnisotropic H := by
  apply isAnisotropic_iff.mpr
  intro I _ i hi
  exact isAnisotropic_iff.mp hG I (i ≫ j) (hi.comp hj)

/-- Every rational character of an affine anisotropic torus locally of finite
type is zero, by detection on its largest split subtorus. -/
theorem IsAnisotropic.rationalCharacter_eq_zero_of_isTorus
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hT : IsAnisotropic T.toGrp) (hTtor : IsTorus T.toGrp)
    (χ : rationalCharacters T.toGrp) : χ = 0 := by
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  obtain ⟨A, i, hi⟩ := exists_largestSplitSubtorus T
  have : Subsingleton (rationalCharacters A.toGrp) :=
    hT.subsingleton_character hi.1
  apply hi.characterRestrict_injective hTtor
  exact Subsingleton.elim _ _

/-- In particular, every rational character of a closed torus inside an
anisotropic group vanishes. -/
theorem IsAnisotropic.rationalCharacter_eq_zero_of_closedTorus
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hG : IsAnisotropic G) (hT : IsTorus T.toGrp)
    {j : T.toGrp ⟶ G} (hj : IsClosedSubgroup j)
    (χ : rationalCharacters T.toGrp) : χ = 0 :=
  (hG.of_isClosedSubgroup hj).rationalCharacter_eq_zero_of_isTorus hT χ

/-- Such a rational character takes the value one on every rational point. -/
theorem IsAnisotropic.rationalCharacterEval_eq_one_of_closedTorus
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hG : IsAnisotropic G) (hT : IsTorus T.toGrp)
    {j : T.toGrp ⟶ G} (hj : IsClosedSubgroup j)
    (χ : rationalCharacters T.toGrp) (t : rationalPoints T.toGrp) :
    rationalCharacterEval χ t = 1 := by
  rw [hG.rationalCharacter_eq_zero_of_closedTorus hT hj χ,
    rationalCharacterEval_zero]

open Langlands.Plancherel.TorusNormKernel

/-- The norm of the value of a character over a finite extension is one on a
closed torus in an anisotropic group. -/
theorem IsAnisotropic.algebraNorm_characterEval_eq_one_of_closedTorus
    (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hG : IsAnisotropic G) (hT : IsTorus T.toGrp)
    {j : T.toGrp ⟶ G} (hj : IsClosedSubgroup j)
    (χ : rationalCharacters (GaloisPointComparison.baseChanged k K T.toGrp))
    (t : rationalPoints T.toGrp) :
    Algebra.norm k (rationalCharacterEval χ
      (GaloisPointComparison.rationalExtend k K T.toGrp t) : K) = 1 := by
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  rw [← normCharacter_eval,
    hG.rationalCharacterEval_eq_one_of_closedTorus hT hj (normCharacter χ) t]
  rfl

/-- An anisotropic local-field torus is compact in the canonical rational-point
topology, by the already proved compactness of its common norm kernel. -/
theorem IsAnisotropic.isCompact_univ_of_isTorus
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hT : IsAnisotropic T.toGrp) (hTtor : IsTorus T.toGrp) :
    letI : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
    letI : TopologicalSpace (rationalPoints T.toGrp) :=
      Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology k T.X
    IsCompact (Set.univ : Set (rationalPoints T.toGrp)) := by
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  let : TopologicalSpace (rationalPoints T.toGrp) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology k T.X
  have hc := Langlands.Plancherel.torusNormKernelCompactness k T.toGrp hTtor
  have heq : (Langlands.Plancherel.rationalCommonNormKernel T.toGrp :
      Set (rationalPoints T.toGrp)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    apply (Langlands.Plancherel.mem_rationalCommonNormKernel T.toGrp t).mpr
    intro χ
    rw [hT.rationalCharacter_eq_zero_of_isTorus hTtor χ, rationalCharacterEval_zero,
      map_one]
  rw [heq] at hc
  exact hc

/-- Anisotropic tori over actual nonarchimedean local fields have compact
rational points in the canonical evaluation topology. -/
def AnisotropicTorusCompactnessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom],
    IsTorus T.toGrp → IsAnisotropic T.toGrp →
      letI : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
      letI : TopologicalSpace (rationalPoints T.toGrp) :=
        Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology F T.X
      IsCompact (Set.univ : Set (rationalPoints T.toGrp))

end Langlands.GroupScheme
