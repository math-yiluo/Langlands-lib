import Langlands.GroupScheme.Rational.DynamicSemigroupProof
import Langlands.GroupScheme.Rational.SemigroupSmoothQuotientProof
import Langlands.GroupScheme.Rational.SemigroupQuotientTransport

/-! # Smooth quotients on dynamic parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [Smooth Q.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    [ConnectedSpace G.X.left] [ConnectedSpace Q.X.left]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (q : G ⟶ Q)

/-- The dynamic parabolic is the nonnegative semigroup subgroup for conjugation
by the cocharacter itself. -/
theorem parabolic_eq_nonnegativeSemigroup :
    parabolic χ = RelativeRoot.semigroupSubgroup (AutomorphicAction.conjugation χ)
      (RelativeRoot.nonnegativeSemigroup (S := Gm _) (𝟙 _)) := by
  exact (RelativeRoot.dynamicSemigroupComparison k G inferInstance inferInstance
    inferInstance (Gm _) isSplitTorus_gm χ (𝟙 _)).1

omit [Smooth G.X.hom] [Smooth Q.X.hom]
  [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
  [ConnectedSpace G.X.left] [ConnectedSpace Q.X.left] in
private theorem conjugation_quotient_equivariant
    (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ (Gm _).X) (x : T ⟶ G.X) :
    (AutomorphicAction.conjugation χ).act s x ≫ q.hom.hom =
      (AutomorphicAction.conjugation (χ ≫ q)).act s (x ≫ q.hom.hom) := by
  simp only [AutomorphicAction.conjugation_act, MonObj.mul_comp, GrpObj.inv_comp,
    Grp.comp_hom_hom, Category.assoc]

/-- A smooth surjective homomorphism induces a smooth surjective homomorphism
between any supplied representatives of the dynamic parabolics. -/
theorem exists_parabolicQuotientHom (hqs : Smooth q.hom.hom.left)
    (hqsurj : Surjective q.hom.hom.left)
    {P R : GroupScheme (Spec (CommRingCat.of k))} (i : P ⟶ G) (j : R ⟶ Q)
    (hi : (parabolic χ).IsRepresentedBy i)
    (hj : (parabolic (χ ≫ q)).IsRepresentedBy j) :
    ∃ p : P ⟶ R, i ≫ q = p ≫ j ∧
      Smooth p.hom.hom.left ∧ Surjective p.hom.hom.left := by
  rw [parabolic_eq_nonnegativeSemigroup] at hi hj
  exact RelativeRoot.semigroupSmoothQuotient k G Q inferInstance inferInstance
    inferInstance inferInstance (Gm _) isSplitTorus_gm
    (AutomorphicAction.conjugation χ) (AutomorphicAction.conjugation (χ ≫ q))
    q hqs hqsurj (conjugation_quotient_equivariant χ q)
    (RelativeRoot.nonnegativeSemigroup (𝟙 _)) P R i j hi hj

/-- The actual quotient homomorphism between given dynamic parabolic
representatives, chosen from the proved smooth quotient existence. -/
def parabolicQuotientHom (hqs : Smooth q.hom.hom.left)
    (hqsurj : Surjective q.hom.hom.left)
    {P R : GroupScheme (Spec (CommRingCat.of k))} (i : P ⟶ G) (j : R ⟶ Q)
    (hi : (parabolic χ).IsRepresentedBy i)
    (hj : (parabolic (χ ≫ q)).IsRepresentedBy j) : P ⟶ R :=
  (exists_parabolicQuotientHom χ q hqs hqsurj i j hi hj).choose

/-- The chosen quotient homomorphism commutes with the ambient inclusions and
is smooth and surjective on schemes. -/
theorem parabolicQuotientHom_spec (hqs : Smooth q.hom.hom.left)
    (hqsurj : Surjective q.hom.hom.left)
    {P R : GroupScheme (Spec (CommRingCat.of k))} (i : P ⟶ G) (j : R ⟶ Q)
    (hi : (parabolic χ).IsRepresentedBy i)
    (hj : (parabolic (χ ≫ q)).IsRepresentedBy j) :
    i ≫ q = parabolicQuotientHom χ q hqs hqsurj i j hi hj ≫ j ∧
      Smooth (parabolicQuotientHom χ q hqs hqsurj i j hi hj).hom.hom.left ∧
      Surjective (parabolicQuotientHom χ q hqs hqsurj i j hi hj).hom.hom.left :=
  (exists_parabolicQuotientHom χ q hqs hqsurj i j hi hj).choose_spec

/-- Dynamic parabolics have their full actual fppf image under every smooth
surjective homomorphism of smooth connected affine groups. -/
theorem parabolic_isFppfImage (hqs : Smooth q.hom.hom.left)
    (hqsurj : Surjective q.hom.hom.left) :
    SubgroupFunctor.IsFppfImage (parabolic χ) (parabolic (χ ≫ q)) q := by
  rw [parabolic_eq_nonnegativeSemigroup, parabolic_eq_nonnegativeSemigroup]
  exact RelativeRoot.isFppfImage_semigroupSubgroup
    (AutomorphicAction.conjugation χ) (AutomorphicAction.conjugation (χ ≫ q)) q
    (conjugation_quotient_equivariant χ q) RelativeRoot.semigroupRealization
    RelativeRoot.semigroupSmoothQuotient isSplitTorus_gm hqs hqsurj
    (RelativeRoot.nonnegativeSemigroup (𝟙 _))

end Langlands.GroupScheme.Dynamic
