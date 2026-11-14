import Langlands.GroupScheme.Rational.DynamicSemigroupProof
import Langlands.GroupScheme.Rational.SemigroupSmoothQuotientProof
import Langlands.GroupScheme.Rational.SemigroupQuotientTransport

/-! # Smooth quotients on dynamic unipotent subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [Smooth Q.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (q : G ⟶ Q)

/-- The dynamic unipotent subgroup is the positive semigroup subgroup for conjugation
by the cocharacter itself. -/
theorem unipotent_eq_positiveSemigroup :
    unipotent χ = RelativeRoot.semigroupSubgroup (AutomorphicAction.conjugation χ)
      (RelativeRoot.positiveSemigroup (S := Gm _) (𝟙 _)) := by
  exact RelativeRoot.dynamicUnipotentSemigroupComparison G (Gm _) isSplitTorus_gm χ (𝟙 _)

omit [Smooth G.X.hom] [Smooth Q.X.hom]
  [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
in
private theorem conjugation_quotient_equivariant
    (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ (Gm _).X) (x : T ⟶ G.X) :
    (AutomorphicAction.conjugation χ).act s x ≫ q.hom.hom =
      (AutomorphicAction.conjugation (χ ≫ q)).act s (x ≫ q.hom.hom) := by
  simp only [AutomorphicAction.conjugation_act, MonObj.mul_comp, GrpObj.inv_comp,
    Grp.comp_hom_hom, Category.assoc]

/-- A smooth surjective homomorphism induces a smooth surjective homomorphism
between any supplied representatives of the dynamic unipotent subgroups. -/
theorem exists_unipotentQuotientHom (hqs : Smooth q.hom.hom.left)
    (hqsurj : Surjective q.hom.hom.left)
    {P R : GroupScheme (Spec (CommRingCat.of k))} (i : P ⟶ G) (j : R ⟶ Q)
    (hi : (unipotent χ).IsRepresentedBy i)
    (hj : (unipotent (χ ≫ q)).IsRepresentedBy j) :
    ∃ p : P ⟶ R, i ≫ q = p ≫ j ∧
      Smooth p.hom.hom.left ∧ Surjective p.hom.hom.left := by
  rw [unipotent_eq_positiveSemigroup] at hi hj
  exact RelativeRoot.semigroupSmoothQuotient k G Q inferInstance inferInstance
    inferInstance inferInstance (Gm _) isSplitTorus_gm
    (AutomorphicAction.conjugation χ) (AutomorphicAction.conjugation (χ ≫ q))
    q hqs hqsurj (conjugation_quotient_equivariant χ q)
    (RelativeRoot.positiveSemigroup (𝟙 _)) P R i j hi hj

/-- The actual quotient homomorphism between given dynamic unipotent subgroup
representatives, chosen from the proved smooth quotient existence. -/
def unipotentQuotientHom (hqs : Smooth q.hom.hom.left)
    (hqsurj : Surjective q.hom.hom.left)
    {P R : GroupScheme (Spec (CommRingCat.of k))} (i : P ⟶ G) (j : R ⟶ Q)
    (hi : (unipotent χ).IsRepresentedBy i)
    (hj : (unipotent (χ ≫ q)).IsRepresentedBy j) : P ⟶ R :=
  (exists_unipotentQuotientHom χ q hqs hqsurj i j hi hj).choose

/-- The chosen quotient homomorphism commutes with the ambient inclusions and
is smooth and surjective on schemes. -/
theorem unipotentQuotientHom_spec (hqs : Smooth q.hom.hom.left)
    (hqsurj : Surjective q.hom.hom.left)
    {P R : GroupScheme (Spec (CommRingCat.of k))} (i : P ⟶ G) (j : R ⟶ Q)
    (hi : (unipotent χ).IsRepresentedBy i)
    (hj : (unipotent (χ ≫ q)).IsRepresentedBy j) :
    i ≫ q = unipotentQuotientHom χ q hqs hqsurj i j hi hj ≫ j ∧
      Smooth (unipotentQuotientHom χ q hqs hqsurj i j hi hj).hom.hom.left ∧
      Surjective (unipotentQuotientHom χ q hqs hqsurj i j hi hj).hom.hom.left :=
  (exists_unipotentQuotientHom χ q hqs hqsurj i j hi hj).choose_spec

/-- Dynamic unipotent subgroups have their full actual fppf image under every smooth
surjective homomorphism of smooth affine groups. -/
theorem unipotent_isFppfImage (hqs : Smooth q.hom.hom.left)
    (hqsurj : Surjective q.hom.hom.left) :
    SubgroupFunctor.IsFppfImage (unipotent χ) (unipotent (χ ≫ q)) q := by
  rw [unipotent_eq_positiveSemigroup, unipotent_eq_positiveSemigroup]
  exact RelativeRoot.isFppfImage_semigroupSubgroup
    (AutomorphicAction.conjugation χ) (AutomorphicAction.conjugation (χ ≫ q)) q
    (conjugation_quotient_equivariant χ q) RelativeRoot.semigroupRealization
    RelativeRoot.semigroupSmoothQuotient isSplitTorus_gm hqs hqsurj
    (RelativeRoot.positiveSemigroup (𝟙 _))

end Langlands.GroupScheme.Dynamic
