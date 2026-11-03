import Langlands.GroupScheme.Rational.BruhatUnipotentReduction

/-! # Normalizer uniqueness from the opposite cell and Weyl factorization -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The root-product factorization needed for normalizer uniqueness: the first
factor is carried into the opposite unipotent group by `n⁻¹`, and the second
factor is carried back into the original unipotent group. -/
def HasUnipotentWeylFactorization : Prop :=
  let χ := CommGroupScheme.groupHom ν ≫ i
  let χminus := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  ∀ (n : normalizerPoints i) (u : RationalPoint.unipotent χ),
    ∃ a b : RationalPoint.unipotent χ,
      (u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) = a * b ∧
      (n : Over.mk (𝟙 _) ⟶ G.X)⁻¹ * a * n ∈ RationalPoint.unipotent χminus ∧
      (n : Over.mk (𝟙 _) ⟶ G.X)⁻¹ * b * n ∈ RationalPoint.unipotent χ

/-- The only normalizing point in the product of the opposite and original
dynamic unipotent groups is the identity. -/
def HasTrivialNormalizerOppositeCellIntersection : Prop :=
  let χ := CommGroupScheme.groupHom ν ≫ i
  let χminus := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  ∀ (n : normalizerPoints i)
    (a : RationalPoint.unipotent χminus) (b : RationalPoint.unipotent χ),
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) = a * b → n = 1

/-- Root-product factorization and the normalizer's trivial intersection with
the opposite unipotent cell imply uniqueness of normalizing points in `U n U`. -/
theorem hasUnipotentNormalizerSeparation_of_weylFactorization_of_oppositeCell
    (hfactor : HasUnipotentWeylFactorization i ν)
    (hcell : HasTrivialNormalizerOppositeCellIntersection i ν) :
    HasUnipotentNormalizerSeparation i ν := by
  let χ := CommGroupScheme.groupHom ν ≫ i
  let χminus := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  intro n n' u v heq
  obtain ⟨a, b, hu, ha, hb⟩ := hfactor n u
  have hc : n⁻¹ * n' = 1 := by
    apply hcell (n⁻¹ * n') ⟨_, ha⟩
      ⟨(n : Over.mk (𝟙 _) ⟶ G.X)⁻¹ * b * n * v,
        (RationalPoint.unipotent χ).mul_mem hb v.property⟩
    change (n : Over.mk (𝟙 _) ⟶ G.X)⁻¹ * n' =
      ((n : Over.mk (𝟙 _) ⟶ G.X)⁻¹ * a * n) *
        ((n : Over.mk (𝟙 _) ⟶ G.X)⁻¹ * b * n * v)
    rw [heq, hu]
    simp only [mul_assoc, mul_inv_cancel_left]
  exact (inv_mul_eq_one.mp hc).symm

variable [IsAffineHom G.X.hom]

/-- The preceding normalizer reduction combines with the pointwise Levi
decompositions to give the published rational Bruhat predicate, once its
centralizer identity and unipotent covering have been established. -/
theorem hasRationalBruhatDecomposition_of_weylFactorization_of_oppositeCell
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (hcover : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      ∃ (n : normalizerPoints i)
        (u v : RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i)),
        g = u * n * v)
    (hfactor : HasUnipotentWeylFactorization i ν)
    (hcell : HasTrivialNormalizerOppositeCellIntersection i ν) :
    HasRationalBruhatDecomposition i ν :=
  hasRationalBruhatDecomposition_of_unipotent_covering_and_separation i ν hZ hcover
    (hasUnipotentNormalizerSeparation_of_weylFactorization_of_oppositeCell i ν hfactor hcell)

end Langlands.GroupScheme
