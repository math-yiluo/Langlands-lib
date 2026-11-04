import Langlands.GroupScheme.Dynamic.NoncentralSolvableQuotientSection
import Langlands.GroupScheme.Dynamic.GeometricQuotientNormalizer
import Langlands.GroupScheme.Rational.CentralRootRestriction

/-! # Nonidentity normalizers from roots and solvable homogeneous quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G P : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]

/-- A split torus with an actual relative root has noncentral image. -/
theorem not_isCentral_of_relativeRoot [LocallyOfFiniteType G.X.hom]
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots i) :
    ¬ IsCentral i := by
  intro hc
  have hc' : IsCentral (CommGroupScheme.groupHom (𝟙 T) ≫ i) := by
    change IsCentral ((𝟙 T.toGrp) ≫ i)
    simpa only [Category.id_comp] using hc
  have hz := root_restrict_eq_zero_of_isCentral i (𝟙 T) hT hc' hχ
  apply (mem_relativeRoots.mp hχ).1
  simpa only [Category.id_comp] using hz

variable [IsAlgClosed k]

/-- An actual root supplies a nonfixed rational lift of a solvable quotient,
under the explicit normal-solvable-torus input. -/
def Dynamic.nonfixedQuotientLiftOfRelativeRoot_of_structural
    (htorus : AlgClosedReductiveNormalSolvableTorusStatement.{u})
    (hG : IsPseudoReductive G)
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots i)
    (j : P ⟶ G) (hj : IsClosedSubgroup j) (hP : IsSolvableGroupScheme P)
    (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V) :
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X //
      ¬ ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib).restrict i).IsFixed
        (g ≫ q)} := by
  have : Smooth G.X.hom := hG.smooth
  have : Smooth T.toGrp.X.hom := hT.smooth
  have : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  have : ConnectedSpace T.toGrp.X.left := hT.connectedSpace
  exact Dynamic.nonfixedQuotientLiftOfNoncentralSubgroup_of_structural htorus hG i
    (not_isCentral_of_relativeRoot i hT hχ) j hj hP q hfib

/-- A noncentral maximal torus factoring through a closed solvable stabilizer
gives a nonidentity Weyl class from smooth proper quotient geometry. -/
def nonidentityNormalizerOfNoncentralSolvableQuotient_of_structural
    (htorus : AlgClosedReductiveNormalSolvableTorusStatement.{u})
    (hG : IsPseudoReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) (hnc : ¬ IsCentral i)
    (j : P ⟶ G) (hj : IsClosedSubgroup j) (hP : IsSolvableGroupScheme P)
    (f : T.toGrp ⟶ P) (hf : f ≫ j = i)
    (hconj : MaximalToriAreConjugate P) (q : G.X ⟶ Q)
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V) :
    {w : normalizerPoints i // (QuotientGroup.mk w : relativeWeylGroup i) ≠ 1} := by
  have : Smooth G.X.hom := hG.smooth
  have : Smooth T.toGrp.X.hom := hi.1.smooth
  have : IsAffineHom T.toGrp.X.hom := hi.2.1.isAffineHom_source
  have : ConnectedSpace T.toGrp.X.left := hi.1.connectedSpace
  let g := Dynamic.nonfixedQuotientLiftOfNoncentralSubgroup_of_structural
    htorus hG i hnc j hj hP q hfib
  exact nonidentityNormalizerOfNonfixedSmoothProperQuotient i hi j hj f hf hconj
    q hfib g.val g.property

/-- A relative root replaces the noncentrality input in the solvable-quotient
normalizer construction. No supplied movement or nonfixed section is needed. -/
def nonidentityNormalizerOfRootedSolvableQuotient_of_structural
    (htorus : AlgClosedReductiveNormalSolvableTorusStatement.{u})
    (hG : IsPseudoReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots i)
    (j : P ⟶ G) (hj : IsClosedSubgroup j) (hP : IsSolvableGroupScheme P)
    (f : T.toGrp ⟶ P) (hf : f ≫ j = i)
    (hconj : MaximalToriAreConjugate P) (q : G.X ⟶ Q)
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V) :
    {w : normalizerPoints i // (QuotientGroup.mk w : relativeWeylGroup i) ≠ 1} := by
  have : Smooth G.X.hom := hG.smooth
  exact nonidentityNormalizerOfNoncentralSolvableQuotient_of_structural
    htorus hG i hi (not_isCentral_of_relativeRoot i hT hχ)
      j hj hP f hf hconj q hfib

end Langlands.GroupScheme
