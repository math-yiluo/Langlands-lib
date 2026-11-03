import Langlands.GroupScheme.AutomorphicAction.SemidirectFactorization
import Langlands.GroupScheme.Rational.SemigroupSemidirectProducts
import Langlands.GroupScheme.Rational.SemigroupProductIsoTransport

/-! # Exact semigroup products from compatible actual subgroup factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section Factorization

variable {B : Scheme.{u}} {K N P L : GroupScheme B}
    (i : N ⟶ P) (j : K ⟶ P) [Mono i.hom.hom]
    (hn : (SubgroupFunctor.range i).IsNormalizedBy (SubgroupFunctor.range j))

/-- The actual normalized-conjugation action satisfies the factor equation. -/
theorem normalizedSubgroupAction_comp (T : Over B) (q : T ⟶ K.X)
    (n : T ⟶ N.X) :
    (AutomorphicAction.ofNormalizedConjugation i j hn).act q n ≫ i.hom.hom =
      (q ≫ j.hom.hom) * (n ≫ i.hom.hom) * (q ≫ j.hom.hom)⁻¹ :=
  SubgroupFunctor.lift_comp_normalizedConjugation_comp i j hn q n

/-- Recover the semidirect group-scheme factorization of a supplied actual
subgroup multiplication isomorphism, using its normalized conjugation action. -/
def normalizedSubgroupFactorIso [IsIso (subgroupMultiplication i j)] :
    (AutomorphicAction.ofNormalizedConjugation i j hn).semidirectProduct ≅ P :=
  AutomorphicAction.semidirectFactorIso
    (AutomorphicAction.ofNormalizedConjugation i j hn) i j
    (normalizedSubgroupAction_comp i j hn)

/-- The recovered factorization has exactly the original multiplication map. -/
@[simp] theorem normalizedSubgroupFactorIso_hom [IsIso (subgroupMultiplication i j)] :
    (normalizedSubgroupFactorIso i j hn).hom.hom.hom = subgroupMultiplication i j :=
  AutomorphicAction.semidirectFactorHom_hom
    (AutomorphicAction.ofNormalizedConjugation i j hn) i j
    (normalizedSubgroupAction_comp i j hn)

variable (b : AutomorphicAction L P)
    (hstable : b.IsStable (SubgroupFunctor.range i))
    (hfixed : ∀ (T : Over B) (s : T ⟶ L.X) (q : T ⟶ K.X),
      b.act s (q ≫ j.hom.hom) = q ≫ j.hom.hom)

include hfixed in
/-- An external action preserving the normal factor and fixing the acting
factor commutes with its actual normalized conjugation action. -/
theorem normalizedSubgroupActions_commute
    (T : Over B) (s : T ⟶ L.X) (q : T ⟶ K.X) (n : T ⟶ N.X) :
    (b.onRepresentedSubgroup i ⟨inferInstance, rfl⟩ hstable).act s
        ((AutomorphicAction.ofNormalizedConjugation i j hn).act q n) =
      (AutomorphicAction.ofNormalizedConjugation i j hn).act q
        ((b.onRepresentedSubgroup i ⟨inferInstance, rfl⟩ hstable).act s n) :=
  AutomorphicAction.semidirectFactor_commuting
    (AutomorphicAction.ofNormalizedConjugation i j hn) i j
    (normalizedSubgroupAction_comp i j hn) b
    (b.onRepresentedSubgroup i ⟨inferInstance, rfl⟩ hstable)
    (fun _ s n => b.onRepresentedSubgroup_act_comp i ⟨inferInstance, rfl⟩ hstable s n)
    hfixed T s q n

include hfixed in
/-- The actual factorization intertwines the lifted and ambient external
actions on every test scheme. -/
theorem normalizedSubgroupFactorIso_equivariant [IsIso (subgroupMultiplication i j)]
    (T : Over B) (s : T ⟶ L.X)
    (z : T ⟶ (AutomorphicAction.ofNormalizedConjugation i j hn).semidirectProduct.X) :
    ((AutomorphicAction.ofNormalizedConjugation i j hn).semidirectLift
        (b.onRepresentedSubgroup i ⟨inferInstance, rfl⟩ hstable)
        (normalizedSubgroupActions_commute i j hn b hstable hfixed)).act s z ≫
          (normalizedSubgroupFactorIso i j hn).hom.hom.hom =
      b.act s (z ≫ (normalizedSubgroupFactorIso i j hn).hom.hom.hom) :=
  AutomorphicAction.semidirectFactorHom_equivariant
    (AutomorphicAction.ofNormalizedConjugation i j hn) i j
    (normalizedSubgroupAction_comp i j hn) b
    (b.onRepresentedSubgroup i ⟨inferInstance, rfl⟩ hstable)
    (fun _ s n => b.onRepresentedSubgroup_act_comp i ⟨inferInstance, rfl⟩ hstable s n)
    hfixed (normalizedSubgroupActions_commute i j hn b hstable hfixed) T s z

end Factorization

section OrderedProducts

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {K N P : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom K.X.hom] [IsAffineHom N.X.hom] [IsAffineHom P.X.hom]
    [Smooth K.X.hom] [Smooth N.X.hom]
    [ConnectedSpace K.X.left] [ConnectedSpace N.X.left]
    (b : AutomorphicAction S.toGrp P) (i : N ⟶ P) (j : K ⟶ P)
    [Mono i.hom.hom] [IsIso (subgroupMultiplication i j)]
    (hn : (SubgroupFunctor.range i).IsNormalizedBy (SubgroupFunctor.range j))
    (hstable : b.IsStable (SubgroupFunctor.range i))
    (hfixed : ∀ (T : Over (Spec (CommRingCat.of k)))
      (s : T ⟶ S.X) (q : T ⟶ K.X),
      b.act s (q ≫ j.hom.hom) = q ≫ j.hom.hom)

include hn hfixed in
/-- A supplied compatible actual subgroup factorization transfers the exact
ordered semigroup products of its normal factor to the ambient action. -/
theorem hasOrderedSemigroupProducts_of_subgroup_factorization
    (hS : IsSplitTorus S.toGrp)
    (hfun : SemigroupFunctorialityStatement.{u})
    (hinter : SemigroupIntersectionStatement.{u})
    (hN : HasOrderedSemigroupProducts
      (b.onRepresentedSubgroup i ⟨inferInstance, rfl⟩ hstable)) :
    HasOrderedSemigroupProducts b := by
  let a := AutomorphicAction.ofNormalizedConjugation i j hn
  let c := b.onRepresentedSubgroup i ⟨inferInstance, rfl⟩ hstable
  have hcomm := normalizedSubgroupActions_commute i j hn b hstable hfixed
  have hproducts := hasOrderedSemigroupProducts_semidirect a c hcomm hS hfun hinter hN
  exact hproducts.map_equivariant_iso (a.semidirectLift c hcomm) b
    (normalizedSubgroupFactorIso i j hn)
    (normalizedSubgroupFactorIso_equivariant i j hn b hstable hfixed)

end OrderedProducts

end Langlands.GroupScheme.RelativeRoot
