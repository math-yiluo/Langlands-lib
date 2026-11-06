import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial
import Langlands.GroupScheme.Rational.RootSubgroupStability
import Langlands.GroupScheme.Rational.WeightVectorUniqueness

/-! # Actual weight-vector coordinates on root subgroups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

section Transport

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {U V : GroupScheme (Spec (CommRingCat.of k))}
    {d : AutomorphicAction S.toGrp U} {c : AutomorphicAction S.toGrp V}
    {a : characterLattice S} {n : ℕ}
    {e : ∀ X : Over (Spec (CommRingCat.of k)),
      (X ⟶ V.X) ≃* Multiplicative (Fin n → Γ(X.left, ⊤))}

/-- Pull back weight-vector coordinates along an equivariant actual isomorphism. -/
theorem IsWeightVectorCoordinates.of_equivariantIso
    (he : IsWeightVectorCoordinates c a e) (ψ : U ≅ V)
    (hψ : ∀ (X : Over (Spec (CommRingCat.of k))) (s : X ⟶ S.X) (x : X ⟶ U.X),
      d.act s x ≫ ψ.hom.hom.hom = c.act s (x ≫ ψ.hom.hom.hom)) :
    IsWeightVectorCoordinates d a
      (fun X => ((yonedaGrp.mapIso ψ).app (op X)).groupIsoToMulEquiv.trans (e X)) := by
  constructor
  · intro X Y f x
    change (e Y ((f ≫ x) ≫ ψ.hom.hom.hom)).toAdd =
      fun l => f.left.appTop ((e X (x ≫ ψ.hom.hom.hom)).toAdd l)
    rw [Category.assoc]
    exact he.1 X Y f _
  · intro X s x
    change (e X (d.act s x ≫ ψ.hom.hom.hom)).toAdd = _
    rw [hψ]
    exact he.2 X s _

end Transport

section RootSubgroups

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- With no higher positive roots, every representative of the actual root
functor has natural vector coordinates of the original character weight. -/
theorem exists_weightVectorCoordinates_of_noHigherRoots
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    {a : characterLattice T} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a)
    {U : GroupScheme (Spec (CommRingCat.of k))} {j : U ⟶ G}
    (hj : (subgroup i a).IsRepresentedBy j) :
    ∃ (n : ℕ) (e : ∀ X : Over (Spec (CommRingCat.of k)),
      (X ⟶ U.X) ≃* Multiplicative (Fin n → Γ(X.left, ⊤))),
      IsWeightVectorCoordinates (subgroupAction i a j hj) a e := by
  let b := AutomorphicAction.conjugation i
  have hfirst : weightFiltration b a 1 = subgroup i a :=
    cyclicRootFunctorComparison k G inferInstance inferInstance T hT i a ha
  have htwo : weightFiltration b a 2 = ⊥ :=
    weightFiltration_two_eq_bot_of_noHigherRoots inferInstance hT i ha hhigh
  have hrep : (weightFiltration b a 1).IsRepresentedBy j := hfirst.symm ▸ hj
  obtain ⟨V, q, c, d, hq, hc, hjd, hqd⟩ :=
    (cyclicWeightFiltration k G inferInstance inferInstance T hT b a ha 1
      (by decide)).2 U j hrep
  let : Mono j.hom.hom := hj.1
  have hq0 : IsFppfQuotient ⊥ q := by
    simpa only [show 1 + 1 = (2 : ℕ) from rfl, htwo,
      SubgroupFunctor.comap_bot_of_mono] using hq
  have hc' : HasUniqueWeightVectorStructure c a := by simpa only [one_nsmul] using hc
  obtain ⟨n, e, he⟩ := hc'.1
  refine ⟨n, _, he.of_equivariantIso hq0.isoOfBot ?_⟩
  intro X s x
  change (subgroupAction i a j hj).act s x ≫ q.hom.hom = c.act s (x ≫ q.hom.hom)
  rw [hqd]
  congr 1
  apply (cancel_mono j.hom.hom).mp
  rw [subgroupAction_act_comp, hjd, AutomorphicAction.conjugation_act]

/-- Chosen natural coordinates, with their dimension and weight-equivariance
proof, for a supplied representative of a root functor with no higher roots. -/
def weightVectorCoordinatesOfNoHigherRoots
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    {a : characterLattice T} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a)
    {U : GroupScheme (Spec (CommRingCat.of k))} {j : U ⟶ G}
    (hj : (subgroup i a).IsRepresentedBy j) :
    Σ (n : ℕ), {e : ∀ X : Over (Spec (CommRingCat.of k)),
      (X ⟶ U.X) ≃* Multiplicative (Fin n → Γ(X.left, ⊤)) //
      IsWeightVectorCoordinates (subgroupAction i a j hj) a e} :=
  let hex := exists_weightVectorCoordinates_of_noHigherRoots hT i ha hhigh hj
  ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec⟩

/-- The scalar multiplication in these weight coordinates is independent of
the coordinates chosen. -/
theorem hasUniqueWeightVectorStructure_of_noHigherRoots
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    {a : characterLattice T} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a)
    {U : GroupScheme (Spec (CommRingCat.of k))} {j : U ⟶ G}
    (hj : (subgroup i a).IsRepresentedBy j) :
    HasUniqueWeightVectorStructure (subgroupAction i a j hj) a := by
  obtain ⟨n, e, he⟩ := weightVectorCoordinatesOfNoHigherRoots hT i ha hhigh hj
  exact hasUniqueWeightVectorStructure_of_coordinates hT ha he

end RootSubgroups

end Langlands.GroupScheme.RelativeRoot
