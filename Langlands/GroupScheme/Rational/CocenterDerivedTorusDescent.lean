import Langlands.GroupScheme.Rational.CoweightCocenterCharacters
import Langlands.GroupScheme.Rational.CocenterCoweightDescent
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.FppfQuotientComparison

/-! # Actual based cocenter descent from compatible derived tori -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable (k E : Type u) [Field k] [Field E] [Algebra k E]
    {G M D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))}

local instance derivedDescentBaseChangeAffine
    (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj H).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd H.X.hom (algebraBaseMap k E))
  infer_instance

local instance derivedDescentBaseChangeFiniteType
    (H : GroupScheme (Spec (CommRingCat.of k))) [LocallyOfFiniteType H.X.hom] :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k E)).obj H).X.hom := by
  change LocallyOfFiniteType
    (CategoryTheory.Limits.pullback.snd H.X.hom (algebraBaseMap k E))
  infer_instance

/-- Compatible actual derived-torus geometry constructs the actual character
image and hence the based cocenter descent data for the supplied fixed coweight.
The descended quotient and full derived-subgroup predicates are transported,
rather than assumed again over the extension field. -/
def cocenterRootDescentOfDerivedTorus
    (t : T.toGrp ⟶ M) (j : M ⟶ G)
    (hM : IsConnectedReductive M) (d : D ⟶ M) (hd : IsDerivedSubgroup d)
    (q : M ⟶ Q.toGrp)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q)
    (hD : IsSemisimple ((GroupScheme.baseChange (algebraBaseMap k E)).obj D))
    (S : CommGroupScheme (Spec (CommRingCat.of E)))
    (a : S.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap k E)).obj D)
    (ha : IsMaximalTorus a)
    (φ : S ⟶ (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
    (hsquare : CommGroupScheme.groupHom φ ≫
        (GroupScheme.baseChange (algebraBaseMap k E)).map t =
      a ≫ (GroupScheme.baseChange (algebraBaseMap k E)).map d)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp)
    (hS : IsSplitTorus S.toGrp)
    (hQ : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj Q).toGrp)
    (ht : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map t))
    (hi : IsClosedSubgroup
      ((GroupScheme.baseChange (algebraBaseMap k E)).map (t ≫ j)))
    {J : Type u} [Finite J] {K : Type v} {L : Type w}
    (P : RootDatum J
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)))
    [P.IsReduced]
    (R : RootDatum K
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)))
    (U : RootDatum L (characterLattice S) (cocharacterLattice S))
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map (t ≫ j)) P)
    (hR : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map t) R)
    (hU : IsRootDatumOf a U)
    (hprod : Surjective (subgroupProductMap
      ((GroupScheme.baseChange (algebraBaseMap k E)).map d)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map t)).left)
    (hI : IsTorus (subgroupIntersection
      ((GroupScheme.baseChange (algebraBaseMap k E)).map t)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map d)))
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
    (hν : ∀ σ : E ≃ₐ[k] E, cocharacterLattice.galoisRepresentation k E T σ ν = ν)
    (hroots : relativeRoots (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
        ((GroupScheme.baseChange (algebraBaseMap k E)).map t) =
      {α | α ∈ relativeRoots
        (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
        ((GroupScheme.baseChange (algebraBaseMap k E)).map (t ≫ j)) ∧
          latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
            α ν = 0}) :
    {B : P.Base // CocenterRootDescentData k E (Additive.ofMul (t ≫ q) : T ⟶ Q) P B
      {p : B.support | P.root' p ν = 0}} := by
  let b := algebraBaseMap k E
  let bc := GroupScheme.baseChange b
  have hME : IsConnectedReductive (bc.obj M) :=
    connectedReductiveFieldExtensionStatement k E M hM
  have hdE : IsDerivedSubgroup (bc.map d) :=
    (derivedSubgroupFieldBaseChange k E M D d hd).1
  have hqE : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (bc.map d)) (bc.map q) := by
    simpa only [bc, SubgroupFunctor.range_baseChangeHom] using hq.baseChange b
  have hquot :
      (CommGroupScheme.baseChange b).map (Additive.ofMul (t ≫ q) : T ⟶ Q) =
        (Additive.ofMul (bc.map t ≫ bc.map q) :
          (CommGroupScheme.baseChange b).obj T ⟶ (CommGroupScheme.baseChange b).obj Q) := by
    apply Additive.toMul.injective
    exact bc.map_comp t q
  have hc := characterLattice.cocenter_coweight_character_comparison hP hR
    (bc.map j) (bc.map_comp t j).symm hME (bc.map d) hdE hD
    a ha ht φ hsquare (bc.map q) hqE hT hS hQ hi hU hprod hI ν hroots
  apply coweightCocenterRootDescent k E
    (Additive.ofMul (t ≫ q) : T ⟶ Q) (t ≫ j) P hT hi hP ν hν
  · change Function.Injective (characterLattice.precompose
      ((CommGroupScheme.baseChange b).map (Additive.ofMul (t ≫ q) : T ⟶ Q))).toIntLinearMap
    rw [hquot]
    exact hc.1
  · change ∀ x, x ∈ (characterLattice.precompose
        ((CommGroupScheme.baseChange b).map (Additive.ofMul (t ≫ q) : T ⟶ Q))).toIntLinearMap.range ↔
      ∀ p, P.root' p ν = 0 → P.toLinearMap x (P.coroot p) = 0
    rw [hquot]
    exact hc.2

end Langlands.GroupScheme
