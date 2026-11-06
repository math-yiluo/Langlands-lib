import Langlands.GroupScheme.Rational.CocenterCorootBaseChange
import Langlands.GroupScheme.Rational.CocenterCoweightDescent

/-! # Reflecting a fixed-coweight character comparison to the splitting field -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace characterLattice

/-- The exact actual character-image comparison for a supplied coweight is
preserved and reflected under every further field base map between split tori.
Both the root datum and the same coweight use canonical actual base change. -/
theorem coweight_character_comparison_baseChange_iff
    {E K : Type u} [Field E] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of E))
    {T Q : CommGroupScheme (Spec (CommRingCat.of E))}
    (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp)
    (f : T ⟶ Q) {J : Type v}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (ν : cocharacterLattice T) :
    (Function.Injective (precompose ((CommGroupScheme.baseChange b).map f)) ∧
      ∀ χ, χ ∈ (precompose ((CommGroupScheme.baseChange b).map f)).toIntLinearMap.range ↔
        ∀ p, (SplitRootDatum.baseChange b T hT P).root' p
            (cocharacterLattice.baseChange b T ν) = 0 →
          (SplitRootDatum.baseChange b T hT P).toLinearMap χ
            ((SplitRootDatum.baseChange b T hT P).coroot p) = 0) ↔
    (Function.Injective (precompose f) ∧
      ∀ χ, χ ∈ (precompose f).toIntLinearMap.range ↔
        ∀ p, P.root' p ν = 0 → P.toLinearMap χ (P.coroot p) = 0) := by
  have hzero (p : J) :
      (SplitRootDatum.baseChange b T hT P).root' p
          (cocharacterLattice.baseChange b T ν) = P.root' p ν := by
    change (SplitRootDatum.baseChange b T hT P).toLinearMap
      ((SplitRootDatum.baseChange b T hT P).root p)
      (cocharacterLattice.baseChange b T ν) = _
    rw [SplitRootDatum.baseChange_root, SplitRootDatum.baseChange_pairing]
  simpa only [Langlands.RootDatum.mem_corootAnnihilator, Set.mem_ofPred_eq, hzero]
    using coroot_character_comparison_baseChange_iff b hT hQ f P {p | P.root' p ν = 0}

end characterLattice

section Descent

variable (k E K : Type u) [Field k] [Field E] [Field K] [Algebra k E]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of E))
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))}
    (g : T ⟶ Q)
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : T.toGrp ⟶ G)
    {J : Type u} [Finite J]
    (P : RootDatum J
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)))
    [P.IsReduced]

local instance geometricDescentBaseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

/-- A character comparison verified only over a further field constructs
the actual based cocenter descent data over the original splitting field.
The coweight and the ordinary Galois actions stay over E/k. -/
def coweightCocenterRootDescentOfBaseChange
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp)
    (hQ : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj Q).toGrp)
    (hi : IsClosedSubgroup ((GroupScheme.baseChange (algebraBaseMap k E)).map i))
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
    (hν : ∀ σ : E ≃ₐ[k] E, cocharacterLattice.galoisRepresentation k E T σ ν = ν)
    (hc : Function.Injective (characterLattice.precompose
        ((CommGroupScheme.baseChange b).map
          ((CommGroupScheme.baseChange (algebraBaseMap k E)).map g))) ∧
      ∀ χ, χ ∈ (characterLattice.precompose
          ((CommGroupScheme.baseChange b).map
            ((CommGroupScheme.baseChange (algebraBaseMap k E)).map g))).toIntLinearMap.range ↔
        ∀ p, (SplitRootDatum.baseChange b _ hT P).root' p
            (cocharacterLattice.baseChange b _ ν) = 0 →
          (SplitRootDatum.baseChange b _ hT P).toLinearMap χ
            ((SplitRootDatum.baseChange b _ hT P).coroot p) = 0) :
    {B : P.Base // CocenterRootDescentData k E g P B
      {p : B.support | P.root' p ν = 0}} := by
  have hcE := (characterLattice.coweight_character_comparison_baseChange_iff
    b hT hQ ((CommGroupScheme.baseChange (algebraBaseMap k E)).map g) P ν).mp hc
  exact coweightCocenterRootDescent k E g i P hT hi hP ν hν hcE.1 hcE.2

end Descent

end Langlands.GroupScheme
