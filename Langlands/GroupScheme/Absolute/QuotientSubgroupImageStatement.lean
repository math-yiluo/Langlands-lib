import Langlands.GroupScheme.Absolute.Borel

/-! # Statement: quotient maps and parabolic, Borel, maximal unipotent and maximal toric subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Proposition 17.20. Let `q : G ⟶ Q` be a quotient map (flat and surjective) of smooth
connected affine groups over an algebraically closed field `k`.
* If `i : H ⟶ G` is a parabolic subgroup (resp. a Borel subgroup, resp. a maximal smooth connected
  unipotent subgroup, resp. a maximal torus), then so is the image `q(H)`. The image is encoded as
  a smooth closed subgroup `j : H' ⟶ Q` with `i ≫ q = f ≫ j` for a homomorphism `f : H ⟶ H'`
  whose underlying map is surjective.
* Every parabolic subgroup (resp. Borel subgroup, resp. maximal smooth connected unipotent
  subgroup, resp. maximal torus) of `Q` is the image of one of `G` of the same kind. -/
def AlgClosedQuotientSubgroupImageStatement : Prop :=
  let IsMaximalUnipotent :
      ∀ {k : Type u} [Field k] {U G : GroupScheme (Spec (CommRingCat.of k))}, (U ⟶ G) → Prop :=
    fun {k} _ {U G} u => IsClosedSubgroup u ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧
      IsUnipotent U ∧
      ∀ (U' : GroupScheme (Spec (CommRingCat.of k))) (u' : U' ⟶ G) (f : U ⟶ U'),
        IsClosedSubgroup u' → Smooth U'.X.hom → ConnectedSpace U'.X.left → IsUnipotent U' →
          f ≫ u' = u → IsIso f
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G Q : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
    (q : G ⟶ Q), Flat q.hom.hom.left → Surjective q.hom.hom.left →
    (∀ (H H' : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G) (j : H' ⟶ Q) (f : H ⟶ H'),
      IsClosedSubgroup j → Smooth H'.X.hom → Surjective f.hom.hom.left → i ≫ q = f ≫ j →
        (IsParabolicSubgroup i → IsParabolicSubgroup j) ∧
        (IsBorelSubgroup i → IsBorelSubgroup j) ∧
        (IsMaximalUnipotent i → IsMaximalUnipotent j)) ∧
    (∀ (T S : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (j : S.toGrp ⟶ Q) (f : T ⟶ S),
      IsClosedSubgroup j → Smooth S.X.hom → Surjective (CommGroupScheme.groupHom f).hom.hom.left →
        i ≫ q = CommGroupScheme.groupHom f ≫ j → IsMaximalTorus i → IsMaximalTorus j) ∧
    (∀ (H' : GroupScheme (Spec (CommRingCat.of k))) (j : H' ⟶ Q), IsParabolicSubgroup j →
      ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G) (f : H ⟶ H'),
        IsParabolicSubgroup i ∧ Surjective f.hom.hom.left ∧ i ≫ q = f ≫ j) ∧
    (∀ (H' : GroupScheme (Spec (CommRingCat.of k))) (j : H' ⟶ Q), IsBorelSubgroup j →
      ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G) (f : H ⟶ H'),
        IsBorelSubgroup i ∧ Surjective f.hom.hom.left ∧ i ≫ q = f ≫ j) ∧
    (∀ (H' : GroupScheme (Spec (CommRingCat.of k))) (j : H' ⟶ Q), IsMaximalUnipotent j →
      ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G) (f : H ⟶ H'),
        IsMaximalUnipotent i ∧ Surjective f.hom.hom.left ∧ i ≫ q = f ≫ j) ∧
    (∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (j : S.toGrp ⟶ Q), IsMaximalTorus j →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G) (f : T ⟶ S),
        IsMaximalTorus i ∧ Surjective (CommGroupScheme.groupHom f).hom.hom.left ∧
          i ≫ q = CommGroupScheme.groupHom f ≫ j)

end Langlands.GroupScheme
