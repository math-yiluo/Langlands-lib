import Langlands.GroupScheme.Rational.MaximalSplitTorusStatement
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.SubgroupConjugacy

/-! # Reduction of maximal split torus conjugacy to a closed subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Any two maximal split tori of this group are conjugate by a rational point. -/
def MaximalSplitToriAreConjugate (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (T T' : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G),
    IsMaximalSplitTorus i → IsMaximalSplitTorus i' → SubgroupConjugate i i'

variable {G H : GroupScheme (Spec (CommRingCat.of k))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Conjugacy of maximal split tori is invariant under an ambient group isomorphism. -/
theorem MaximalSplitToriAreConjugate.of_iso (hG : MaximalSplitToriAreConjugate G)
    (e : G ≅ H) : MaximalSplitToriAreConjugate H := by
  intro T T' i i' hi hi'
  have h := hG T T' (i ≫ e.inv) (i' ≫ e.inv)
    (hi.comp_iso e.symm) (hi'.comp_iso e.symm)
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h.postcomp e.hom

/-- If two ambient maximal split tori factor through a closed subgroup in which
maximal split tori are conjugate, they are conjugate in the ambient group. -/
theorem subgroupConjugate_of_closed_factorizations
    (hH : MaximalSplitToriAreConjugate H) (j : H ⟶ G) (hj : IsClosedSubgroup j)
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (hi' : IsMaximalSplitTorus i')
    (f : T.toGrp ⟶ H) (f' : T'.toGrp ⟶ H)
    (hf : f ≫ j = i) (hf' : f' ≫ j = i') :
    SubgroupConjugate i i' := by
  have h := hH T T' f f'
    (IsMaximalSplitTorus.of_comp hj (hf.symm ▸ hi))
    (IsMaximalSplitTorus.of_comp hj (hf'.symm ▸ hi'))
  simpa only [hf, hf'] using h.postcomp j

/-- The same reduction applies when both torus embeddings are first conjugated
into the closed subgroup, using possibly different rational points. -/
theorem subgroupConjugate_of_conjugate_closed_factorizations
    (hH : MaximalSplitToriAreConjugate H) (j : H ⟶ G) (hj : IsClosedSubgroup j)
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (hi' : IsMaximalSplitTorus i')
    (g g' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (f : T.toGrp ⟶ H) (f' : T'.toGrp ⟶ H)
    (hf : f ≫ j = i ≫ (G.innerIso g).hom)
    (hf' : f' ≫ j = i' ≫ (G.innerIso g').hom) :
    SubgroupConjugate i i' := by
  have h := subgroupConjugate_of_closed_factorizations hH j hj
    (hi.comp_iso (G.innerIso g)) (hi'.comp_iso (G.innerIso g')) f f' hf hf'
  exact ((SubgroupConjugate.conjugate i g).trans h).trans
    (SubgroupConjugate.conjugate i' g').symm

/-- A single closed subgroup suffices if every ambient maximal split torus can
be conjugated into it and its own maximal split tori are conjugate. -/
theorem MaximalSplitToriAreConjugate.of_closed_overgroup
    (hH : MaximalSplitToriAreConjugate H) (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hlift : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : T.toGrp ⟶ G), IsMaximalSplitTorus i →
      ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
        (f : T.toGrp ⟶ H), f ≫ j = i ≫ (G.innerIso g).hom) :
    MaximalSplitToriAreConjugate G := by
  intro T T' i i' hi hi'
  obtain ⟨g, f, hf⟩ := hlift T i hi
  obtain ⟨g', f', hf'⟩ := hlift T' i' hi'
  exact subgroupConjugate_of_conjugate_closed_factorizations
    hH j hj hi hi' g g' f f' hf hf'

/-- The published smooth-group statement is exactly the universal assertion of
the individual-group conjugacy property. -/
theorem smoothMaximalSplitTorusConjugacyStatement_iff :
    SmoothMaximalSplitTorusConjugacyStatement.{u} ↔
      ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
        [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
        MaximalSplitToriAreConjugate G := Iff.rfl

end Langlands.GroupScheme
