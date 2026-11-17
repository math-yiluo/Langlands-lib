import Langlands.GroupScheme.Reductive.CenterExistenceProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.CommutativeSubgroupIntersection

/-! # The full scheme-theoretic centre inside a chosen maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {T : CommGroupScheme (Spec (CommRingCat.of K))}

/-- A commutative representative of the full centre together with its
factorization through a specified maximal torus. -/
structure CenterInMaximalTorus (i : T.toGrp ⟶ G) where
  group : CommGroupScheme (Spec (CommRingCat.of K))
  torusMap : group ⟶ T
  isCenter : IsSchemeTheoreticCenter (CommGroupScheme.groupHom torusMap ≫ i)

/-- Construct the full centre in any chosen maximal torus of a connected
reductive field group, retaining the full subgroup scheme. -/
def centerInMaximalTorus (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) :
    CenterInMaximalTorus i := by
  classical
  have hex : Nonempty (CenterInMaximalTorus i) := by
    obtain ⟨Z, z, hz⟩ := schemeTheoreticCenterExistence K G hG
    have : IsClosedImmersion z.hom.hom.left := hz.1
    have : Mono z.hom.hom := Over.mono_of_mono_left _
    let C := commutativeSubgroupIntersection i z
    let w : C.toGrp ⟶ T.toGrp := commutativeSubgroupIntersectionFst i z
    have hw : IsClosedImmersion w.hom.hom.left :=
      isClosedSubgroup_commutativeSubgroupIntersectionFst i z hz.1
    have : IsClosedImmersion i.hom.hom.left := hi.2.1
    have hclosed : IsClosedSubgroup (w ≫ i) := by
      change IsClosedImmersion (w.hom.hom.left ≫ i.hom.hom.left)
      infer_instance
    have hle : center G ≤ SubgroupFunctor.range i := by
      rw [← maximalTorusCentralizer K G hG T i hi]
      intro U g hg V a t
      exact hg V a (t ≫ i.hom.hom)
    refine ⟨⟨C, Additive.ofMul w, hclosed, ?_⟩⟩
    change SubgroupFunctor.range (commutativeSubgroupIntersectionFst i z ≫ i) =
      center G
    rw [range_commutativeSubgroupIntersection, hz.2]
    apply le_antisymm
    · intro U g hg
      exact hg.2
    · intro U g hg
      exact ⟨hle U hg, hg⟩
  exact Classical.choice hex

end Langlands.GroupScheme
