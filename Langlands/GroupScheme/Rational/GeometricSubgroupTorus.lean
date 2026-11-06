import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyReduction
import Langlands.GroupScheme.Derived.MaximalSplitTorusConjugacyReduction
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # A compatible subgroup torus inside a prescribed geometric maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G D : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {F : SubgroupFunctor G} {d : D ⟶ G}

/-- Actual split maximal-torus data of a subgroup inside a prescribed
ambient torus, with its closed integral torus map retained. -/
structure CompatibleSubgroupTorus (t : T.toGrp ⟶ G) (d : D ⟶ G) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  subgroup : torus.toGrp ⟶ D
  inclusion : torus ⟶ T
  isSplit : IsSplitTorus torus.toGrp
  isMaximal : IsMaximalTorus subgroup
  inclusion_closed : IsClosedSubgroup (CommGroupScheme.groupHom inclusion)
  inclusion_comp : CommGroupScheme.groupHom inclusion ≫ t = subgroup ≫ d

/-- Over an algebraically closed field, a closed normal subgroup has an
actual split maximal torus inside any prescribed ambient maximal torus.
The prescribed ambient source and embedding are retained. -/
theorem SubgroupFunctor.IsRepresentedBy.exists_compatible_maximalTorus_of_isAlgClosed
    (hr : F.IsRepresentedBy d) (hd : IsClosedSubgroup d) (hn : F.IsNormal)
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of k))) (a : S.toGrp ⟶ D) (φ : S ⟶ T),
      IsSplitTorus S.toGrp ∧ IsMaximalTorus a ∧
        IsClosedSubgroup (CommGroupScheme.groupHom φ) ∧
          CommGroupScheme.groupHom φ ≫ t = a ≫ d := by
  have hsplit : ToriAreSplit k := fun S hS =>
    hS.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  have hconj : MaximalSplitToriAreConjugate G := by
    intro T₁ T₂ i₁ i₂ hi₁ hi₂
    exact (subgroupConjugate_iff_exists_commGroupSchemeIso i₁ i₂).mpr
      (maximalTorusConjugacy k G T₁ T₂ i₁ i₂
        (hi₁.isMaximalTorus hsplit) (hi₂.isMaximalTorus hsplit))
  obtain ⟨S, a, φ, ha, hφ, hcomp⟩ :=
    hr.maximalSplitToriContainSubgroupTori_of_conjugate hd hn hconj T t
      (ht.isMaximalSplitTorus (hsplit _ ht.1))
  exact ⟨S, a, φ, ha.1.1, ha.isMaximalTorus hsplit, hφ, hcomp.symm⟩

/-- The compatible prescribed-torus construction applies to every actual
derived subgroup, without a semisimplicity or root-datum hypothesis. -/
theorem IsDerivedSubgroup.exists_compatible_maximalTorus_of_isAlgClosed
    (hd : IsDerivedSubgroup d) (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of k))) (a : S.toGrp ⟶ D) (φ : S ⟶ T),
      IsSplitTorus S.toGrp ∧ IsMaximalTorus a ∧
        IsClosedSubgroup (CommGroupScheme.groupHom φ) ∧
          CommGroupScheme.groupHom φ ≫ t = a ≫ d :=
  hd.isRepresentedBy.exists_compatible_maximalTorus_of_isAlgClosed
    hd.1 (derivedSubgroup_isNormal G) t ht

/-- Choose the actual compatible subgroup-torus data supplied by geometric
conjugacy, retaining the prescribed ambient torus. -/
def SubgroupFunctor.IsRepresentedBy.geometricSubgroupTorus
    (hr : F.IsRepresentedBy d) (hd : IsClosedSubgroup d) (hn : F.IsNormal)
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t) : CompatibleSubgroupTorus t d :=
  Classical.choice (by
    obtain ⟨S, a, φ, hS, ha, hφ, hcomp⟩ :=
      hr.exists_compatible_maximalTorus_of_isAlgClosed hd hn t ht
    exact ⟨{
      torus := S
      subgroup := a
      inclusion := φ
      isSplit := hS
      isMaximal := ha
      inclusion_closed := hφ
      inclusion_comp := hcomp }⟩)

/-- The actual full derived subgroup has compatible geometric torus data
inside the unchanged prescribed ambient torus. -/
def IsDerivedSubgroup.geometricSubgroupTorus
    (hd : IsDerivedSubgroup d) (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t) :
    CompatibleSubgroupTorus t d :=
  hd.isRepresentedBy.geometricSubgroupTorus hd.1 (derivedSubgroup_isNormal G) t ht

end Langlands.GroupScheme
