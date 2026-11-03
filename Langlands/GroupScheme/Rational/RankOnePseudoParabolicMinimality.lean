import Langlands.GroupScheme.Rational.RankOneParabolicMinimality
import Langlands.GroupScheme.Rational.GenericMinimalParabolicReduction
import Langlands.GroupScheme.Rational.CocharacterMaximalSplitTorusProof
import Langlands.GroupScheme.Rational.MinimalPseudoParabolic
import Langlands.GroupScheme.Reductive.TrivialUnipotentRadical
import Langlands.GroupScheme.SubgroupFunctor.FppfProductTrivial

/-! # Rank-one minimality among arbitrary ground-field pseudo-parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- In a smooth connected affine group with trivial ground-field radical,
every closed representative of a dynamic parabolic is pseudo-parabolic. -/
theorem Dynamic.isPseudoParabolicSubgroup_of_trivialUnipotentRadical
    (hR : HasTrivialUnipotentRadical G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {P : GroupScheme (Spec (CommRingCat.of k))} (j : P ⟶ G)
    (hjc : IsClosedSubgroup j) (hj : (Dynamic.parabolic χ).IsRepresentedBy j) :
    IsPseudoParabolicSubgroup j := by
  refine ⟨inferInstance, inferInstance, inferInstance,
    Grp.trivial _, kernelUnit G, χ, isUnipotentRadical_kernelUnit G hR, ?_⟩
  rw [range_kernelUnit, ← hj.2]
  exact SubgroupFunctor.IsFppfProduct.range_bot j hjc

namespace RelativeRoot

section CommonTorus

variable (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (a : characterLattice T)
    (hcyclic : ∀ α ∈ relativeRoots i, ∃ n : ℤ, α = n • a)
    (ν : cocharacterLattice T) (hν : 0 < latticePairing T a ν)
    (hproper : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≠ ⊤)
    (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G)
    (hjc : IsClosedSubgroup j)
    (hj : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    [Smooth P.X.hom] [ConnectedSpace P.X.left]

include hconj hi hcyclic hν hproper hjc hj

/-- Common-torus conjugacy upgrades same-torus rank-one minimality to every
ground-field cocharacter. Conjugacy and connectedness of the larger
representative remain explicit hypotheses. -/
theorem rankOne_dynamicParabolic_eq_of_le_of_conjugacy
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hle : Dynamic.parabolic χ ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) :
    Dynamic.parabolic χ =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) := by
  obtain ⟨g, eta, hg, hχ⟩ :=
    exists_conjugate_cocharacter_on_torus_of_parabolic_le
      cocharacterMaximalSplitTorus hconj k G T i hi ν P j hjc hj χ hle
  have hinv :
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).comap (G.innerIso g).hom =
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) :=
    SubgroupFunctor.comap_innerIso_hom_eq_of_mem _ hg
  have hχcomap := Dynamic.parabolic_eq_comap_of_iso χ (G.innerIso g)
  rw [hχ] at hχcomap
  have heta :
      Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) := by
    apply (SubgroupFunctor.comap_iso_le_comap_iso_iff (G.innerIso g)).mp
    rw [← hχcomap, hinv]
    exact hle
  have heq := rankOneParabolic_eq_of_le hi.isSplitSubtorus.1 i a hcyclic
    ν eta hν hproper heta
  rw [heq, hinv] at hχcomap
  exact hχcomap

/-- The actual inclusion-compatible isomorphism for an arbitrary smaller
dynamic parabolic in the cyclic-root situation. -/
def rankOneParabolicIsoOfLEOfConjugacy
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hle : Dynamic.parabolic χ ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i))
    {Q : GroupScheme (Spec (CommRingCat.of k))} (l : Q ⟶ G)
    (hl : (Dynamic.parabolic χ).IsRepresentedBy l) : Q ≅ P :=
  hl.isoOfIsRepresentedBy
    (by rw [rankOne_dynamicParabolic_eq_of_le_of_conjugacy
          hconj T i hi a hcyclic ν hν hproper P j hjc hj χ hle]
        exact hj)

/-- The arbitrary-cocharacter rank-one isomorphism respects the ambient
subgroup inclusions. -/
theorem rankOneParabolicIsoOfLEOfConjugacy_hom_comp
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hle : Dynamic.parabolic χ ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i))
    {Q : GroupScheme (Spec (CommRingCat.of k))} (l : Q ⟶ G)
    (hl : (Dynamic.parabolic χ).IsRepresentedBy l) :
    (rankOneParabolicIsoOfLEOfConjugacy
      hconj T i hi a hcyclic ν hν hproper P j hjc hj χ hle l hl).hom ≫ j = l :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- A pseudo-parabolic representative of a proper cyclic-root dynamic
parabolic is minimal among all ground-field pseudo-parabolic subgroups,
under the explicit smooth maximal-split-torus conjugacy input. -/
theorem isMinimalPseudoParabolic_of_rankOne_dynamicParabolic
    (hP : IsPseudoParabolicSubgroup j) : IsMinimalPseudoParabolicSubgroup j := by
  refine ⟨hP, ?_⟩
  intro Q l hl hle
  obtain ⟨χ, hχ⟩ := hl.exists_cocharacter_le
  have heq := rankOne_dynamicParabolic_eq_of_le_of_conjugacy
    hconj T i hi a hcyclic ν hν hproper P j hjc hj χ
    (by rw [hj.2] at hle; exact hχ.trans hle)
  apply le_antisymm hle
  rw [hj.2, ← heq]
  exact hχ

/-- In the pseudo-reductive case, radical triviality supplies the
pseudo-parabolic presentation required by the preceding minimality result. -/
theorem isMinimalPseudoParabolic_of_rankOne_of_trivialUnipotentRadical
    (hR : HasTrivialUnipotentRadical G) : IsMinimalPseudoParabolicSubgroup j :=
  isMinimalPseudoParabolic_of_rankOne_dynamicParabolic
    hconj T i hi a hcyclic ν hν hproper P j hjc hj
    (Dynamic.isPseudoParabolicSubgroup_of_trivialUnipotentRadical hR _ j hjc hj)

end CommonTorus
end RelativeRoot
end Langlands.GroupScheme
