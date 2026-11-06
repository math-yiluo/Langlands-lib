import Langlands.GroupScheme.Reductive.RankOneWeylCriterionProof
import Langlands.GroupScheme.Reductive.IdentityComponentLocusOpenDescent
import Langlands.GroupScheme.Torus.GeometricRootProfiles
import Langlands.GroupScheme.Torus.GeometricTransporterSections

/-! # Relative rank-one reductive good neighbourhoods -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

variable {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)

local instance rankOneNeighbourhood_smooth_geometricFiber (t : Spec (CommRingCat.of r)) :
    Smooth (geometricFiber G t).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ t)))

local instance rankOneNeighbourhood_affine_geometricFiber (t : Spec (CommRingCat.of r)) :
    IsAffineHom (geometricFiber G t).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ t)))

/-- An actual relative transporter section and the actual rank-one root profile
at one fibre construct a good open neighbourhood using the proved field criterion.
The profile and section inputs remain explicit. -/
def rankOneIdentityComponentReductiveNeighbourhood
    (hi : IsClosedSubgroup i) (s : Spec (CommRingCat.of r))
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i)
    (m : I → ℤ) (hm : m ≠ 0)
    (hroots : ∀ a : I → ℤ,
      a ∈ geometricExponentRoots I G i s ↔ a = m ∨ a = -m)
    (hpos : Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))
      (weightSpace (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s)
        (exponentCharacter _ I m)) = 1)
    (hneg : Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))
      (weightSpace (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s)
        (exponentCharacter _ I (-m))) = 1)
    (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) (he : e m = -m)
    {g : Spec (CommRingCat.of r) ⟶ G.X.left}
    (hg : g ≫ G.X.hom = 𝟙 _)
    (d : RelativeIdentityComponent.SectionIdentityNeighbourhoodData G g s)
    (htrans : PointwiseSchemeAction.IsTransporter
      ((exponentIso (Spec (CommRingCat.of r)) I e).hom ≫ i) i
      (show Over.mk (𝟙 _) ⟶ G.X from Over.homMk g hg)) :
    IdentityComponentReductiveOpenNeighbourhood G s := by
  classical
  let U := Classical.choose (exists_open_geometricRootProfiles_eq I G i s)
  have hU : IsOpen U := (Classical.choose_spec
    (exists_open_geometricRootProfiles_eq I G i s)).1
  have hsU : s ∈ U := (Classical.choose_spec
    (exists_open_geometricRootProfiles_eq I G i s)).2.1
  have hconst := (Classical.choose_spec
    (exists_open_geometricRootProfiles_eq I G i s)).2.2
  refine
    { neighbourhood := ⟨U ∩ (geometricSelfCentralizingTorusLocus I G i ∩ d.neighbourhood),
        hU.inter ((isOpen_geometricSelfCentralizingTorusLocus I G i hi).inter
          d.neighbourhood.isOpen)⟩
      mem_neighbourhood := ⟨hsU, hself, d.mem_neighbourhood⟩
      subset_locus := ?_ }
  intro t ht
  obtain ⟨hrootst, hdimt⟩ := hconst t ht.1
  let k := AlgebraicClosure ((Spec (CommRingCat.of r)).residueField t)
  let α : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I) :=
    exponentCharacter _ I m
  have hα : α ≠ 0 := by
    change exponentCharacter _ I m ≠ 0
    rw [exponentCharacter_eq_characterLatticeEquiv_symm]
    exact fun hz => hm ((AddEquiv.map_eq_zero_iff _).mp hz)
  have hminus :
      exponentCharacter (Spec (CommRingCat.of k)) I (-m) = -α :=
    (exponentCharacterLinear _ I).map_neg m
  have hsupport (β : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)) :
      β ∈ roots (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i t) ↔
        β = α ∨ β = -α := by
    obtain ⟨a, ha⟩ := (characterLatticeEquiv k I).symm.surjective β
    have hβ : exponentCharacter (Spec (CommRingCat.of k)) I a = β :=
      (exponentCharacter_eq_characterLatticeEquiv_symm I k a).trans ha
    rw [← hβ]
    have hbase : a ∈ geometricExponentRoots I G i t ↔ a = m ∨ a = -m := by
      rw [hrootst]
      exact hroots a
    have hposEq : exponentCharacter (Spec (CommRingCat.of k)) I a = α ↔ a = m := by
      change exponentCharacter _ I a = exponentCharacter _ I m ↔ _
      rw [exponentCharacter_eq_characterLatticeEquiv_symm,
        exponentCharacter_eq_characterLatticeEquiv_symm]
      exact (characterLatticeEquiv k I).symm.injective.eq_iff
    have hnegEq : exponentCharacter (Spec (CommRingCat.of k)) I a = -α ↔ a = -m := by
      rw [← hminus, exponentCharacter_eq_characterLatticeEquiv_symm,
        exponentCharacter_eq_characterLatticeEquiv_symm]
      exact (characterLatticeEquiv k I).symm.injective.eq_iff
    exact hbase.trans (or_congr hposEq hnegEq).symm
  have hdimpos : Module.finrank k
      (weightSpace (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i t) α) = 1 :=
    (hdimt m).trans hpos
  have hdimneg : Module.finrank k
      (weightSpace (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i t) (-α)) = 1 := by
    rw [← hminus]
    exact (hdimt (-m)).trans hneg
  let q := geometricPoint (Spec (CommRingCat.of r)) t
  have hq : Set.range q ⊆ (d.neighbourhood : Set (Spec (CommRingCat.of r))) :=
    d.range_geometricPoint_subset t ht.2.2
  exact rankOneWeylReductivity k (identityComponent (geometricFiber G t)) (commGroupScheme _ I)
    (geometricIdentityComponentHom I G i t)
    ⟨isSplitTorus_splitTorus I, isClosedSubgroup_geometricIdentityComponentHom I G i hi t⟩
    ht.2.1 α hα hsupport hdimpos hdimneg (exponentIso (Spec (CommRingCat.of k)) I e)
    (fieldAffineIdentityTransporterPoint I G q d hg i e htrans hq)
    (exponentIso_inverts_character (Spec (CommRingCat.of k)) I e m he)
    (fieldAffineIdentityTransporterPoint_relation I G q d hg i e htrans hq)

end Langlands.GroupScheme.splitTorus
