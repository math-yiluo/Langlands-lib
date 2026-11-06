import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerCoverPreimageStatement
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedStatement
import Langlands.GroupScheme.SimplyConnected.CoverPreimageCentralizer
import Langlands.GroupScheme.SimplyConnected.CoverPreimageCharacters
import Langlands.GroupScheme.SimplyConnected.CoverPreimageDerived
import Langlands.GroupScheme.SimplyConnected.CoverPreimageTorus
import Langlands.GroupScheme.Reductive.CentralDerivedProductStatement
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement
import Langlands.GroupScheme.Derived.RepresentabilityProof

/-! # Reduction of the cover-preimage statement to three structural inputs -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The cover-preimage statement follows from the existence of a central torus generating a
connected reductive group together with its derived subgroup, the connected reductivity of
dynamic centralizers, and the simple connectedness of derived subgroups of split-torus
centralizers in simply connected groups. -/
def SplitTorusCentralizerCoverPreimageReductionStatement : Prop :=
  ReductiveCentralDerivedProductStatement.{u} →
    DynamicCentralizerReductiveStatement.{u} →
    SplitTorusCentralizerDerivedSimplyConnectedStatement.{u} →
    SplitTorusCentralizerCoverPreimageStatement.{u}

open CoverPreimage in
theorem splitTorusCentralizerCoverPreimage_of_inputs :
    SplitTorusCentralizerCoverPreimageReductionStatement.{u} := by
  intro hprod hdyn hsc k _ G D C d π hG hd hC hπ A a ha M j hj DM CM dM πM hcov T t ht
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion d.hom.hom.left := hd.1
  have : Mono d.hom.hom := Over.mono_of_mono_left _
  have hCred := hC.isSemisimple.isConnectedReductive
  have : Smooth C.X.hom := hCred.smooth
  have : IsAffineHom C.X.hom := hCred.isAffineHom
  -- the central torus and the multiplication cover
  obtain ⟨Z, D₀, i, d₀, -, -, hZ, hi, hic, hd₀, hepi⟩ := hprod k G hG
  let e := hd₀.isRepresentedBy.isoOfIsRepresentedBy hd.isRepresentedBy
  have he : e.hom ≫ d = d₀ := hd₀.isRepresentedBy.isoOfIsRepresentedBy_hom_comp _
  have heq : subgroupProductMap i d₀ = (Z.X ◁ e.hom.hom.hom) ≫ subgroupProductMap i d := by
    simp only [subgroupProductMap, MonObj.comp_mul, ← Category.assoc, whiskerLeft_fst,
      whiskerLeft_snd]
    rw [Category.assoc (snd Z.X D₀.X), ← Grp.comp_hom_hom, he]
  have : Epi (subgroupProductMap i d) := by
    have : Epi ((Z.X ◁ e.hom.hom.hom) ≫ subgroupProductMap i d) := heq ▸ hepi
    exact epi_of_epi (Z.X ◁ e.hom.hom.hom) _
  have hm := isCentralFppfCover_centralProduct hG hd hZ hic hi
  -- clauses 1 to 3
  obtain ⟨A', a', ha', hA'⟩ :=
    exists_splitSubtorus_torusCentralizer_eq_comap d π hπ hic hm a ha
  have hjD : (Dynamic.centralizer
      (CommGroupScheme.groupHom (centralizingCocharacter ha.1 a) ≫ a)).IsRepresentedBy j := by
    rw [centralizingCocharacter_spec]
    exact hj
  have hjc : IsClosedSubgroup j :=
    Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_centralizer _ hjD
  have : IsClosedImmersion j.hom.hom.left := hjc
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  let M' := subgroupIntersection (π ≫ d) j
  let j' := subgroupIntersectionFst (π ≫ d) j
  let p := subgroupIntersectionSnd (π ≫ d) j
  have hrep : ((torusCentralizer a).comap (π ≫ d)).IsRepresentedBy j' :=
    hj.comap_subgroupIntersectionFst hjc (π ≫ d)
  have hrep' : (torusCentralizer a').IsRepresentedBy j' := by
    rw [hA']
    exact hrep
  have hj'c : IsClosedSubgroup j' := isClosedSubgroup_subgroupIntersectionFst (π ≫ d) hjc
  have hM' : IsConnectedReductive M' := by
    refine hdyn k C hCred
      (CommGroupScheme.groupHom (centralizingCocharacter ha'.1 a') ≫ a') M' j' hj'c ?_
    rw [centralizingCocharacter_spec]
    exact hrep'
  -- the central torus lies in `M`
  have hle : SubgroupFunctor.range i ≤ torusCentralizer a := by
    intro U x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    intro V b s
    rw [← Category.assoc]
    exact commute_of_mem_center (hic V (b ≫ y)) _
  let iM := hj.liftOfLE i hle
  have hiM : iM ≫ j = i := SubgroupFunctor.IsRepresentedBy.liftOfLE_comp _ _ _
  have hM := hcov.isConnectedReductive
  -- clause 5
  have : IsAffineHom M'.X.hom := hM'.isAffineHom
  have : Smooth M'.X.hom := hM'.smooth
  obtain ⟨D', d', -, -, hd'⟩ := derivedSubgroupRepresentability k M'
  have hD'sc := hsc k C hC A' a' ha' M' j' hrep' D' d' hd'
  obtain ⟨b, hb⟩ := exists_derivedSubgroup_lift hG hd hπ hic hm hjc iM hiM hM' hcov hd' hD'sc
  -- clause 6
  obtain ⟨T', t', g, ht', htg, hsplit⟩ :=
    exists_maximalTorus_preimage hπ hic hm iM hiM hZ hM hM' ht
  refine ⟨A', a', M', j', p, ha', hrep', hM', ?_, ?_, ?_, ⟨D', d', b, hd', hb⟩,
    ⟨T', t', g, ht', htg, hsplit⟩⟩
  · rw [← Category.assoc]
    exact subgroupIntersection_condition (π ≫ d) j
  · rw [hrep.2, hj.2]
  · intro χ'
    exact exists_nsmul_eq_characterRestrict (isCentralFppfCover_of_isCentralIsogeny hπ) d hic hm
      j iM hiM χ'

end Langlands.GroupScheme
