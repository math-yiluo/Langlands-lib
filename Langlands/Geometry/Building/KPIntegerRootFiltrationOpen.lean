import Langlands.Geometry.Building.IntegerAffineRootArrangement
import Langlands.Geometry.Building.IntegerValuationChamberBounded
import Langlands.Geometry.Building.QuasiSplitApartmentOpposite
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.GroupScheme.Dynamic.RationalOpenCell
import Langlands.Representation.Aubert.General.RationalOppositeIwahoriBasisProof
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Relative openness for integer-valued root filtrations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Filter
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [IsOpenUnits k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

private instance ambientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
private instance centralizerAffine : IsAffine B.centralizer.Z.X.left := by
  have : IsClosedImmersion B.centralizer.j.hom.hom.left := B.centralizer.isClosedSubgroup
  exact isAffine_of_isAffineHom B.centralizer.j.hom.hom.left

local instance ambientTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology k G.X
local instance centralizerTopology : TopologicalSpace (rationalPoints B.centralizer.Z) :=
  rationalPointTopology k B.centralizer.Z.X

omit [IsTopologicalRing k] [IsOpenUnits k] in
/-- Extend an open centralizer character kernel to an ambient identity neighbourhood. -/
private theorem exists_isOpen_centralizer_characterKernel
    (hZ : IsOpen (characterValuationKernel v B.centralizer.Z :
      Set (rationalPoints B.centralizer.Z))) :
    ∃ W : Set (rationalPoints G), IsOpen W ∧ 1 ∈ W ∧
      ∀ z : rationalPoints B.centralizer.Z, rationalPoints.map B.centralizer.j z ∈ W →
        z ∈ characterValuationKernel v B.centralizer.Z := by
  let : IsClosedImmersion B.centralizer.j.hom.hom.left := B.centralizer.isClosedSubgroup
  obtain ⟨W, hW, heq⟩ :=
    (isEmbedding_rationalPointMap k B.centralizer.j.hom.hom).isInducing.isOpen_iff.mp hZ
  refine ⟨W, hW, ?_, fun z hz => ?_⟩
  · have h1 : (1 : rationalPoints B.centralizer.Z) ∈
        (fun p => p ≫ B.centralizer.j.hom.hom) ⁻¹' W := by
      rw [heq]
      exact one_mem _
    simpa only [Set.mem_preimage, MonObj.one_comp] using h1
  · have hz' : z ∈ (fun p => p ≫ B.centralizer.j.hom.hom) ⁻¹' W := hz
    rw [heq] at hz'
    exact hz'

/-- Opposite-cell coordinates and V6 make root values locally constant away from one. -/
theorem eventually_val_eq {α : relativeRoots B.i} {u : rationalPoints G}
    (hZ : IsOpen (characterValuationKernel v B.centralizer.Z :
      Set (rationalPoints B.centralizer.Z)))
    (hu : u ∈ B.rootGroup α) (h1 : u ≠ 1) :
    ∀ᶠ w in 𝓝 u, w ∈ B.rootGroup α → w ≠ 1 →
      ∀ x : B.Apartment, x.val α w = x.val α u := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have : LocallyOfFiniteType G.X.hom := inferInstance
  have : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup k G
  have hS : IsSplitTorus B.S.toGrp := B.isMaximalSplitTorus.isSplitSubtorus.1
  have hα0 : (α : characterLattice B.S) ≠ 0 := α.property.1
  obtain ⟨p, hp⟩ := B.hasOppositeFactorPairs α α.property u hu h1
  obtain ⟨D, hD, ν, hν⟩ := hS.exists_pairing_eq_pos hα0
  have hpos : 0 < latticePairing B.S (α : characterLattice B.S) ν := by omega
  have hneg : 0 < latticePairing B.S (-(α : characterLattice B.S)) (-ν) := by simpa using hpos
  let χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G := CommGroupScheme.groupHom (-ν) ≫ B.i
  have hχinv : CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ =
      CommGroupScheme.groupHom ν ≫ B.i := by
    have h := groupHom_neg_comp_eq_oppositeCocharacter B.i (-ν)
    rw [neg_neg] at h
    exact h.symm
  have hO : ∀ g ∈ B.rootGroup α, g ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).carrier
        (Over.mk (𝟙 _)) := by
    intro g hg
    rw [hχinv]
    exact RelativeRoot.subgroup_le_dynamicUnipotent B.i ν hpos _ hg
  have hN : ∀ g ∈ B.rootGroup (-(α : characterLattice B.S)),
      g ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) :=
    fun g hg => RelativeRoot.subgroup_le_dynamicUnipotent B.i (-ν) hneg _ hg
  have hM : ∀ g ∈ centralizerPoints B.i,
      g ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    intro g hg
    rw [← torusCentralizer_carrier_base] at hg
    exact torusCentralizer_le_dynamicCentralizer B.i (CommGroupScheme.groupHom (-ν)) _ hg
  obtain ⟨W, hW, hW1, hWZ⟩ := B.exists_isOpen_centralizer_characterKernel hZ
  have hcell := Dynamic.opposite_cell_mem_nhds_one k G χ
  rw [← rationalPointTopology_eq_rationalSchemeTopology k G.X] at hcell
  have hC := hcell Set.univ Filter.univ_mem W (hW.mem_nhds hW1) Set.univ Filter.univ_mem
  have hcont : Continuous
      (fun w : rationalPoints G => (p.1 * u * p.2)⁻¹ * p.1 * w * p.2) := by
    exact (continuous_const.mul continuous_id).mul continuous_const
  have hwu : (p.1 * u * p.2)⁻¹ * p.1 * u * p.2 = 1 := by group
  have hev := hcont.continuousAt.preimage_mem_nhds (x := u) (by rw [hwu]; exact hC)
  filter_upwards [hev] with w hv hvα hv1 x
  obtain ⟨a, ⟨-, ha⟩, b, ⟨hbW, hb⟩, c, ⟨-, hc⟩, habc⟩ := hv
  obtain ⟨q, hq⟩ := B.hasOppositeFactorPairs α α.property w hvα hv1
  have h1' : (p.1 * u * p.2)⁻¹ * (p.1 * q.1⁻¹) * (p.1 * u * p.2) ∈ B.rootGroup α :=
    Langlands.Geometry.Building.IsOppositeFactorPair.inv_conj_mem B.i hS hα0 hu h1 hp
      (mul_mem hp.1 (inv_mem hq.1))
  have h2' : (p.1 * u * p.2)⁻¹ * (q.1 * w * q.2) ∈ centralizerPoints B.i :=
    B.reflectionElement_inv_mul_mem_centralizer hu h1 hvα hv1 hp hq
  have h3' : q.2⁻¹ * p.2 ∈ B.rootGroup (-(α : characterLattice B.S)) :=
    mul_mem (inv_mem hq.2.1) hp.2.1
  have hdec : (p.1 * u * p.2)⁻¹ * p.1 * w * p.2 =
      ((p.1 * u * p.2)⁻¹ * (p.1 * q.1⁻¹) * (p.1 * u * p.2)) *
        ((p.1 * u * p.2)⁻¹ * (q.1 * w * q.2)) * (q.2⁻¹ * p.2) := by
    group
  obtain ⟨-, hbm, -⟩ :=
    Aubert.General.RationalPointFamily.dynamic_opposite_factorization_unique χ
      a ha b hb c hc _ (hO _ h1') _ (hM _ h2') _ (hN _ h3') (habc.symm.trans hdec)
  rw [← torusCentralizer_carrier_base, ← B.centralizer.isRepresentedBy.2] at h2'
  obtain ⟨z, hz⟩ := h2'
  change z ≫ B.centralizer.j.hom.hom = _ at hz
  have hzK : z ∈ characterValuationKernel v B.centralizer.Z := by
    apply hWZ z
    change z ≫ B.centralizer.j.hom.hom ∈ W
    rw [hz, ← hbm]
    exact hbW
  have hfix := B.isOmegaCompatible.smul_eq_self hzK x
  have hzeq : B.centralizer.toNormalizer z =
      (B.reflectionElement hp)⁻¹ * B.reflectionElement hq :=
    Subtype.ext hz
  rw [hzeq, mul_smul, inv_smul_eq_iff] at hfix
  have key : ∀ {g : rationalPoints G} {r : rationalPoints G × rationalPoints G}
      (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
      (hr : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g r),
      rootForm B.i α (B.reflectionElement hr • x -ᵥ x) =
        -2 * B.reflectionFunctional α g x := by
    intro g r hg hg1 hr
    have h := DFunLike.congr_fun (B.normalizerAffineEquiv_reflectionElement hg hg1 hr) x
    change B.reflectionElement hr • x = _ at h
    rw [h]
    change rootForm B.i α
      (((-B.reflectionFunctional α g x) • B.reflectionCoroot hg hg1 hr +ᵥ x) -ᵥ x) = _
    rw [vadd_vsub, map_smul, B.rootForm_reflectionCoroot hg hg1 hr, smul_eq_mul]
    ring
  have hval : B.reflectionFunctional α w x = B.reflectionFunctional α u x := by
    have h := key hvα hv1 hq
    rw [hfix, key hu h1 hp] at h
    linarith
  rw [← B.coe_reflectionFunctional_apply hvα hv1, ← B.coe_reflectionFunctional_apply hu h1, hval]


/-- Every root filtration is relatively open when the centralizer character kernel
is open and the integer valuation is nontrivial. -/
theorem isOpen_filtration
    (hZ : IsOpen (characterValuationKernel v B.centralizer.Z :
      Set (rationalPoints B.centralizer.Z)))
    (hv : ∃ b : kˣ, IntegerValuation.order v b ≠ 0)
    (x : B.Apartment) (α : relativeRoots B.i) (r : ℝ) :
    IsOpen (((↑) : B.rootGroup α → rationalPoints G) ⁻¹'
      (B.filtration x α r : Set (rationalPoints G))) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup k G
  obtain ⟨s, δ, hδ, hs⟩ := B.exists_rootValue_sub_mul hv x α
  have hex : ∃ n : ℤ, r ≤ s - n * δ := by
    rcases lt_or_gt_of_ne hδ with hneg | hpos
    · obtain ⟨n, hn⟩ := exists_int_gt ((r - s) / (-δ))
      have hh := (div_lt_iff₀ (neg_pos.mpr hneg)).mp hn
      exact ⟨n, by linarith⟩
    · obtain ⟨n, hn⟩ := exists_int_lt ((s - r) / δ)
      have hh := (lt_div_iff₀ hpos).mp hn
      exact ⟨n, by linarith⟩
  obtain ⟨n, hn⟩ := hex
  obtain ⟨u, hu, hval⟩ := hs n
  have hu1 : u ≠ 1 := by
    intro heq
    rw [heq, B.val_apply_one] at hval
    exact WithTop.top_ne_coe hval
  have hmem : u ∈ B.filtration x α r :=
    ⟨hu, by rw [hval]; exact WithTop.coe_le_coe.mpr hn⟩
  apply ((B.filtration x α r).subgroupOf (B.rootGroup α)).isOpen_of_mem_nhds
    (g := ⟨u, hu⟩)
  have he := (continuous_subtype_val.tendsto (⟨u, hu⟩ : B.rootGroup α)).eventually
    (B.eventually_val_eq hZ hu hu1)
  filter_upwards [he] with w hw
  by_cases hw1 : (w : rationalPoints G) = 1
  · exact (show (w : rationalPoints G) ∈ B.filtration x α r by
      rw [hw1]; exact one_mem _)
  · refine ⟨w.property, ?_⟩
    change (r : WithTop ℝ) ≤ x.val α (w : rationalPoints G)
    rw [hw w.property hw1 x]
    exact hmem.2

/-- The supplied root filtration, bundled with its relative openness. -/
def filtrationOpenSubgroup
    (hZ : IsOpen (characterValuationKernel v B.centralizer.Z :
      Set (rationalPoints B.centralizer.Z)))
    (hv : ∃ b : kˣ, IntegerValuation.order v b ≠ 0)
    (x : B.Apartment) (α : relativeRoots B.i) (r : ℝ) :
    OpenSubgroup (B.rootGroup α) where
  toSubgroup := (B.filtration x α r).subgroupOf (B.rootGroup α)
  isOpen' := B.isOpen_filtration hZ hv x α r

end Langlands.Geometry.Building.IntegerValuationBuildingData
