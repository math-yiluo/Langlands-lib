import Langlands.Topology.RenardOrbitQuotientStatements
import Langlands.Topology.GroupAction.FiniteOrbitProof
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.ProperAction.Basic

/-! # Proofs of Renard II.3.3–II.3.4 -/

set_option autoImplicit false

open Set MulAction Topology

universe uG uX

namespace Langlands.Topology.RenardOrbitQuotient

/-- Compact open neighborhoods descend along an open quotient map to a Hausdorff space. -/
theorem locallyProfinite_of_openQuotientMap
    {X : Type uG} {Y : Type uX} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} (hf : IsOpenQuotientMap f)
    (hX : IsLocallyProfinite X) : IsLocallyProfinite Y := by
  refine ⟨inferInstance, ?_⟩
  intro y U hU
  obtain ⟨x, rfl⟩ := hf.surjective y
  obtain ⟨V, hxV, hVo, hVc, hVU⟩ :=
    hX.2 x (f ⁻¹' U) (hf.continuous.continuousAt hU)
  exact ⟨f '' V, mem_image_of_mem f hxV, hf.isOpenMap V hVo,
    hVc.image hf.continuous, image_subset_iff.mpr hVU⟩

/-- An open orbit has open orbit maps into the ambient space. -/
theorem isOpenMap_smul_of_open_orbit
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G]
    {X : Type uX} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [MulAction G X] [ContinuousSMul G X]
    {x : X} (hx : IsOpen (orbit G x)) :
    ∀ y ∈ orbit G x, IsOpenMap (fun g : G => g • y) := by
  let : LocallyCompactSpace (orbit G x) := hx.locallyCompactSpace
  let : ContinuousSMul G (orbit G x) :=
    IsInducing.subtypeVal.continuousSMul continuous_id rfl
  intro y hy
  let y' : orbit G x := ⟨y, hy⟩
  have hopen : IsOpenMap (fun g : G => g • y') :=
    isOpenMap_smul_of_sigmaCompact y'
  exact hx.isOpenMap_subtype_val.comp hopen

theorem finiteOrbitOpenOrbit : FiniteOrbitOpenOrbitStatement.{uG, uX} := by
  intro G _ _ _ _ X _ _ _ _ _ hX hfin
  let : T2Space X := hX.t2Space
  let : LocallyCompactSpace X := hX.locallyCompactSpace
  let : Finite (Quotient (orbitRel G X)) := hfin
  obtain ⟨x, _, V, hV, hVo⟩ :=
    FiniteOrbitProof.exists_relOpen_orbit (H := G) (X := X)
      isClosed_univ (fun _ _ _ => mem_univ _) (Set.univ_nonempty)
  have hx : IsOpen (orbit G x) := by
    rw [inter_univ] at hVo
    rwa [← hVo]
  exact ⟨x, hx, isOpenMap_smul_of_open_orbit hx⟩

theorem finiteOrbitsLocallyClosed : FiniteOrbitsLocallyClosedStatement.{uG, uX} := by
  intro G _ _ _ _ X _ _ _ _ hX hfin x
  let : T2Space X := hX.t2Space
  let : LocallyCompactSpace X := hX.locallyCompactSpace
  obtain ⟨n, r, hcover, hdisj, hopen⟩ := finiteOrbitOrdering G X hfin
  obtain ⟨i, hxi⟩ := hcover x
  let P : Fin (n + 1) → Set X :=
    fun k => {z | ∃ j : Fin n, j.val < k.val ∧ z ∈ orbit G (r j)}
  have heq : orbit G (r i) = P i.succ ∩ (P i.castSucc)ᶜ := by
    ext z
    constructor
    · intro hz
      refine ⟨⟨i, Nat.lt_succ_self _, hz⟩, ?_⟩
      rintro ⟨j, hj, hzj⟩
      have hij : i ≠ j := by
        intro hij
        subst j
        exact Nat.lt_irrefl _ hj
      exact Set.disjoint_left.mp (hdisj hij) hz hzj
    · rintro ⟨⟨j, hj, hzj⟩, hn⟩
      have hji : j = i := by
        apply Fin.ext
        have hnot : ¬ j.val < i.val := fun h => hn ⟨j, h, hzj⟩
        change j.val < i.val + 1 at hj
        omega
      simpa only [hji] using hzj
  exact ⟨P i.succ, (P i.castSucc)ᶜ, hopen i.succ,
    (hopen i.castSucc).isClosed_compl, (orbit_eq_iff.mpr hxi).trans heq⟩

/-- An invariant subset is saturated for the actual orbit projection. -/
theorem preimage_image_of_invariant
    {G : Type uG} [Group G] {X : Type uX} [MulAction G X]
    (Z : Set X) (hZ : ∀ (g : G) (x : X), x ∈ Z → g • x ∈ Z) :
    (Quotient.mk (orbitRel G X)) ⁻¹' ((Quotient.mk (orbitRel G X)) '' Z) = Z := by
  ext x
  constructor
  · rintro ⟨z, hz, hzx⟩
    have hxz : x ∈ orbit G z := Quotient.exact hzx.symm
    obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hxz
    exact hZ g z hz
  · exact fun hx => mem_image_of_mem _ hx

theorem invariantQuotientImages : InvariantQuotientImagesStatement.{uG, uX} := by
  intro G _ _ _ X _ _ _ _ _ Z hinv
  have hq := MulAction.isOpenQuotientMap_quotientMk (Γ := G) (T := X)
  have hsat := preimage_image_of_invariant Z hinv
  constructor
  · intro hZ
    rwa [← hq.isQuotientMap.isClosed_preimage, hsat]
  · intro hZ
    rw [isLocallyClosed_iff_isOpen_coborder, ← hq.isQuotientMap.isOpen_preimage,
      ← coborder_preimage hq.isOpenMap hq.continuous, hsat]
    exact hZ.isOpen_coborder

theorem hausdorffOrbitQuotient : HausdorffOrbitQuotientStatement.{uG, uX} := by
  intro G _ _ _ X _ _ _ _ hX hQ
  let : T2Space (Quotient (orbitRel G X)) := hQ
  exact locallyProfinite_of_openQuotientMap
    (MulAction.isOpenQuotientMap_quotientMk (Γ := G) (T := X)) hX

theorem transitiveQuotientHomeomorphism :
    TransitiveQuotientHomeomorphismStatement.{uG, uX} := by
  intro G _ _ _ _ X _ _ _ _ _ hX x
  let : T2Space X := hX.t2Space
  let : LocallyCompactSpace X := hX.locallyCompactSpace
  let f : (G ⧸ stabilizer G x) → X := ofQuotientStabilizer G x
  have hfc : Continuous f :=
    (QuotientGroup.isQuotientMap_mk (stabilizer G x)).continuous_iff.mpr
      (continuous_id.smul continuous_const)
  have hfo : IsOpenMap f :=
    QuotientGroup.isOpenQuotientMap_mk.isOpenMap_iff.mpr
      (isOpenMap_smul_of_sigmaCompact x)
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨g, hg⟩ := exists_smul_eq G x y
    exact ⟨QuotientGroup.mk g, hg⟩
  refine ⟨IsHomeomorph.homeomorph f
    ⟨hfc, hfo, injective_ofQuotientStabilizer G x, hfs⟩, ?_⟩
  intro g
  rfl

theorem closedSubgroupQuotient : ClosedSubgroupQuotientStatement.{uG} := by
  intro G _ _ _ hG N hN
  let : IsClosed (N : Set G) := hN
  exact locallyProfinite_of_openQuotientMap
    (QuotientGroup.isOpenQuotientMap_mk (N := N)) hG

/-- All six published targets, with the group and space universes independent. -/
theorem statements : Statements.{uG, uX} :=
  ⟨finiteOrbitOpenOrbit, finiteOrbitsLocallyClosed, invariantQuotientImages,
    hausdorffOrbitQuotient, transitiveQuotientHomeomorphism, closedSubgroupQuotient⟩

end Langlands.Topology.RenardOrbitQuotient
