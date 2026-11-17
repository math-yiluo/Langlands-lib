import Langlands.GroupScheme.RelativeLevi.SplitWeightCoordinates
import Langlands.GroupScheme.RelativeLevi.SplitBorelPositiveFactors
import Langlands.GroupScheme.RelativeUnipotent.RootWeightSeries
import Langlands.GroupScheme.RelativeUnipotent.SeriesTransport

/-! # Positive-weight terms represent the actual contracting subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalSplitCell

open RelativeUnipotent

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G U V : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {fam : J → (Ga R ⟶ G)}

/-- Products supported on strictly positive weights contract on every test. -/
theorem orderedProduct_mem_unipotent_of_supported
    (hu : TorusEquivariant i ch fam) (wt : I → ℤ)
    {n : ℕ} (pos : Fin n → J)
    (T : Over (Spec (CommRingCat.of R))) (c : Fin n → Γ(T.left, ⊤))
    (hc : ∀ k, coPairing (ch (pos k)) wt ≤ 0 → c k = 0) :
    orderedProduct fam pos T c ∈
      (Dynamic.unipotent (AffineRegularBorel.cocharacter i wt)).carrier T := by
  apply ((Dynamic.unipotent (AffineRegularBorel.cocharacter i wt)).carrier T).list_prod_mem
  intro a ha
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
  by_cases hk : 0 < coPairing (ch (pos k)) wt
  · exact rootPoint_mem_unipotent hu wt (pos k) hk T (c k)
  · rw [hc k (le_of_not_gt hk), rootPoint_zero]
    exact one_mem _

/-- The supported coordinate theorem on every affine test scheme. -/
theorem exists_orderedProduct_supported_of_mem_unipotent_of_affine
    {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}
    [IsOpenImmersion (cellMap i fam neg pos).left]
    (hu : TorusEquivariant i ch fam) (wt : I → ℤ)
    (hneg : ∀ k, coPairing (ch (neg k)) wt ≤ 0)
    {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (g : T ⟶ G.X)
    (hg : g ∈ (Dynamic.unipotent (AffineRegularBorel.cocharacter i wt)).carrier T) :
    ∃ c : Fin n → Γ(T.left, ⊤), g = orderedProduct fam pos T c ∧
      ∀ k, coPairing (ch (pos k)) wt ≤ 0 → c k = 0 := by
  let e : Over.mk (T.left.isoSpec.inv ≫ T.hom) ≅ T :=
    Over.isoMk T.left.isoSpec.symm rfl
  obtain ⟨c, hc, hs⟩ := exists_orderedProduct_supported_of_mem_unipotent_of_ring
    (pos := pos) hu wt hneg _ (e.hom ≫ g)
      ((Dynamic.unipotent (AffineRegularBorel.cocharacter i wt)).comp_mem e.hom hg)
  refine ⟨fun k => e.inv.left.appTop (c k), ?_, ?_⟩
  · have h := congrArg (fun f => e.inv ≫ f) hc
    rwa [← Category.assoc, e.inv_hom_id, Category.id_comp, comp_orderedProduct] at h
  · intro k hk
    change e.inv.left.appTop (c k) = 0
    rw [hs k hk, map_zero]

variable (C : RootHeightChart U) (W : RootWeightData C) (j : U ⟶ G)
    {pos : Fin C.dimension → J}
    (hroot : ∀ k, C.roots (ULift.up k) ≫ j = fam (pos k))

include hroot in
/-- The chart's factored root product retains its ambient root labels. -/
theorem orderedProduct_chart_comp (T : Over (Spec (CommRingCat.of R)))
    (c : Fin C.dimension → Γ(T.left, ⊤)) :
    orderedProduct C.roots ULift.up T c ≫ j.hom.hom =
      orderedProduct fam pos T c := by
  rw [orderedProduct_comp_hom]
  simp only [orderedProduct, hroot]

variable (hu : TorusEquivariant i ch fam) (wt : I → ℤ)
    (hweight : ∀ k, (W.weight k : ℤ) = coPairing (ch (pos k)) wt)
    {m : ℕ} {neg : Fin m → J}
    [IsOpenImmersion (cellMap i fam neg pos).left]
    (hneg : ∀ k, coPairing (ch (neg k)) wt ≤ 0)

include hroot hu hweight in
/-- The ambient range of the chart's positive-weight term lies in the actual
contracting functor on every test scheme. -/
theorem range_positiveWeight_le_unipotent :
    SubgroupFunctor.range (W.inclusion 0 ≫ j) ≤
      Dynamic.unipotent (AffineRegularBorel.cocharacter i wt) := by
  intro T g hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  have hx : x ≫ (W.inclusion 0).hom.hom ∈ (W.subgroup 0).carrier T := by
    rw [← (W.isRepresentedBy_inclusion 0).2]
    exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
  have hs := (W.mem_subgroup_iff T 0 _).mp hx
  change (x ≫ (W.inclusion 0).hom.hom) ≫ j.hom.hom ∈ _
  rw [← C.orderedProduct_coordinates T (x ≫ (W.inclusion 0).hom.hom),
    orderedProduct_chart_comp C j hroot]
  apply orderedProduct_mem_unipotent_of_supported hu wt pos T
  intro k hk
  apply hs k
  have he := hweight k
  omega

variable [Mono j.hom.hom] [IsAffine V.X.left] (v : V ⟶ G)
    (hV : (Dynamic.unipotent (AffineRegularBorel.cocharacter i wt)).IsRepresentedBy v)

include hroot hu hweight hneg hV in
/-- The positive-weight term represents the actual contracting functor on
all scheme tests. The affine representative's universal point upgrades the
affine-test coordinate theorem to this all-test equality. -/
theorem isRepresentedBy_positiveWeightInclusion :
    (Dynamic.unipotent (AffineRegularBorel.cocharacter i wt)).IsRepresentedBy
      (W.inclusion 0 ≫ j) := by
  have : Mono (W.inclusion 0).hom.hom := (W.isRepresentedBy_inclusion 0).1
  have hmono : Mono (W.inclusion 0 ≫ j).hom.hom := by
    change Mono ((W.inclusion 0).hom.hom ≫ j.hom.hom)
    infer_instance
  refine ⟨hmono, le_antisymm
    (range_positiveWeight_le_unipotent C W j hroot hu wt hweight) ?_⟩
  have hv : v.hom.hom ∈
      (Dynamic.unipotent (AffineRegularBorel.cocharacter i wt)).carrier V.X := by
    rw [← hV.2]
    exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨c, hc, hs⟩ := exists_orderedProduct_supported_of_mem_unipotent_of_affine
    (pos := pos) hu wt hneg v.hom.hom hv
  let x : V.X ⟶ U.X := orderedProduct C.roots ULift.up V.X c
  have hx : x ∈ (W.subgroup 0).carrier V.X := by
    rw [W.mem_subgroup_iff]
    change ∀ k, W.weight k < 0 + 1 →
      C.coordinates V.X (orderedProduct C.roots ULift.up V.X c) k = 0
    rw [C.coordinates_orderedProduct]
    intro k hk
    apply hs k
    have he := hweight k
    omega
  rw [← (W.isRepresentedBy_inclusion 0).2] at hx
  obtain ⟨a, ha⟩ := SubgroupFunctor.mem_range.mp hx
  have hav : a ≫ (W.inclusion 0 ≫ j).hom.hom = v.hom.hom := by
    rw [Grp.comp_hom_hom, ← Category.assoc, ha]
    exact (orderedProduct_chart_comp C j hroot V.X c).trans hc.symm
  intro T g hg
  rw [← hV.2] at hg
  obtain ⟨b, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  exact SubgroupFunctor.mem_range.mpr ⟨b ≫ a, by rw [Category.assoc, hav]⟩

/-- The chart's actual positive-weight group is isomorphic to any affine
representative of the supplied cocharacter's contracting subgroup. -/
def positiveWeightDynamicIso : W.groupScheme 0 ≅ V :=
  (isRepresentedBy_positiveWeightInclusion C W j hroot hu wt hweight hneg v hV).isoOfIsRepresentedBy hV

/-- The comparison isomorphism preserves the specified ambient inclusions. -/
theorem positiveWeightDynamicIso_hom_comp :
    (positiveWeightDynamicIso C W j hroot hu wt hweight hneg v hV).hom ≫ v =
      W.inclusion 0 ≫ j :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

include hroot hu hweight hneg hV in
/-- Every affine representative of this supplied contracting subgroup has a
finite vector-bundle series. -/
theorem hasFiniteVectorBundleSeries_of_positiveWeights :
    HasFiniteVectorBundleSeries V :=
  W.hasFiniteVectorBundleSeries.of_iso
    (positiveWeightDynamicIso C W j hroot hu wt hweight hneg v hV)

end Langlands.GroupScheme.LocalSplitCell
