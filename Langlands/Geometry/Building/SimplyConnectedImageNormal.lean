import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.GroupScheme.HomConjugacy

/-!
# Transport and normality of `G(k)^♮`

For a connected reductive group `G` over a field `k`, the subgroup `G(k)^♮` is the image of
`G_sc(k) → G(k)` for a simply connected cover `π : C → D` of the derived subgroup `d : D → G`
(KP Definition 2.6.20). This module proves:

* an isomorphism `G ≅ G'` carries the derived subgroup of `G` onto that of `G'`;
* an isomorphism `e : G ≅ G'` carries `G(k)^♮` onto `G'(k)^♮`, computed with any simply
  connected covers of the two derived subgroups (the isomorphism case of KP Fact 2.6.21);
* `G(k)^♮` does not depend on the choice of the derived subgroup inclusion and of its simply
  connected cover;
* `G(k)^♮` is a normal subgroup of `G(k)` (the case of inner automorphisms).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Derived

variable {S : Scheme.{u}} {G G' D : GroupScheme S}

/-- An isomorphism `e : G ≅ G'` carries points of the derived subgroup of `G` to points of the
derived subgroup of `G'`. -/
theorem comp_iso_mem_derivedSubgroup (e : G ≅ G') {T : Over S} {x : T ⟶ G.X}
    (hx : x ∈ (derivedSubgroup G).carrier T) :
    x ≫ e.hom.hom.hom ∈ (derivedSubgroup G').carrier T := by
  intro H i hi hcomm
  have : IsIso e.inv.hom.hom := (Grp.forget (Over S)).map_isIso e.inv
  have : IsIso e.inv.hom.hom.left := (Over.forget S).map_isIso e.inv.hom.hom
  have : IsClosedImmersion i.hom.hom.left := hi
  have hi' : IsClosedSubgroup (i ≫ e.inv) := by
    change IsClosedImmersion (i.hom.hom.left ≫ e.inv.hom.hom.left)
    infer_instance
  have hcomm' : (SubgroupFunctor.range (i ≫ e.inv)).ContainsCommutators := by
    intro T' a b
    obtain ⟨z, hz⟩ :=
      SubgroupFunctor.mem_range.mp (hcomm T' (a ≫ e.hom.hom.hom) (b ≫ e.hom.hom.hom))
    refine SubgroupFunctor.mem_range.mpr ⟨z, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hz, ← GrpObj.inv_comp, ← GrpObj.inv_comp, ← MonObj.mul_comp,
      ← MonObj.mul_comp, ← MonObj.mul_comp, Category.assoc, ← Grp.comp_hom_hom,
      e.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp (hx H (i ≫ e.inv) hi' hcomm')
  refine SubgroupFunctor.mem_range.mpr ⟨z, ?_⟩
  rw [← hz, Grp.comp_hom_hom, Category.assoc, Category.assoc, ← Grp.comp_hom_hom e.inv,
    e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

/-- Composing an inclusion of the derived subgroup with an isomorphism `G ≅ G'` gives an
inclusion of the derived subgroup of `G'`. -/
theorem IsDerivedSubgroup.comp_iso {d : D ⟶ G} (hd : IsDerivedSubgroup d) (e : G ≅ G') :
    IsDerivedSubgroup (d ≫ e.hom) := by
  have : IsIso e.hom.hom.hom := (Grp.forget (Over S)).map_isIso e.hom
  have : IsIso e.hom.hom.hom.left := (Over.forget S).map_isIso e.hom.hom.hom
  have : IsClosedImmersion d.hom.hom.left := hd.1
  refine ⟨?_, ?_⟩
  · change IsClosedImmersion (d.hom.hom.left ≫ e.hom.hom.hom.left)
    infer_instance
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hy : y ≫ d.hom.hom ∈ (derivedSubgroup G).carrier T := by
      rw [← hd.2]
      exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
    have h := comp_iso_mem_derivedSubgroup e hy
    rwa [Category.assoc, ← Grp.comp_hom_hom] at h
  · intro hx
    have h := comp_iso_mem_derivedSubgroup e.symm hx
    rw [← hd.2] at h
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp h
    refine SubgroupFunctor.mem_range.mpr ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hy, Iso.symm_hom, Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id]

end Derived

namespace IsSimplyConnectedDerivedCover

variable {k : Type u} [Field k]
  {G G' D D' C C' : GroupScheme (Spec (CommRingCat.of k))}
  {d : D ⟶ G} {π : C ⟶ D} {d' : D' ⟶ G'} {π' : C' ⟶ D'}

/-- Simply connected covers of derived subgroups are functorial for isomorphisms: for
`e : G ≅ G'`, the composite `C → D → G → G'` factors through `C' → D' → G'`. -/
theorem exists_comp_eq_comp_iso (h : IsSimplyConnectedDerivedCover d π)
    (h' : IsSimplyConnectedDerivedCover d' π') (e : G ≅ G') :
    ∃ a : C ⟶ C', a ≫ π' ≫ d' = π ≫ d ≫ e.hom := by
  have hr := (h.isDerivedSubgroup.comp_iso e).isRepresentedBy
  have hr' := h'.isDerivedSubgroup.isRepresentedBy
  let ψ : D ≅ D' := SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy hr hr'
  have hψ : ψ.hom ≫ d' = d ≫ e.hom :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp hr hr'
  have hq : IsCentralIsogeny (π' ≫ ψ.symm.hom) :=
    h'.isSimplyConnectedCover.isCentralIsogeny.comp_iso ψ.symm
  obtain ⟨a, ha, -⟩ := h.isSimplyConnectedCover.universal C' (π' ≫ ψ.symm.hom)
    h'.isSimplyConnectedCover.isSimplyConnected.isSemisimple hq
  refine ⟨a, ?_⟩
  rw [← hψ, ← ha, Iso.symm_hom, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]

end IsSimplyConnectedDerivedCover

end Langlands.GroupScheme

namespace Langlands.Geometry.Building

open Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G G' D D' C C' : GroupScheme (Spec (CommRingCat.of k))}
  {d : D ⟶ G} {π : C ⟶ D} {d' : D' ⟶ G'} {π' : C' ⟶ D'}

/-- An isomorphism `e : G ≅ G'` carries `G(k)^♮` into `G'(k)^♮`, for any simply connected
covers of the derived subgroups of `G` and `G'`. -/
theorem map_simplyConnectedImage_le (h : IsSimplyConnectedDerivedCover d π)
    (h' : IsSimplyConnectedDerivedCover d' π') (e : G ≅ G') :
    (simplyConnectedImage d π).map (rationalPoints.map e.hom) ≤ simplyConnectedImage d' π' := by
  obtain ⟨a, ha⟩ := h.exists_comp_eq_comp_iso h' e
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  refine ⟨rationalPoints.map a c, ?_⟩
  have hc := congrArg (fun f : C ⟶ G' => c ≫ f.hom.hom) ha
  simp only [Grp.comp_hom_hom] at hc
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  exact hc

/-- An isomorphism `e : G ≅ G'` carries `G(k)^♮` onto `G'(k)^♮`. -/
theorem map_simplyConnectedImage_eq (h : IsSimplyConnectedDerivedCover d π)
    (h' : IsSimplyConnectedDerivedCover d' π') (e : G ≅ G') :
    (simplyConnectedImage d π).map (rationalPoints.map e.hom) = simplyConnectedImage d' π' := by
  refine le_antisymm (map_simplyConnectedImage_le h h' e) fun g hg => ?_
  refine ⟨rationalPoints.map e.inv g, map_simplyConnectedImage_le h' h e.symm ⟨g, hg, rfl⟩, ?_⟩
  simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id]

/-- The isomorphism `G(k)^♮ ≃* G'(k)^♮` induced by an isomorphism `e : G ≅ G'`, for any simply
connected covers of the derived subgroups of `G` and `G'`; it is the restriction of
`G(k) ≃* G'(k)`. -/
def simplyConnectedImageEquiv (h : IsSimplyConnectedDerivedCover d π)
    (h' : IsSimplyConnectedDerivedCover d' π') (e : G ≅ G') :
    simplyConnectedImage d π ≃* simplyConnectedImage d' π' :=
  ((isoPointsEquiv e (Over.mk (𝟙 _))).subgroupMap (simplyConnectedImage d π)).trans
    (MulEquiv.subgroupCongr (map_simplyConnectedImage_eq h h' e))

@[simp]
theorem coe_simplyConnectedImageEquiv_apply (h : IsSimplyConnectedDerivedCover d π)
    (h' : IsSimplyConnectedDerivedCover d' π') (e : G ≅ G') (x : simplyConnectedImage d π) :
    (simplyConnectedImageEquiv h h' e x : rationalPoints G') = rationalPoints.map e.hom x :=
  rfl

/-- `G(k)^♮` does not depend on the inclusion of the derived subgroup and on its simply
connected cover. -/
theorem simplyConnectedImage_eq {d' : D' ⟶ G} (h : IsSimplyConnectedDerivedCover d π)
    (h' : IsSimplyConnectedDerivedCover d' π') :
    simplyConnectedImage d π = simplyConnectedImage d' π' := by
  have key : ∀ {D₁ D₂ C₁ C₂ : GroupScheme (Spec (CommRingCat.of k))} {d₁ : D₁ ⟶ G}
      {π₁ : C₁ ⟶ D₁} {d₂ : D₂ ⟶ G} {π₂ : C₂ ⟶ D₂}, IsSimplyConnectedDerivedCover d₁ π₁ →
      IsSimplyConnectedDerivedCover d₂ π₂ →
      simplyConnectedImage d₁ π₁ ≤ simplyConnectedImage d₂ π₂ := by
    intro D₁ D₂ C₁ C₂ d₁ π₁ d₂ π₂ h₁ h₂ g hg
    have := map_simplyConnectedImage_le h₁ h₂ (Iso.refl G) ⟨g, hg, rfl⟩
    simpa [rationalPoints.map_apply] using this
  exact le_antisymm (key h h') (key h' h)

/-- `G(k)^♮` is a normal subgroup of `G(k)`: it is stable under the inner automorphisms
(KP Fact 2.6.21 applied to `Ad(g)`). -/
theorem simplyConnectedImage_normal (h : IsSimplyConnectedDerivedCover d π) :
    (simplyConnectedImage d π).Normal := by
  refine ⟨fun c hc g => ?_⟩
  have := map_simplyConnectedImage_le h h (G.innerIso g) ⟨c, hc, rfl⟩
  rwa [rationalPoints.map_apply, comp_innerIso_hom, constantPoint_self] at this

/-! ### The data of KP Definition 2.6.23 -/

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

namespace UnramifiedZeroDatum

variable {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}

/-- `H(K)^♮` does not depend on the datum. -/
theorem simplyConnectedImage_eq (E E' : UnramifiedZeroDatum F H) :
    E.simplyConnectedImage = E'.simplyConnectedImage :=
  Building.simplyConnectedImage_eq E.isSimplyConnectedDerivedCover
    E'.isSimplyConnectedDerivedCover

/-- `H(K)^♮` is normal in `H(K)`. -/
instance simplyConnectedImage_normal (E : UnramifiedZeroDatum F H) :
    E.simplyConnectedImage.Normal :=
  Building.simplyConnectedImage_normal E.isSimplyConnectedDerivedCover

end UnramifiedZeroDatum

namespace ZeroSubgroupDatum

variable {S S' : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z Z' : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {j : Z ⟶ G} {i' : S'.toGrp ⟶ G} {j' : Z' ⟶ G}

/-- `G(F)^♮` does not depend on the datum, nor on the torus and Levi subgroup it is relative
to. -/
theorem simplyConnectedImage_eq (E : ZeroSubgroupDatum i j) (E' : ZeroSubgroupDatum i' j') :
    E.simplyConnectedImage = E'.simplyConnectedImage :=
  Building.simplyConnectedImage_eq E.isSimplyConnectedDerivedCover
    E'.isSimplyConnectedDerivedCover

/-- `G(F)^♮` is normal in `G(F)`. -/
instance simplyConnectedImage_normal (E : ZeroSubgroupDatum i j) :
    E.simplyConnectedImage.Normal :=
  Building.simplyConnectedImage_normal E.isSimplyConnectedDerivedCover

end ZeroSubgroupDatum

end Local

end Langlands.Geometry.Building
