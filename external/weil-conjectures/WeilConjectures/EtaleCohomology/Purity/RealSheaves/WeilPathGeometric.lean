/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.HomotopyExactSequence
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath

/-!
# The geometric fundamental group inside the Weil group

For base point data `B` of a Weil group `W` of a curve `C₀`
(`AlgebraicGeometry.WeilGroup.BasePointData`), the map `π₁(C, t) → π₁(C₀, s)` induced by base
change of finite étale schemes (`AlgebraicGeometry.WeilGroup.BasePointData.geomAut`) lands in the
Weil group with degree zero and identifies `π₁(C, t) = Aut F_t` with the geometric part
`W.geometric = ker deg`, as topological groups
(`AlgebraicGeometry.WeilGroup.BasePointData.geomEquiv`); this is the homotopy exact sequence
(`AlgebraicGeometry.WeilGroup.isEtaleQuotient`) at the base point `t`.
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.WeilGroup.BasePointData

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  {W : WeilGroup p} (B : BasePointData W)

/-- The geometric curve of a curve admitting a Weil group is connected. -/
theorem _root_.AlgebraicGeometry.WeilGroup.connectedSpace_geometricFiber (W : WeilGroup p) :
    ConnectedSpace p.geometricFiber := by
  have := W.geometricallyConnected
  exact GeometricallyConnected.geometrically_connectedSpace (f := p)
    (Scheme.specAlgebraicClosure K).hom p.geometricFiberProj
    p.geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)

/-- The path `F_t ∘ π^* ≅ F_s` along which `π₁(C, t)` maps to `π₁(C₀, s)`: the base change
isomorphism `F_t ∘ π^* ≅ F_{π(t)}` followed by `B.path`. -/
noncomputable def geomPath : pullback p.geometricFiberProj ⋙ fiber B.t ≅ fiber W.basePoint :=
  pullbackFiberIso p.geometricFiberProj B.t ≪≫ B.path

/-- `geomAut` is the map of fundamental groups induced by the path `B.geomPath`, for any (small)
fundamental group `G'` of the fibre functor at `t`, identified with `Aut F_t`. -/
lemma geomAut_eq_fundamentalGroupMap [ConnectedSpace p.geometricFiber] (G' : Type u)
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']
    [∀ P, MulAction G' ((fiber B.t).obj P)] [IsFundamentalGroup (fiber B.t) G']
    (g : Aut (fiber B.t)) :
    haveI := W.connectedSpace
    B.geomAut g = fundamentalGroupMap B.geomPath G' W.fundamentalGroup
      ((toAutMulEquiv (fiber B.t) G').symm g) := by
  have := W.connectedSpace
  apply (toAutMulEquiv (fiber W.basePoint) W.fundamentalGroup).injective
  rw [geomAut_apply, toAutMulEquiv_toπ]
  ext P y
  obtain ⟨y', rfl⟩ : ∃ y', B.geomPath.hom.app P y' = y :=
    ⟨B.geomPath.inv.app P y, ConcreteCategory.congr_hom (B.geomPath.inv_hom_id_app P) y⟩
  have hg (x : (fiber B.t).obj ((pullback p.geometricFiberProj).obj P)) :
      (toAutMulEquiv (fiber B.t) G').symm g • x = g.asIso.hom.app _ x := by
    rw [← toAut_hom_app_apply, ← toAutMulEquiv_apply, MulEquiv.apply_symm_apply]
  rw [toAutMulEquiv_apply, toAut_hom_app_apply, fundamentalGroupMap_smul, hg]
  simp only [geomPath, pullbackPathIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  simp only [← ConcreteCategory.comp_apply, Category.assoc, Iso.hom_inv_id_app_assoc]
  exact ConcreteCategory.comp_apply _ _ _

/-- The image of `π₁(C, t)` in `π₁(C₀, s)` acts trivially on the constant covers. -/
theorem mem_weilGroup_geomAut (g : Aut (fiber B.t)) :
    haveI := W.geometricallyConnected
    (B.geomAut g, (1 : Multiplicative ℤ)) ∈ weilGroup p W.basePoint W.fundamentalGroup := by
  have := W.connectedSpace
  have := W.geometricallyConnected
  have := W.connectedSpace_geometricFiber
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup B.t
  rw [B.geomAut_eq_fundamentalGroupMap G']
  exact mem_weilGroup_fundamentalGroupMap p B.ht B.geomPath W.fundamentalGroup G' _

/-- The map `π₁(C, t) → π₁(C₀, s)` is injective. -/
lemma geomAut_injective : Function.Injective B.geomAut := by
  have := W.connectedSpace
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated p
  have := W.connectedSpace_geometricFiber
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup B.t
  intro g g' h
  rw [B.geomAut_eq_fundamentalGroupMap G', B.geomAut_eq_fundamentalGroupMap G'] at h
  exact (toAutMulEquiv (fiber B.t) G').symm.injective
    (fundamentalGroupMap_injective_geometricFiber p B.geomPath G' W.fundamentalGroup h)

/-- Every element of `π₁(C₀, s)` acting trivially on the constant covers is in the image of
`π₁(C, t)`. -/
lemma exists_geomAut_eq (x : W.fundamentalGroup)
    (hx : haveI := W.geometricallyConnected
      (x, (1 : Multiplicative ℤ)) ∈ weilGroup p W.basePoint W.fundamentalGroup) :
    ∃ g, B.geomAut g = x := by
  have := W.connectedSpace
  have := W.geometricallyConnected
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated p
  have := W.connectedSpace_geometricFiber
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup B.t
  obtain ⟨k, hk⟩ := mem_range_fundamentalGroupMap_of_mem_weilGroup p B.geomPath G'
    W.fundamentalGroup x hx
  refine ⟨toAutMulEquiv (fiber B.t) G' k, ?_⟩
  rw [B.geomAut_eq_fundamentalGroupMap G', MulEquiv.symm_apply_apply, hk]

/-- The map `π₁(C, t) → π₁(C₀, s)` is continuous. -/
lemma continuous_geomAut :
    haveI := W.connectedSpace_geometricFiber
    Continuous B.geomAut := by
  have := W.connectedSpace
  have := W.connectedSpace_geometricFiber
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup B.t
  have : ∀ P, ContinuousSMul G' ((fiber B.t).obj P) := fun P ↦ IsFundamentalGroup.continuous_smul P
  have h : (B.geomAut : Aut (fiber B.t) → W.fundamentalGroup) =
      fundamentalGroupMap B.geomPath G' W.fundamentalGroup ∘
        (toAutHomeo (fiber B.t) G').symm := by
    funext g
    exact B.geomAut_eq_fundamentalGroupMap G' g
  rw [h]
  exact (continuous_fundamentalGroupMap B.geomPath G' W.fundamentalGroup).comp
    (toAutHomeo (fiber B.t) G').symm.continuous

/-- The map `π₁(C, t) → W(C₀)`, `g ↦ (geomAut g, 0)`. -/
noncomputable def geomHom : Aut (fiber B.t) →* W.carrier :=
  haveI := W.geometricallyConnected
  W.weilGroupEquiv.symm.toMonoidHom.comp
    (((B.geomAut).prod (1 : Aut (fiber B.t) →* Multiplicative ℤ)).codRestrict _
      B.mem_weilGroup_geomAut)

/-- The image of `geomHom g` in `π₁(C₀, s) × ℤ` is `(geomAut g, 1)`. -/
lemma weilGroupEquiv_geomHom (g : Aut (fiber B.t)) :
    haveI := W.geometricallyConnected
    (W.weilGroupEquiv (B.geomHom g) : W.fundamentalGroup × Multiplicative ℤ) = (B.geomAut g, 1) :=
  by simp [geomHom]

/-- The image of `geomHom g` in `π₁(C₀, s)` is `geomAut g`. -/
lemma toFundamentalGroup_geomHom (g : Aut (fiber B.t)) :
    W.toFundamentalGroup (B.geomHom g) = B.geomAut g := by
  rw [toFundamentalGroup_apply, weilGroupEquiv_geomHom]

/-- `geomHom` takes values in the geometric part of the Weil group. -/
lemma geomHom_mem (g : Aut (fiber B.t)) : B.geomHom g ∈ W.geometric := by
  rw [MonoidHom.mem_ker, W.deg_eq]
  exact congrArg Prod.snd (B.weilGroupEquiv_geomHom g)

/-- The map `π₁(C, t) → W.geometric`, `g ↦ (geomAut g, 0)`. -/
noncomputable def geomHomGeometric : Aut (fiber B.t) →* W.geometric :=
  B.geomHom.codRestrict W.geometric B.geomHom_mem

/-- `π₁(C, t) → W.geometric` is bijective (the homotopy exact sequence). -/
lemma geomHomGeometric_bijective : Function.Bijective B.geomHomGeometric := by
  have := W.geometricallyConnected
  refine ⟨fun g g' h ↦ B.geomAut_injective ?_, ?_⟩
  · rw [← toFundamentalGroup_geomHom, ← toFundamentalGroup_geomHom]
    exact congrArg (fun w : W.geometric ↦ W.toFundamentalGroup w) h
  · rintro ⟨w, hw⟩
    have h1 : (W.weilGroupEquiv w : W.fundamentalGroup × Multiplicative ℤ).2 = 1 :=
      (W.deg_eq w).symm.trans hw
    have hmem : ((W.weilGroupEquiv w : W.fundamentalGroup × Multiplicative ℤ).1,
        (1 : Multiplicative ℤ)) ∈ weilGroup p W.basePoint W.fundamentalGroup := by
      rw [← h1]
      exact (W.weilGroupEquiv w).2
    obtain ⟨g, hg⟩ := B.exists_geomAut_eq _ hmem
    refine ⟨g, Subtype.ext (W.weilGroupEquiv.injective (Subtype.ext ?_))⟩
    change (W.weilGroupEquiv (B.geomHom g) : W.fundamentalGroup × Multiplicative ℤ) = _
    rw [weilGroupEquiv_geomHom, hg, ← h1]

/-- `π₁(C, t) → W.geometric` is continuous. -/
lemma continuous_geomHomGeometric :
    haveI := W.connectedSpace_geometricFiber
    Continuous B.geomHomGeometric := by
  have := W.connectedSpace_geometricFiber
  refine W.isEmbedding_ker.isInducing.continuous_iff.2 ?_
  have : (fun g ↦ (W.weilGroupEquiv (B.geomHomGeometric g) :
      W.fundamentalGroup × Multiplicative ℤ).1) = B.geomAut :=
    funext fun g ↦ congrArg Prod.fst (B.weilGroupEquiv_geomHom g)
  change Continuous fun g ↦ (W.weilGroupEquiv (B.geomHomGeometric g) :
    W.fundamentalGroup × Multiplicative ℤ).1
  rw [this]
  exact B.continuous_geomAut

/-- **The geometric fundamental group is the geometric part of the Weil group**: base change of
finite étale schemes identifies `π₁(C, t) = Aut F_t` with `W.geometric = ker deg` as topological
groups (the homotopy exact sequence). -/
noncomputable def geomEquiv : Aut (fiber B.t) ≃ₜ* W.geometric :=
  haveI := W.connectedSpace_geometricFiber
  haveI := W.connectedSpace
  haveI : T2Space W.fundamentalGroup :=
    (toAutHomeo (fiber W.basePoint) W.fundamentalGroup).isEmbedding.t2Space
  haveI : T2Space W.geometric := W.isEmbedding_ker.t2Space
  let e := MulEquiv.ofBijective B.geomHomGeometric B.geomHomGeometric_bijective
  { e with
    continuous_toFun := B.continuous_geomHomGeometric
    continuous_invFun :=
      (B.continuous_geomHomGeometric.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

/-- `geomEquiv` is `geomHom`. -/
lemma geomEquiv_apply (g : Aut (fiber B.t)) : (B.geomEquiv g : W.carrier) = B.geomHom g := by
  rfl

end AlgebraicGeometry.WeilGroup.BasePointData
