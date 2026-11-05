import Langlands.Geometry.Building.CentralIsogenyValuation
import Langlands.GroupScheme.Rational.TwoCharacterPositiveCocharacter

/-! # Full valuation transfer under an actual central isogeny -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {C G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom C.X.hom] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType C.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ C} {j : T.toGrp ⟶ G}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  (q : C ⟶ G) (hq : IsCentralIsogeny q)
  (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
  (t : S ⟶ T) (h : i ≫ q = CommGroupScheme.groupHom t ≫ j)
  (ht : IsIsogeny (CommGroupScheme.groupHom t))

open RootFunctionFamily

private theorem restrict_not_opposite (a b : characterLattice T)
    (hab : ∀ r : ℝ, 0 < r →
      (1 : ℝ) ⊗ₜ[ℤ] (t ≫ b) ≠ -(r • (1 : ℝ) ⊗ₜ[ℤ] (t ≫ a))) :
    ∀ r : ℝ, 0 < r →
      (1 : ℝ) ⊗ₜ[ℤ] b ≠ -(r • (1 : ℝ) ⊗ₜ[ℤ] a) := by
  intro r hr he
  apply hab r hr
  let f : characterLattice T →ₗ[ℤ] characterLattice S :=
    { toFun := fun a => t ≫ a
      map_add' := fun a b => by simp only [Preadditive.comp_add]
      map_smul' := fun m a => by simp only [Preadditive.comp_zsmul, RingHom.id_apply] }
  have he' := congrArg (f.baseChange ℝ) he
  simpa only [map_neg, map_smul, LinearMap.baseChange_tmul, f,
    LinearMap.coe_mk, AddHom.coe_mk] using he'

omit [Mono i.hom.hom.left] [Mono j.hom.hom.left] in
private theorem image_commutator_generators
    (φ : RootFunctionFamily T G) (a b : relativeRoots j) (r s : ℝ) :
    rationalPoints.map q ''
      (⋃ (p : ℕ) (m : ℕ) (_ : 0 < p) (_ : 0 < m)
        (_ : p • (t ≫ a.val) + m • (t ≫ b.val) ∈ relativeRoots i),
        rootFiltration i (centralIsogenyPullback q hq hS hT t h ht φ)
          (p • (t ≫ a.val) + m • (t ≫ b.val)) (p * r + m * s)) =
      ⋃ (p : ℕ) (m : ℕ) (_ : 0 < p) (_ : 0 < m)
        (_ : p • a.val + m • b.val ∈ relativeRoots j),
        rootFiltration j φ (p • a.val + m • b.val) (p * r + m * s) := by
  have hc (p m : ℕ) :
      t ≫ (p • a.val + m • b.val) = p • (t ≫ a.val) + m • (t ≫ b.val) := by
    simp only [Preadditive.comp_add, Preadditive.comp_nsmul]
  ext g
  simp only [Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨x, ⟨p, m, hp, hm, hcroot, hx⟩, rfl⟩
    have hcroot' : p • a.val + m • b.val ∈ relativeRoots j :=
      (centralIsogenyRoot_mem_iff q hq hS hT t h ht _).mp (hc p m ▸ hcroot)
    refine ⟨p, m, hp, hm, hcroot', ?_⟩
    exact ((rootFiltration_centralIsogenyPullback_iff q hq hS hT t h ht φ
      ⟨_, hcroot'⟩ _ x).mp (hc p m ▸ hx)).2
  · rintro ⟨p, m, hp, hm, hcroot, hg⟩
    have hmem : g ∈ rationalPoints.map q ''
        rootFiltration i (centralIsogenyPullback q hq hS hT t h ht φ)
          (t ≫ (p • a.val + m • b.val)) (p * r + m * s) := by
      rw [image_rootFiltration_centralIsogenyPullback q hq hS hT t h ht φ ⟨_, hcroot⟩]
      exact hg
    obtain ⟨x, hx, rfl⟩ := hmem
    refine ⟨x, ⟨p, m, hp, hm, ?_, ?_⟩, rfl⟩
    · rw [← hc]
      exact (centralIsogenyRoot_mem_iff q hq hS hT t h ht _).mpr hcroot
    · simpa only [hc] using hx

namespace IsRootDatumValuation

variable {φ : RootFunctionFamily T G} (hφ : IsRootDatumValuation j φ)

include hφ

omit [Mono i.hom.hom.left] in
/-- V3 is reflected inside a common contracting subgroup, where the actual
central isogeny is injective. -/
theorem centralIsogenyPullback_commutator (a b : relativeRoots j)
    (hab : ∀ z : ℝ, 0 < z →
      (1 : ℝ) ⊗ₜ[ℤ] (t ≫ b.val) ≠ -(z • (1 : ℝ) ⊗ₜ[ℤ] (t ≫ a.val)))
    (r s : ℝ) :
    ⁅Subgroup.closure
        (rootFiltration i (centralIsogenyPullback q hq hS hT t h ht φ) (t ≫ a.val) r),
      Subgroup.closure
        (rootFiltration i (centralIsogenyPullback q hq hS hT t h ht φ) (t ≫ b.val) s)⁆ ≤
      Subgroup.closure (⋃ (p : ℕ) (m : ℕ) (_ : 0 < p) (_ : 0 < m)
        (_ : p • (t ≫ a.val) + m • (t ≫ b.val) ∈ relativeRoots i),
        rootFiltration i (centralIsogenyPullback q hq hS hT t h ht φ)
          (p • (t ≫ a.val) + m • (t ≫ b.val)) (p * r + m * s)) := by
  let ψ := centralIsogenyPullback q hq hS hT t h ht φ
  let A := Subgroup.closure (rootFiltration i ψ (t ≫ a.val) r)
  let B := Subgroup.closure (rootFiltration i ψ (t ≫ b.val) s)
  let Z := Subgroup.closure (⋃ (p : ℕ) (m : ℕ) (_ : 0 < p) (_ : 0 < m)
    (_ : p • (t ≫ a.val) + m • (t ≫ b.val) ∈ relativeRoots i),
    rootFiltration i ψ (p • (t ≫ a.val) + m • (t ≫ b.val)) (p * r + m * s))
  have ha := (centralIsogenyRoot_mem_iff q hq hS hT t h ht a.val).mpr a.property
  have hb := (centralIsogenyRoot_mem_iff q hq hS hT t h ht b.val).mpr b.property
  obtain ⟨ν, hνa, hνb⟩ :=
    hS.exists_cocharacter_pos_pair_of_not_opposite (t ≫ a.val) (t ≫ b.val) ha.1 hb.1 hab
  let χ := CommGroupScheme.groupHom ν ≫ i
  let U : Subgroup (rationalPoints C) := (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))
  have hAU : A ≤ U := (Subgroup.closure_le U).mpr fun _ hx =>
    RelativeRoot.subgroup_le_dynamicUnipotent i ν hνa _ hx.1
  have hBU : B ≤ U := (Subgroup.closure_le U).mpr fun _ hx =>
    RelativeRoot.subgroup_le_dynamicUnipotent i ν hνb _ hx.1
  have hZU : Z ≤ U := by
    apply (Subgroup.closure_le U).mpr
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨p, m, hp, hm, _, hx⟩ := hx
    have hpos : 0 < latticePairing S (p • (t ≫ a.val) + m • (t ≫ b.val)) ν := by
      simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply]
      positivity
    exact RelativeRoot.subgroup_le_dynamicUnipotent i ν hpos _ hx.1
  have hmap : (⁅A, B⁆).map (rationalPoints.map q) ≤ Z.map (rationalPoints.map q) := by
    change (⁅Subgroup.closure (rootFiltration i ψ (t ≫ a.val) r),
        Subgroup.closure (rootFiltration i ψ (t ≫ b.val) s)⁆).map _ ≤
      (Subgroup.closure _).map _
    rw [Subgroup.map_commutator, MonoidHom.map_closure, MonoidHom.map_closure,
      MonoidHom.map_closure,
      image_rootFiltration_centralIsogenyPullback q hq hS hT t h ht φ a r,
      image_rootFiltration_centralIsogenyPullback q hq hS hT t h ht φ b s,
      image_commutator_generators q hq hS hT t h ht φ a b r s]
    exact hφ.commutator a.val a.property b.val b.property
      (restrict_not_opposite t a.val b.val hab) r s
  intro x hx
  have hxU : x ∈ U := Subgroup.commutator_le_of_le hAU hBU hx
  have hxq : rationalPoints.map q x ∈ Z.map (rationalPoints.map q) :=
    hmap (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  obtain ⟨y, hy, hyq⟩ := hxq
  have hxy : y = x := congrArg Subtype.val
    (Dynamic.unipotentPointsMap_injective q χ hq.isCentral_kernelι (Over.mk (𝟙 _))
      (a₁ := ⟨y, hZU hy⟩) (a₂ := ⟨x, hxU⟩) (Subtype.ext hyq))
  exact hxy ▸ hy

/-- Normalized pullback along the supplied central-isogeny square is a valuation. -/
theorem centralIsogenyPullback_isRootDatumValuation :
    IsRootDatumValuation i (centralIsogenyPullback q hq hS hT t h ht φ) := by
  have hlift (a : characterLattice S) (ha : a ∈ relativeRoots i) :
      ∃ a' : relativeRoots j, t ≫ a'.val = a := by
    obtain ⟨a', he⟩ := (centralIsogenyRootPullbackEquiv q hq hS hT t h ht).surjective ⟨a, ha⟩
    exact ⟨a', congrArg Subtype.val he⟩
  have hn := centralIsogenyPullback_isNormalized q hq hS hT t h ht φ
  refine
    { eq_top_of_not_mem_roots := hn.1
      eq_top_of_not_mem := hn.2
      three_le_encard := ?_
      one_mem := ?_
      mul_mem := ?_
      inv_mem := ?_
      eq_top_iff := ?_
      reflection := ?_
      commutator := ?_
      double := ?_
      opposite := ?_ } <;> intros
  · rename_i a ha
    obtain ⟨a', rfl⟩ := hlift a ha
    exact hφ.centralIsogenyPullback_three_le_encard q hq hS hT t h ht a'
  · rename_i a ha r
    obtain ⟨a', rfl⟩ := hlift a ha
    exact hφ.centralIsogenyPullback_one_mem q hq hS hT t h ht a' r
  · rename_i a ha r g g' hg hg'
    obtain ⟨a', rfl⟩ := hlift a ha
    exact hφ.centralIsogenyPullback_mul_mem q hq hS hT t h ht a' r g g' hg hg'
  · rename_i a ha r g hg
    obtain ⟨a', rfl⟩ := hlift a ha
    exact hφ.centralIsogenyPullback_inv_mem q hq hS hT t h ht a' r g hg
  · rename_i a ha g hg
    obtain ⟨a', rfl⟩ := hlift a ha
    exact hφ.centralIsogenyPullback_eq_top_iff q hq hS hT t h ht a' g hg
  · rename_i a ha n hn
    obtain ⟨a', rfl⟩ := hlift a ha
    exact hφ.centralIsogenyPullback_reflection q hq hS hT t h ht a' n hn
  · rename_i a ha b hb hab r s
    obtain ⟨a', rfl⟩ := hlift a ha
    obtain ⟨b', rfl⟩ := hlift b hb
    exact hφ.centralIsogenyPullback_commutator q hq hS hT t h ht a' b' hab r s
  · rename_i a ha h2a g hg
    obtain ⟨a', rfl⟩ := hlift a ha
    exact hφ.centralIsogenyPullback_double q hq hS hT t h ht a' h2a g hg
  · rename_i a ha g hg hg1 g' hg' g'' hg'' hn
    obtain ⟨a', rfl⟩ := hlift a ha
    exact hφ.centralIsogenyPullback_opposite q hq hS hT t h ht a' g hg hg1 g' hg' g'' hg'' hn

end IsRootDatumValuation

/-- Pull back an actual valuation along the supplied central-isogeny square. -/
def centralIsogenyValuationPullback
    (φ : {φ : RootFunctionFamily T G // IsRootDatumValuation j φ}) :
    {ψ : RootFunctionFamily S C // IsRootDatumValuation i ψ} :=
  ⟨centralIsogenyPullback q hq hS hT t h ht φ.val,
    φ.property.centralIsogenyPullback_isRootDatumValuation q hq hS hT t h ht⟩

@[simp] theorem centralIsogenyValuationPullback_val
    (φ : {φ : RootFunctionFamily T G // IsRootDatumValuation j φ}) :
    (centralIsogenyValuationPullback q hq hS hT t h ht φ).val =
      centralIsogenyPullback q hq hS hT t h ht φ.val := rfl

end Langlands.Geometry.Building
