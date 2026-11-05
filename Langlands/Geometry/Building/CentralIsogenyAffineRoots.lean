import Langlands.Geometry.Building.CentralIsogenyApartment
import Langlands.Geometry.Building.AffineWeylTransport

/-! # Actual affine roots and Weyl groups under central-isogeny pullback -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

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
  {ω : kˣ → ℝ} (D : KPApartmentData j ω)

/-- Inverse precomposition by the actual affine apartment pullback. -/
def affineFunctionalCentralIsogenyPullbackEquiv :
    (D.Apartment →ᵃ[ℝ] ℝ) ≃ₗ[ℝ]
      ((D.centralIsogenyPullback q hq hS hT t h ht).Apartment →ᵃ[ℝ] ℝ) :=
  AffineRootSystem.affineFunctionalTransport
    (D.centralIsogenyApartmentAffineEquiv q hq hS hT t h ht)

@[simp] theorem affineFunctionalCentralIsogenyPullbackEquiv_apply_map
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (x : D.Apartment) :
    D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ψ
        (D.centralIsogenyApartmentEquiv q hq hS hT t h ht x) = ψ x := by
  change ψ ((D.centralIsogenyApartmentAffineEquiv q hq hS hT t h ht).symm
    (D.centralIsogenyApartmentAffineEquiv q hq hS hT t h ht x)) = ψ x
  rw [AffineEquiv.symm_apply_apply]

/-- The transported derivative composes with the forward reduced torus map. -/
theorem affineFunctionalCentralIsogenyPullbackEquiv_linear_apply
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (v : TranslationSpace i) :
    (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ψ).linear v =
      ψ.linear (centralIsogenyTranslationEquiv q hq hS hT t h ht v) := rfl

/-- The derivatives are precisely the corresponding actual root forms. -/
theorem affineFunctionalCentralIsogenyPullbackEquiv_linear_eq_rootForm_iff
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (a : relativeRoots j) :
    (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ψ).linear =
        rootForm i (centralIsogenyRootPullbackEquiv q hq hS hT t h ht a) ↔
      ψ.linear = rootForm j a := by
  constructor
  · intro hψ
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := (centralIsogenyTranslationEquiv q hq hS hT t h ht).surjective w
    rw [← D.affineFunctionalCentralIsogenyPullbackEquiv_linear_apply q hq hS hT t h ht,
      hψ, rootForm_centralIsogenyTranslationEquiv]
  · intro hψ
    apply LinearMap.ext
    intro v
    rw [D.affineFunctionalCentralIsogenyPullbackEquiv_linear_apply, hψ,
      rootForm_centralIsogenyTranslationEquiv]

/-- The same real constant is added on both actual apartments. -/
theorem affineFunctionalCentralIsogenyPullbackEquiv_add_const
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (c : ℝ) :
    D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht
        (ψ + AffineMap.const ℝ D.Apartment c) =
      D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ψ +
        AffineMap.const ℝ (D.centralIsogenyPullback q hq hS hT t h ht).Apartment c := by
  apply AffineMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (D.centralIsogenyApartmentEquiv q hq hS hT t h ht).surjective y
  simp only [affineFunctionalCentralIsogenyPullbackEquiv_apply_map,
    AffineMap.coe_add, Pi.add_apply, AffineMap.coe_const, Function.const_apply]

/-- Filtration reflection explicitly retains membership in the source root group. -/
theorem mem_filtration_centralIsogenyPullback_iff (x : D.Apartment)
    (a : relativeRoots j) (r : ℝ) (g : rationalPoints C) :
    g ∈ (D.centralIsogenyPullback q hq hS hT t h ht).filtration
        (D.centralIsogenyApartmentEquiv q hq hS hT t h ht x) (t ≫ a.val) r ↔
      g ∈ rootGroupPoints i (t ≫ a.val) ∧
        rationalPoints.map q g ∈ D.filtration x a.val r := by
  exact rootFiltration_centralIsogenyPullback_iff q hq hS hT t h ht x.val a r g

/-- An actual affine root group is the restricted inverse image of the target group. -/
theorem mem_affineRootGroup_centralIsogenyPullback_iff (a : relativeRoots j)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (g : rationalPoints C) :
    g ∈ (D.centralIsogenyPullback q hq hS hT t h ht).affineRootGroup (t ≫ a.val)
        (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ψ) ↔
      g ∈ rootGroupPoints i (t ≫ a.val) ∧
        rationalPoints.map q g ∈ D.affineRootGroup a.val ψ := by
  constructor
  · intro hg
    refine ⟨(D.centralIsogenyPullback q hq hS hT t h ht).affineRootGroup_le_rootGroupPoints
      _ _ hg, ?_⟩
    simp only [affineRootGroup, Subgroup.mem_iInf] at hg ⊢
    intro x
    have hx := hg (D.centralIsogenyApartmentEquiv q hq hS hT t h ht x)
    rw [affineFunctionalCentralIsogenyPullbackEquiv_apply_map] at hx
    exact ((D.mem_filtration_centralIsogenyPullback_iff q hq hS hT t h ht x a _ g).mp hx).2
  · rintro ⟨hg, hqg⟩
    simp only [affineRootGroup, Subgroup.mem_iInf] at hqg ⊢
    intro y
    obtain ⟨x, rfl⟩ := (D.centralIsogenyApartmentEquiv q hq hS hT t h ht).surjective y
    rw [affineFunctionalCentralIsogenyPullbackEquiv_apply_map]
    exact (D.mem_filtration_centralIsogenyPullback_iff q hq hS hT t h ht x a _ g).mpr
      ⟨hg, hqg x⟩

/-- Every target affine root-group point lifts inside its corresponding source root group. -/
theorem map_affineRootGroup_centralIsogenyPullback (a : relativeRoots j)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    ((D.centralIsogenyPullback q hq hS hT t h ht).affineRootGroup (t ≫ a.val)
      (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ψ)).map
        (rationalPoints.map q) = D.affineRootGroup a.val ψ := by
  apply Subgroup.ext
  intro y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ((D.mem_affineRootGroup_centralIsogenyPullback_iff q hq hS hT t h ht a ψ g).mp hg).2
  · intro hy
    obtain ⟨g, hg⟩ := (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a).surjective
      ⟨y, D.affineRootGroup_le_rootGroupPoints a.val ψ hy⟩
    have hg' : rationalPoints.map q g.val = y := congrArg Subtype.val hg
    refine ⟨g.val, ?_, hg'⟩
    exact (D.mem_affineRootGroup_centralIsogenyPullback_iff q hq hS hT t h ht a ψ g.val).mpr
      ⟨g.property, by rw [hg']; exact hy⟩

/-- Strict root-group membership has the same restricted inverse-image formula. -/
theorem mem_affineRootGroupPlus_centralIsogenyPullback_iff (a : relativeRoots j)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (g : rationalPoints C) :
    g ∈ (D.centralIsogenyPullback q hq hS hT t h ht).affineRootGroupPlus (t ≫ a.val)
        (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ψ) ↔
      g ∈ rootGroupPoints i (t ≫ a.val) ∧
        rationalPoints.map q g ∈ D.affineRootGroupPlus a.val ψ := by
  rw [mem_affineRootGroupPlus, mem_affineRootGroupPlus]
  constructor
  · rintro ⟨c, hc, hg⟩
    rw [← D.affineFunctionalCentralIsogenyPullbackEquiv_add_const] at hg
    have he := (D.mem_affineRootGroup_centralIsogenyPullback_iff
      q hq hS hT t h ht a _ g).mp hg
    exact ⟨he.1, c, hc, he.2⟩
  · rintro ⟨hg, c, hc, hqg⟩
    refine ⟨c, hc, ?_⟩
    rw [← D.affineFunctionalCentralIsogenyPullbackEquiv_add_const]
    exact (D.mem_affineRootGroup_centralIsogenyPullback_iff q hq hS hT t h ht a _ g).mpr
      ⟨hg, hqg⟩

/-- The strict affine root groups have exactly the original target groups as images. -/
theorem map_affineRootGroupPlus_centralIsogenyPullback (a : relativeRoots j)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    ((D.centralIsogenyPullback q hq hS hT t h ht).affineRootGroupPlus (t ≫ a.val)
      (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ψ)).map
        (rationalPoints.map q) = D.affineRootGroupPlus a.val ψ := by
  apply Subgroup.ext
  intro y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ((D.mem_affineRootGroupPlus_centralIsogenyPullback_iff
      q hq hS hT t h ht a ψ g).mp hg).2
  · intro hy
    obtain ⟨g, hg⟩ := (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a).surjective
      ⟨y, D.affineRootGroup_le_rootGroupPoints a.val ψ (D.affineRootGroupPlus_le _ _ hy)⟩
    have hg' : rationalPoints.map q g.val = y := congrArg Subtype.val hg
    refine ⟨g.val, ?_, hg'⟩
    exact (D.mem_affineRootGroupPlus_centralIsogenyPullback_iff
      q hq hS hT t h ht a ψ g.val).mpr ⟨g.property, by rw [hg']; exact hy⟩

omit [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    [LocallyOfFiniteType C.X.hom] [LocallyOfFiniteType G.X.hom] in
include hq hS h ht in
private theorem rootPointMap_injOn (a : relativeRoots j) :
    Set.InjOn (rationalPoints.map q) (rootGroupPoints i (t ≫ a.val)) := by
  intro g hg v hv heq
  have he : centralIsogenyRootGroupPointsEquiv q hq hS t h ht a ⟨g, hg⟩ =
      centralIsogenyRootGroupPointsEquiv q hq hS t h ht a ⟨v, hv⟩ := by
    apply Subtype.ext
    exact heq
  exact congrArg Subtype.val
    ((centralIsogenyRootGroupPointsEquiv q hq hS t h ht a).injective he)

omit [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    [LocallyOfFiniteType C.X.hom] [LocallyOfFiniteType G.X.hom] in
include hq hS h ht in
private theorem map_rootGroupPoints (a : relativeRoots j) :
    (rootGroupPoints i (t ≫ a.val)).map (rationalPoints.map q) = rootGroupPoints j a.val := by
  apply Subgroup.ext
  intro y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a ⟨g, hg⟩).property
  · intro hy
    obtain ⟨g, hg⟩ := (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a).surjective ⟨y, hy⟩
    exact ⟨g.val, g.property, congrArg Subtype.val hg⟩

omit [Mono i.hom.hom.left] [Mono j.hom.hom.left] in
include hq hS hT h ht in
/-- The convention for a missing double root is respected by the actual point map. -/
theorem map_doubleRootGroupPoints_centralIsogenyPullback (a : characterLattice T) :
    (doubleRootGroupPoints i (t ≫ a)).map (rationalPoints.map q) =
      doubleRootGroupPoints j a := by
  classical
  have he : t ≫ ((2 : ℕ) • a) = (2 : ℕ) • (t ≫ a) :=
    Preadditive.comp_nsmul t a 2
  have h2 : 2 • (t ≫ a) ∈ relativeRoots i ↔ 2 • a ∈ relativeRoots j := by
    rw [← he]
    exact centralIsogenyRoot_mem_iff q hq hS hT t h ht (2 • a)
  by_cases ha : 2 • a ∈ relativeRoots j
  · rw [doubleRootGroupPoints, ite_eq_left (h2.mpr ha), doubleRootGroupPoints, ite_eq_left ha,
      ← he]
    exact map_rootGroupPoints q hq hS t h ht ⟨2 • a, ha⟩
  · rw [doubleRootGroupPoints, ite_eq_right (fun hs => ha (h2.mp hs)),
      doubleRootGroupPoints, ite_eq_right ha, Subgroup.map_bot]

omit [Mono i.hom.hom.left] [Mono j.hom.hom.left] [LocallyOfFiniteType C.X.hom] in
private theorem doubleRootGroupPoints_le (a : characterLattice S) :
    doubleRootGroupPoints i a ≤ rootGroupPoints i a := by
  classical
  unfold doubleRootGroupPoints
  split_ifs with ha
  · exact RelativeRoot.subgroup_nsmul_le i a (show 0 < (2 : ℕ) by omega) _
  · exact bot_le

/-- The ordinary affine-root noncontainment test is reflected inside one root group. -/
theorem affineRootGroup_subset_mul_centralIsogenyPullback_iff (a : relativeRoots j)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    ((D.centralIsogenyPullback q hq hS hT t h ht).affineRootGroup (t ≫ a.val)
          (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ψ) :
        Set (rationalPoints C)) ⊆
      ((D.centralIsogenyPullback q hq hS hT t h ht).affineRootGroupPlus (t ≫ a.val)
          (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ψ) :
        Set (rationalPoints C)) *
          (doubleRootGroupPoints i (t ≫ a.val) : Set (rationalPoints C)) ↔
    (D.affineRootGroup a.val ψ : Set (rationalPoints G)) ⊆
      (D.affineRootGroupPlus a.val ψ : Set (rationalPoints G)) *
        (doubleRootGroupPoints j a.val : Set (rationalPoints G)) := by
  let E := D.centralIsogenyPullback q hq hS hT t h ht
  let psiSource := D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ψ
  have hmul : (E.affineRootGroupPlus (t ≫ a.val) psiSource : Set (rationalPoints C)) *
        (doubleRootGroupPoints i (t ≫ a.val) : Set (rationalPoints C)) ⊆
      (rootGroupPoints i (t ≫ a.val) : Set (rationalPoints C)) := by
    rintro _ ⟨u, hu, v, hv, rfl⟩
    exact (rootGroupPoints i (t ≫ a.val)).mul_mem
      (E.affineRootGroup_le_rootGroupPoints _ _ (E.affineRootGroupPlus_le _ _ hu))
      (doubleRootGroupPoints_le (t ≫ a.val) hv)
  have hc := (rootPointMap_injOn q hq hS t h ht a).image_subset_image_iff
    (E.affineRootGroup_le_rootGroupPoints _ psiSource) hmul
  rw [Set.image_mul] at hc
  change
    (((E.affineRootGroup (t ≫ a.val) psiSource).map (rationalPoints.map q) :
        Set (rationalPoints G)) ⊆
      ((E.affineRootGroupPlus (t ≫ a.val) psiSource).map (rationalPoints.map q) :
        Set (rationalPoints G)) *
      ((doubleRootGroupPoints i (t ≫ a.val)).map (rationalPoints.map q) :
        Set (rationalPoints G))) ↔ _ at hc
  dsimp only [E, psiSource] at hc
  rw [D.map_affineRootGroup_centralIsogenyPullback,
    D.map_affineRootGroupPlus_centralIsogenyPullback,
    map_doubleRootGroupPoints_centralIsogenyPullback q hq hS hT t h ht] at hc
  exact hc.symm

/-- Extended affine roots are preserved and reflected by the actual functional map. -/
theorem mem_extendedAffineRoots_centralIsogenyPullback_iff (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ψ ∈
        (D.centralIsogenyPullback q hq hS hT t h ht).extendedAffineRoots ↔
      ψ ∈ D.extendedAffineRoots := by
  constructor
  · rintro ⟨a', hψ, hne⟩
    obtain ⟨a, rfl⟩ := (centralIsogenyRootPullbackEquiv q hq hS hT t h ht).surjective a'
    refine ⟨a, (D.affineFunctionalCentralIsogenyPullbackEquiv_linear_eq_rootForm_iff
      q hq hS hT t h ht ψ a).mp hψ, ?_⟩
    intro heq
    apply hne
    apply SetLike.coe_injective
    apply ((rootPointMap_injOn q hq hS t h ht a).image_eq_image_iff
      (fun _ hg => (D.centralIsogenyPullback q hq hS hT t h ht).affineRootGroup_le_rootGroupPoints
        _ _ ((D.centralIsogenyPullback q hq hS hT t h ht).affineRootGroupPlus_le _ _ hg))
      ((D.centralIsogenyPullback q hq hS hT t h ht).affineRootGroup_le_rootGroupPoints _ _)).mp
    change
      (((D.centralIsogenyPullback q hq hS hT t h ht).affineRootGroupPlus (t ≫ a.val)
        (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ψ)).map
          (rationalPoints.map q) : Set (rationalPoints G)) =
      (((D.centralIsogenyPullback q hq hS hT t h ht).affineRootGroup (t ≫ a.val)
        (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ψ)).map
          (rationalPoints.map q) : Set (rationalPoints G))
    rw [D.map_affineRootGroupPlus_centralIsogenyPullback,
      D.map_affineRootGroup_centralIsogenyPullback, heq]
  · rintro ⟨a, hψ, hne⟩
    refine ⟨centralIsogenyRootPullbackEquiv q hq hS hT t h ht a,
      (D.affineFunctionalCentralIsogenyPullbackEquiv_linear_eq_rootForm_iff
        q hq hS hT t h ht ψ a).mpr hψ, ?_⟩
    intro heq
    apply hne
    rw [← D.map_affineRootGroupPlus_centralIsogenyPullback q hq hS hT t h ht a ψ,
      ← D.map_affineRootGroup_centralIsogenyPullback q hq hS hT t h ht a ψ]
    exact congrArg (Subgroup.map (rationalPoints.map q)) heq

/-- Ordinary affine roots retain exactly their original doubled-root test. -/
theorem mem_affineRoots_centralIsogenyPullback_iff (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ψ ∈
        (D.centralIsogenyPullback q hq hS hT t h ht).affineRoots ↔
      ψ ∈ D.affineRoots := by
  constructor
  · rintro ⟨a', hψ, hnot⟩
    obtain ⟨a, rfl⟩ := (centralIsogenyRootPullbackEquiv q hq hS hT t h ht).surjective a'
    refine ⟨a, (D.affineFunctionalCentralIsogenyPullbackEquiv_linear_eq_rootForm_iff
      q hq hS hT t h ht ψ a).mp hψ, ?_⟩
    exact fun hs => hnot ((D.affineRootGroup_subset_mul_centralIsogenyPullback_iff
      q hq hS hT t h ht a ψ).mpr hs)
  · rintro ⟨a, hψ, hnot⟩
    refine ⟨centralIsogenyRootPullbackEquiv q hq hS hT t h ht a,
      (D.affineFunctionalCentralIsogenyPullbackEquiv_linear_eq_rootForm_iff
        q hq hS hT t h ht ψ a).mpr hψ, ?_⟩
    exact fun hs => hnot ((D.affineRootGroup_subset_mul_centralIsogenyPullback_iff
      q hq hS hT t h ht a ψ).mp hs)

/-- The actual functional map restricts to the extended affine-root subtypes. -/
def extendedAffineRootsCentralIsogenyPullbackEquiv :
    D.extendedAffineRoots ≃ (D.centralIsogenyPullback q hq hS hT t h ht).extendedAffineRoots :=
  (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht).toEquiv.subtypeEquiv
    (fun ψ => (D.mem_extendedAffineRoots_centralIsogenyPullback_iff q hq hS hT t h ht ψ).symm)

/-- The actual functional map restricts to the ordinary affine-root subtypes. -/
def affineRootsCentralIsogenyPullbackEquiv :
    D.affineRoots ≃ (D.centralIsogenyPullback q hq hS hT t h ht).affineRoots :=
  (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht).toEquiv.subtypeEquiv
    (fun ψ => (D.mem_affineRoots_centralIsogenyPullback_iff q hq hS hT t h ht ψ).symm)

/-- Inverse precomposition gives exactly the affine roots of the source apartment. -/
theorem transportedRoots_centralIsogenyPullback :
    AffineRootSystem.transportedRoots (D.centralIsogenyApartmentAffineEquiv q hq hS hT t h ht)
        D.affineRoots = (D.centralIsogenyPullback q hq hS hT t h ht).affineRoots := by
  ext psiSource
  obtain ⟨ψ, rfl⟩ :=
    (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht).surjective psiSource
  change
    (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ψ ∈
        (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht) '' D.affineRoots) ↔ _
  constructor
  · rintro ⟨φ, hφ, he⟩
    have hφψ := (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht).injective he
    subst φ
    exact (D.mem_affineRoots_centralIsogenyPullback_iff q hq hS hT t h ht ψ).mpr hφ
  · intro hψ
    exact ⟨ψ, (D.mem_affineRoots_centralIsogenyPullback_iff q hq hS hT t h ht ψ).mp hψ, rfl⟩

/-- The actual apartment equivalence conjugates the original affine Weyl groups. -/
theorem map_affineWeylGroup_centralIsogenyPullback :
    (AffineRootSystem.affineWeylGroup D.affineRoots).map
        (AffineRootSystem.affineConjugation
          (D.centralIsogenyApartmentAffineEquiv q hq hS hT t h ht)).toMonoidHom =
      AffineRootSystem.affineWeylGroup
        (D.centralIsogenyPullback q hq hS hT t h ht).affineRoots :=
  AffineRootSystem.map_affineWeylGroup_of_transportedRoots_eq _
    (D.transportedRoots_centralIsogenyPullback q hq hS hT t h ht)

end Langlands.Geometry.Building.KPApartmentData
