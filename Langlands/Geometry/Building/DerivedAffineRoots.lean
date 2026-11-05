import Langlands.Geometry.Building.DerivedApartment
import Langlands.Geometry.Building.AffineWeylTransport

/-! # Actual affine roots and Weyl groups under derived pullback -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
    {T A S : CommGroupScheme (Spec (CommRingCat.of k))}
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (e : T ⟶ S) (c : A ⟶ S) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G)
    (d : D ⟶ G) (hd : IsDerivedSubgroup d)
    (h : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hT : IsSplitTorus T.toGrp) (hS : IsSplitTorus S.toGrp)
    (hA : IsSplitTorus A.toGrp)
    [Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))

variable [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    (hi : IsMaximalSplitTorus i) {ω : kˣ → ℝ} (P : KPApartmentData i ω)

/-- Inverse precomposition by the actual affine apartment pullback. -/
def affineFunctionalDerivedPullbackEquiv :
    (P.Apartment →ᵃ[ℝ] ℝ) ≃ₗ[ℝ]
      ((P.derivedPullback e c j i d hd h hT hS hA hc hi).Apartment →ᵃ[ℝ] ℝ) :=
  AffineRootSystem.affineFunctionalTransport
    (P.derivedApartmentAffineEquiv e c j i d hd h hT hS hA hc hi)

@[simp] theorem affineFunctionalDerivedPullbackEquiv_apply_map
    (ψ : P.Apartment →ᵃ[ℝ] ℝ) (x : P.Apartment) :
    P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi ψ
        (P.derivedApartmentEquiv e c j i d hd h hT hS hA hc hi x) = ψ x := by
  change ψ ((P.derivedApartmentAffineEquiv e c j i d hd h hT hS hA hc hi).symm
    (P.derivedApartmentAffineEquiv e c j i d hd h hT hS hA hc hi x)) = ψ x
  rw [AffineEquiv.symm_apply_apply]

/-- The transported derivative composes with the forward reduced torus map. -/
theorem affineFunctionalDerivedPullbackEquiv_linear_apply
    (ψ : P.Apartment →ᵃ[ℝ] ℝ) (v : TranslationSpace j) :
    (P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi ψ).linear v =
      ψ.linear (derivedTranslationEquiv e c j i d hd h hT hS hA hc v) := rfl

/-- The derivatives are precisely the corresponding actual root forms. -/
theorem affineFunctionalDerivedPullbackEquiv_linear_eq_rootForm_iff
    (ψ : P.Apartment →ᵃ[ℝ] ℝ) (a : relativeRoots i) :
    (P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi ψ).linear =
        rootForm j (RelativeRoot.derivedRelativeRootEquiv e c j i d hd h hT hS hA hc a) ↔
      ψ.linear = rootForm i a := by
  constructor
  · intro hψ
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := (derivedTranslationEquiv e c j i d hd h hT hS hA hc).surjective w
    rw [← P.affineFunctionalDerivedPullbackEquiv_linear_apply e c j i d hd h hT hS hA hc hi,
      hψ, rootForm_derivedTranslationEquiv]
  · intro hψ
    apply LinearMap.ext
    intro v
    rw [P.affineFunctionalDerivedPullbackEquiv_linear_apply e c j i d hd h hT hS hA hc hi,
      hψ, rootForm_derivedTranslationEquiv e c j i d hd h hT hS hA hc]

/-- The same real constant is added on both actual apartments. -/
theorem affineFunctionalDerivedPullbackEquiv_add_const
    (ψ : P.Apartment →ᵃ[ℝ] ℝ) (rconst : ℝ) :
    P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi
        (ψ + AffineMap.const ℝ P.Apartment rconst) =
      P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi ψ +
        AffineMap.const ℝ (P.derivedPullback e c j i d hd h hT hS hA hc hi).Apartment rconst := by
  apply AffineMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (P.derivedApartmentEquiv e c j i d hd h hT hS hA hc hi).surjective y
  simp only [affineFunctionalDerivedPullbackEquiv_apply_map,
    AffineMap.coe_add, Pi.add_apply, AffineMap.coe_const, Function.const_apply]

/-- Filtration reflection explicitly retains membership in the source root group. -/
theorem mem_filtration_derivedPullback_iff (x : P.Apartment)
    (a : relativeRoots i) (r : ℝ) (g : rationalPoints D) :
    g ∈ (P.derivedPullback e c j i d hd h hT hS hA hc hi).filtration
        (P.derivedApartmentEquiv e c j i d hd h hT hS hA hc hi x) (e ≫ a.val) r ↔
      g ∈ rootGroupPoints j (e ≫ a.val) ∧
        rationalPoints.map d g ∈ P.filtration x a.val r := by
  exact rootFiltration_derivedPullback_iff e c j i d hd h hT hS hA hc x.val a r g

/-- An actual affine root group is the restricted inverse image of the target group. -/
theorem mem_affineRootGroup_derivedPullback_iff (a : relativeRoots i)
    (ψ : P.Apartment →ᵃ[ℝ] ℝ) (g : rationalPoints D) :
    g ∈ (P.derivedPullback e c j i d hd h hT hS hA hc hi).affineRootGroup (e ≫ a.val)
        (P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi ψ) ↔
      g ∈ rootGroupPoints j (e ≫ a.val) ∧
        rationalPoints.map d g ∈ P.affineRootGroup a.val ψ := by
  constructor
  · intro hg
    refine ⟨(P.derivedPullback e c j i d hd h hT hS hA hc hi).affineRootGroup_le_rootGroupPoints
      _ _ hg, ?_⟩
    simp only [affineRootGroup, Subgroup.mem_iInf] at hg ⊢
    intro x
    have hx := hg (P.derivedApartmentEquiv e c j i d hd h hT hS hA hc hi x)
    rw [affineFunctionalDerivedPullbackEquiv_apply_map] at hx
    exact ((P.mem_filtration_derivedPullback_iff e c j i d hd h hT hS hA hc hi x a _ g).mp hx).2
  · rintro ⟨hg, hqg⟩
    simp only [affineRootGroup, Subgroup.mem_iInf] at hqg ⊢
    intro y
    obtain ⟨x, rfl⟩ := (P.derivedApartmentEquiv e c j i d hd h hT hS hA hc hi).surjective y
    rw [affineFunctionalDerivedPullbackEquiv_apply_map]
    exact (P.mem_filtration_derivedPullback_iff e c j i d hd h hT hS hA hc hi x a _ g).mpr
      ⟨hg, hqg x⟩

/-- Every target affine root-group point lifts inside its corresponding source root group. -/
theorem map_affineRootGroup_derivedPullback (a : relativeRoots i)
    (ψ : P.Apartment →ᵃ[ℝ] ℝ) :
    ((P.derivedPullback e c j i d hd h hT hS hA hc hi).affineRootGroup (e ≫ a.val)
      (P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi ψ)).map
        (rationalPoints.map d) = P.affineRootGroup a.val ψ := by
  apply Subgroup.ext
  intro y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ((P.mem_affineRootGroup_derivedPullback_iff e c j i d hd h hT hS hA hc hi a ψ g).mp hg).2
  · intro hy
    obtain ⟨g, hg⟩ := (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a).surjective
      ⟨y, P.affineRootGroup_le_rootGroupPoints a.val ψ hy⟩
    have hg' : rationalPoints.map d g.val = y := congrArg Subtype.val hg
    refine ⟨g.val, ?_, hg'⟩
    exact (P.mem_affineRootGroup_derivedPullback_iff e c j i d hd h hT hS hA hc hi a ψ g.val).mpr
      ⟨g.property, by rw [hg']; exact hy⟩

/-- Strict root-group membership has the same restricted inverse-image formula. -/
theorem mem_affineRootGroupPlus_derivedPullback_iff (a : relativeRoots i)
    (ψ : P.Apartment →ᵃ[ℝ] ℝ) (g : rationalPoints D) :
    g ∈ (P.derivedPullback e c j i d hd h hT hS hA hc hi).affineRootGroupPlus (e ≫ a.val)
        (P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi ψ) ↔
      g ∈ rootGroupPoints j (e ≫ a.val) ∧
        rationalPoints.map d g ∈ P.affineRootGroupPlus a.val ψ := by
  rw [mem_affineRootGroupPlus, mem_affineRootGroupPlus]
  constructor
  · rintro ⟨rconst, hlocal, hg⟩
    rw [← P.affineFunctionalDerivedPullbackEquiv_add_const e c j i d hd h hT hS hA hc hi] at hg
    have he := (P.mem_affineRootGroup_derivedPullback_iff
      e c j i d hd h hT hS hA hc hi a _ g).mp hg
    exact ⟨he.1, rconst, hlocal, he.2⟩
  · rintro ⟨hg, rconst, hlocal, hqg⟩
    refine ⟨rconst, hlocal, ?_⟩
    rw [← P.affineFunctionalDerivedPullbackEquiv_add_const e c j i d hd h hT hS hA hc hi]
    exact (P.mem_affineRootGroup_derivedPullback_iff e c j i d hd h hT hS hA hc hi a _ g).mpr
      ⟨hg, hqg⟩

/-- The strict affine root groups have exactly the original target groups as images. -/
theorem map_affineRootGroupPlus_derivedPullback (a : relativeRoots i)
    (ψ : P.Apartment →ᵃ[ℝ] ℝ) :
    ((P.derivedPullback e c j i d hd h hT hS hA hc hi).affineRootGroupPlus (e ≫ a.val)
      (P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi ψ)).map
        (rationalPoints.map d) = P.affineRootGroupPlus a.val ψ := by
  apply Subgroup.ext
  intro y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ((P.mem_affineRootGroupPlus_derivedPullback_iff
      e c j i d hd h hT hS hA hc hi a ψ g).mp hg).2
  · intro hy
    obtain ⟨g, hg⟩ := (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a).surjective
      ⟨y, P.affineRootGroup_le_rootGroupPoints a.val ψ (P.affineRootGroupPlus_le _ _ hy)⟩
    have hg' : rationalPoints.map d g.val = y := congrArg Subtype.val hg
    refine ⟨g.val, ?_, hg'⟩
    exact (P.mem_affineRootGroupPlus_derivedPullback_iff
      e c j i d hd h hT hS hA hc hi a ψ g.val).mpr ⟨g.property, by rw [hg']; exact hy⟩

include c hd h hT hS hA hc in
omit [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom] in
private theorem rootPointMap_injOn (a : relativeRoots i) :
    Set.InjOn (rationalPoints.map d) (rootGroupPoints j (e ≫ a.val)) := by
  intro g hg v hv heq
  have he : derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a ⟨g, hg⟩ =
      derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a ⟨v, hv⟩ := by
    apply Subtype.ext
    exact heq
  exact congrArg Subtype.val
    ((derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a).injective he)

include c hd h hT hS hA hc in
omit [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom] in
private theorem map_rootGroupPoints (a : relativeRoots i) :
    (rootGroupPoints j (e ≫ a.val)).map (rationalPoints.map d) = rootGroupPoints i a.val := by
  apply Subgroup.ext
  intro y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a ⟨g, hg⟩).property
  · intro hy
    obtain ⟨g, hg⟩ := (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a).surjective ⟨y, hy⟩
    exact ⟨g.val, g.property, congrArg Subtype.val hg⟩

include c hd h hT hS hA hc in
omit [Mono i.hom.hom.left] [Mono j.hom.hom.left] in
/-- The missing-double-root convention is preserved on corresponding actual roots. -/
theorem map_doubleRootGroupPoints_derivedPullback (a : relativeRoots i) :
    (doubleRootGroupPoints j (e ≫ a.val)).map (rationalPoints.map d) =
      doubleRootGroupPoints i a.val := by
  classical
  have he : e ≫ ((2 : ℕ) • a.val) = (2 : ℕ) • (e ≫ a.val) :=
    Preadditive.comp_nsmul e a.val 2
  have hz : c ≫ (2 • a.val) = 0 := by
    rw [Preadditive.comp_nsmul, root_restrict_eq_zero_of_isCentral i c hA hc a.property,
      nsmul_zero]
  have h2 : 2 • (e ≫ a.val) ∈ relativeRoots j ↔ 2 • a.val ∈ relativeRoots i := by
    rw [← he]
    exact derivedRoot_mem_iff_of_central_vanishing e c j i d hd h hT hS hA hc _ hz
  by_cases ha : 2 • a.val ∈ relativeRoots i
  · rw [doubleRootGroupPoints, ite_eq_left (h2.mpr ha), doubleRootGroupPoints, ite_eq_left ha,
      ← he]
    exact map_rootGroupPoints e c j i d hd h hT hS hA hc ⟨2 • a.val, ha⟩
  · rw [doubleRootGroupPoints, ite_eq_right (fun hs => ha (h2.mp hs)),
      doubleRootGroupPoints, ite_eq_right ha, Subgroup.map_bot]

omit [LocallyOfFiniteType D.X.hom] [Mono j.hom.hom.left] in
private theorem doubleRootGroupPoints_le (a : characterLattice T) :
    doubleRootGroupPoints j a ≤ rootGroupPoints j a := by
  classical
  unfold doubleRootGroupPoints
  split_ifs with ha
  · exact RelativeRoot.subgroup_nsmul_le j a (show 0 < (2 : ℕ) by omega) _
  · exact bot_le

/-- The ordinary affine-root noncontainment test is reflected inside one root group. -/
theorem affineRootGroup_subset_mul_derivedPullback_iff (a : relativeRoots i)
    (ψ : P.Apartment →ᵃ[ℝ] ℝ) :
    ((P.derivedPullback e c j i d hd h hT hS hA hc hi).affineRootGroup (e ≫ a.val)
          (P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi ψ) :
        Set (rationalPoints D)) ⊆
      ((P.derivedPullback e c j i d hd h hT hS hA hc hi).affineRootGroupPlus (e ≫ a.val)
          (P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi ψ) :
        Set (rationalPoints D)) *
          (doubleRootGroupPoints j (e ≫ a.val) : Set (rationalPoints D)) ↔
    (P.affineRootGroup a.val ψ : Set (rationalPoints G)) ⊆
      (P.affineRootGroupPlus a.val ψ : Set (rationalPoints G)) *
        (doubleRootGroupPoints i a.val : Set (rationalPoints G)) := by
  let E := P.derivedPullback e c j i d hd h hT hS hA hc hi
  let psiSource := P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi ψ
  have hmul : (E.affineRootGroupPlus (e ≫ a.val) psiSource : Set (rationalPoints D)) *
        (doubleRootGroupPoints j (e ≫ a.val) : Set (rationalPoints D)) ⊆
      (rootGroupPoints j (e ≫ a.val) : Set (rationalPoints D)) := by
    rintro _ ⟨u, hu, v, hv, rfl⟩
    exact (rootGroupPoints j (e ≫ a.val)).mul_mem
      (E.affineRootGroup_le_rootGroupPoints _ _ (E.affineRootGroupPlus_le _ _ hu))
      (doubleRootGroupPoints_le j (e ≫ a.val) hv)
  have hlocal := (rootPointMap_injOn e c j i d hd h hT hS hA hc a).image_subset_image_iff
    (E.affineRootGroup_le_rootGroupPoints _ psiSource) hmul
  rw [Set.image_mul] at hlocal
  change
    (((E.affineRootGroup (e ≫ a.val) psiSource).map (rationalPoints.map d) :
        Set (rationalPoints G)) ⊆
      ((E.affineRootGroupPlus (e ≫ a.val) psiSource).map (rationalPoints.map d) :
        Set (rationalPoints G)) *
      ((doubleRootGroupPoints j (e ≫ a.val)).map (rationalPoints.map d) :
        Set (rationalPoints G))) ↔ _ at hlocal
  dsimp only [E, psiSource] at hlocal
  rw [P.map_affineRootGroup_derivedPullback e c j i d hd h hT hS hA hc hi,
    P.map_affineRootGroupPlus_derivedPullback e c j i d hd h hT hS hA hc hi,
    map_doubleRootGroupPoints_derivedPullback e c j i d hd h hT hS hA hc] at hlocal
  exact hlocal.symm

/-- Extended affine roots are preserved and reflected by the actual functional map. -/
theorem mem_extendedAffineRoots_derivedPullback_iff (ψ : P.Apartment →ᵃ[ℝ] ℝ) :
    P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi ψ ∈
        (P.derivedPullback e c j i d hd h hT hS hA hc hi).extendedAffineRoots ↔
      ψ ∈ P.extendedAffineRoots := by
  constructor
  · rintro ⟨a', hψ, hne⟩
    obtain ⟨a, rfl⟩ := (RelativeRoot.derivedRelativeRootEquiv e c j i d hd h hT hS hA hc).surjective a'
    refine ⟨a, (P.affineFunctionalDerivedPullbackEquiv_linear_eq_rootForm_iff
      e c j i d hd h hT hS hA hc hi ψ a).mp hψ, ?_⟩
    intro heq
    apply hne
    apply SetLike.coe_injective
    apply ((rootPointMap_injOn e c j i d hd h hT hS hA hc a).image_eq_image_iff
      (fun _ hg => (P.derivedPullback e c j i d hd h hT hS hA hc hi).affineRootGroup_le_rootGroupPoints
        _ _ ((P.derivedPullback e c j i d hd h hT hS hA hc hi).affineRootGroupPlus_le _ _ hg))
      ((P.derivedPullback e c j i d hd h hT hS hA hc hi).affineRootGroup_le_rootGroupPoints _ _)).mp
    change
      (((P.derivedPullback e c j i d hd h hT hS hA hc hi).affineRootGroupPlus (e ≫ a.val)
        (P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi ψ)).map
          (rationalPoints.map d) : Set (rationalPoints G)) =
      (((P.derivedPullback e c j i d hd h hT hS hA hc hi).affineRootGroup (e ≫ a.val)
        (P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi ψ)).map
          (rationalPoints.map d) : Set (rationalPoints G))
    rw [P.map_affineRootGroupPlus_derivedPullback e c j i d hd h hT hS hA hc hi,
      P.map_affineRootGroup_derivedPullback e c j i d hd h hT hS hA hc hi, heq]
  · rintro ⟨a, hψ, hne⟩
    refine ⟨RelativeRoot.derivedRelativeRootEquiv e c j i d hd h hT hS hA hc a,
      (P.affineFunctionalDerivedPullbackEquiv_linear_eq_rootForm_iff
        e c j i d hd h hT hS hA hc hi ψ a).mpr hψ, ?_⟩
    intro heq
    apply hne
    rw [← P.map_affineRootGroupPlus_derivedPullback e c j i d hd h hT hS hA hc hi a ψ,
      ← P.map_affineRootGroup_derivedPullback e c j i d hd h hT hS hA hc hi a ψ]
    exact congrArg (Subgroup.map (rationalPoints.map d)) heq

/-- Ordinary affine roots retain exactly their original doubled-root test. -/
theorem mem_affineRoots_derivedPullback_iff (ψ : P.Apartment →ᵃ[ℝ] ℝ) :
    P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi ψ ∈
        (P.derivedPullback e c j i d hd h hT hS hA hc hi).affineRoots ↔
      ψ ∈ P.affineRoots := by
  constructor
  · rintro ⟨a', hψ, hnot⟩
    obtain ⟨a, rfl⟩ := (RelativeRoot.derivedRelativeRootEquiv e c j i d hd h hT hS hA hc).surjective a'
    refine ⟨a, (P.affineFunctionalDerivedPullbackEquiv_linear_eq_rootForm_iff
      e c j i d hd h hT hS hA hc hi ψ a).mp hψ, ?_⟩
    exact fun hs => hnot ((P.affineRootGroup_subset_mul_derivedPullback_iff
      e c j i d hd h hT hS hA hc hi a ψ).mpr hs)
  · rintro ⟨a, hψ, hnot⟩
    refine ⟨RelativeRoot.derivedRelativeRootEquiv e c j i d hd h hT hS hA hc a,
      (P.affineFunctionalDerivedPullbackEquiv_linear_eq_rootForm_iff
        e c j i d hd h hT hS hA hc hi ψ a).mpr hψ, ?_⟩
    exact fun hs => hnot ((P.affineRootGroup_subset_mul_derivedPullback_iff
      e c j i d hd h hT hS hA hc hi a ψ).mp hs)

/-- The actual functional map restricts to the extended affine-root subtypes. -/
def extendedAffineRootsDerivedPullbackEquiv :
    P.extendedAffineRoots ≃ (P.derivedPullback e c j i d hd h hT hS hA hc hi).extendedAffineRoots :=
  (P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi).toEquiv.subtypeEquiv
    (fun ψ => (P.mem_extendedAffineRoots_derivedPullback_iff e c j i d hd h hT hS hA hc hi ψ).symm)

/-- The actual functional map restricts to the ordinary affine-root subtypes. -/
def affineRootsDerivedPullbackEquiv :
    P.affineRoots ≃ (P.derivedPullback e c j i d hd h hT hS hA hc hi).affineRoots :=
  (P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi).toEquiv.subtypeEquiv
    (fun ψ => (P.mem_affineRoots_derivedPullback_iff e c j i d hd h hT hS hA hc hi ψ).symm)

/-- Inverse precomposition gives exactly the affine roots of the source apartment. -/
theorem transportedRoots_derivedPullback :
    AffineRootSystem.transportedRoots (P.derivedApartmentAffineEquiv e c j i d hd h hT hS hA hc hi)
        P.affineRoots = (P.derivedPullback e c j i d hd h hT hS hA hc hi).affineRoots := by
  ext psiSource
  obtain ⟨ψ, rfl⟩ :=
    (P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi).surjective psiSource
  change
    (P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi ψ ∈
        (P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi) '' P.affineRoots) ↔ _
  constructor
  · rintro ⟨φ, hφ, he⟩
    have hφψ := (P.affineFunctionalDerivedPullbackEquiv e c j i d hd h hT hS hA hc hi).injective he
    subst φ
    exact (P.mem_affineRoots_derivedPullback_iff e c j i d hd h hT hS hA hc hi ψ).mpr hφ
  · intro hψ
    exact ⟨ψ, (P.mem_affineRoots_derivedPullback_iff e c j i d hd h hT hS hA hc hi ψ).mp hψ, rfl⟩

/-- The actual apartment equivalence conjugates the original affine Weyl groups. -/
theorem map_affineWeylGroup_derivedPullback :
    (AffineRootSystem.affineWeylGroup P.affineRoots).map
        (AffineRootSystem.affineConjugation
          (P.derivedApartmentAffineEquiv e c j i d hd h hT hS hA hc hi)).toMonoidHom =
      AffineRootSystem.affineWeylGroup
        (P.derivedPullback e c j i d hd h hT hS hA hc hi).affineRoots :=
  AffineRootSystem.map_affineWeylGroup_of_transportedRoots_eq _
    (P.transportedRoots_derivedPullback e c j i d hd h hT hS hA hc hi)

end Langlands.Geometry.Building.KPApartmentData
