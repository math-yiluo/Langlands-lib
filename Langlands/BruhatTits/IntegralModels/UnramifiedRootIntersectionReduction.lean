import Langlands.BruhatTits.IntegralModels.UnramifiedRootPositiveReductionProof
import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentQuotientRoots

/-! # Upper positive reduction and incident quotient roots from root intersections -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (Ω : Set C.Apartment)
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)

/-- Root-group points of the neutral model are the root fixers of `Ω`. -/
def HasRootFixerIntersections : Prop :=
  ∀ b : relativeRoots C.i,
    rootGroupPoints C.i b ⊓ D.neutral.integralPoints = C.apartment.rootFixer b Ω

variable {C Ω D}

/-- The positive-reduction criterion for a neutral integral root point, from the
root-fixer intersections alone. -/
theorem mem_positivePoints_iff_of_rootFixerIntersections
    (hinter : HasRootFixerIntersections C Ω D) (hne : Ω.Nonempty)
    (T : IntegralTorusData D C.S C.i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)
    (a : relativeRoots C.i) {g : rationalPoints G}
    (hga : g ∈ rootGroupPoints C.i a) (hgint : g ∈ D.neutral.integralPoints) :
    g ∈ Q.positivePoints ↔ ∃ x ∈ Ω, g ∈ C.apartment.filtrationPlus x a 0 := by
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  let : Smooth D.neutral.group.X.hom := D.neutral_smooth
  let : Smooth G.X.hom := C.isConnectedReductive.smooth
  have hgBoth : g ∈ D.neutral.integralPoints ⊓ rootGroupPoints C.i a := ⟨hgint, hga⟩
  have hgFix : g ∈ C.apartment.rootFixer a Ω := by
    rw [← hinter a]
    exact ⟨hga, hgint⟩
  by_cases hg1 : g = 1
  · constructor
    · intro _
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, hx, by rw [hg1]; exact one_mem _⟩
    · intro _
      rw [hg1]
      exact one_mem _
  obtain ⟨p, hp⟩ :=
    ((rootRankOneFactorization (inertiaFixedField F) G C.isConnectedReductive
      C.S C.i C.isMaximalSplitTorus a a.property g hgBoth.2 hg1).1).exists
  have hna : -(a : characterLattice C.S) ∈ relativeRoots C.i := by
    have hflip := hp.weylAction_eq_neg C.i C.isMaximalSplitTorus.1.1
      a.2.1 hgBoth.2 hg1
    exact hflip ▸ weylAction_mapsTo_relativeRoots C.i
      (⟨p.1 * g * p.2, hp.2.2⟩ : normalizerPoints C.i) a.property
  constructor
  · intro hgpos
    by_contra hn
    have hval (x : C.Apartment) (hx : x ∈ Ω) : x.val a g = 0 := by
      have hnot : ¬ (0 : WithTop ℝ) < x.val a g := by
        intro hlt
        exact hn ⟨x, hx, KPApartmentData.mem_filtrationPlus.mpr ⟨hgBoth.2, hlt⟩⟩
      exact le_antisymm (le_of_not_gt hnot)
        ((C.apartment.mem_rootFixer.mp hgFix).2 x hx).2
    have hp1Fix : p.1 ∈ C.apartment.rootFixer (-(a : characterLattice C.S)) Ω := by
      refine C.apartment.mem_rootFixer.mpr ⟨hp.1, fun x hx => ⟨hp.1, ?_⟩⟩
      have h5 := x.isValuation.opposite a a.property g hgBoth.2 hg1
        p.1 hp.1 p.2 hp.2.1 hp.2.2
      rw [hval x hx, add_zero] at h5
      simp only [h5, WithTop.coe_zero, le_refl]
    have hp2Fix : p.2 ∈ C.apartment.rootFixer (-(a : characterLattice C.S)) Ω := by
      refine C.apartment.mem_rootFixer.mpr ⟨hp.2.1, fun x hx => ⟨hp.2.1, ?_⟩⟩
      have h5 := x.isValuation.opposite_snd a.property hgBoth.2 hg1 hp.1 hp.2.1 hp.2.2
      rw [hval x hx, add_zero] at h5
      simp only [h5, WithTop.coe_zero, le_refl]
    have hp1R : p.1 ∈ D.neutral.integralPoints := by
      rw [← hinter ⟨_, hna⟩] at hp1Fix
      exact hp1Fix.2
    have hp2R : p.2 ∈ D.neutral.integralPoints := by
      rw [← hinter ⟨_, hna⟩] at hp2Fix
      exact hp2Fix.2
    exact (T.not_mem_positivePoints_of_integral_oppositeFactors
      hT Q hQ C.isConnectedReductive C.isMaximalSplitTorus
      a.2.1 hgBoth.2 hg1 hp.1 hp.2.1 hp.2.2 hp1R hp2R) hgpos
  · rintro ⟨x, hx, hxpos⟩
    by_contra hnon
    have hpR := henselianIntegralOppositeFactors
      (fixedFieldIntegers F) (inertiaFixedField F) G D C.S C.i T
      hT Q hQ C.isConnectedReductive C.isMaximalSplitTorus
      a a.property g hgBoth.2 hg1 hgBoth.1 p hp hnon
    have hp1Fix : p.1 ∈ C.apartment.rootFixer (-(a : characterLattice C.S)) Ω := by
      rw [← hinter ⟨_, hna⟩]
      exact ⟨hp.1, hpR.1⟩
    have hge := ((C.apartment.mem_rootFixer.mp hp1Fix).2 x hx).2
    have hpos := (KPApartmentData.mem_filtrationPlus.mp hxpos).2
    have h5 := x.isValuation.opposite a a.property g hgBoth.2 hg1
      p.1 hp.1 p.2 hp.2.1 hp.2.2
    have hle : x.val a g ≤ x.val (-(a : characterLattice C.S)) p.1 + x.val a g :=
      le_add_of_nonneg_left hge
    rw [h5] at hle
    exact (not_lt_of_ge hle) hpos

/-- On a singleton, reductive reduction of a neutral root section is trivial
exactly at strictly positive depth. -/
theorem singleton_reductiveReduction_eq_one_iff_of_rootFixerIntersections
    {x : C.Apartment} (hinter : HasRootFixerIntersections C {x} D)
    (T : IntegralTorusData D C.S C.i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)
    (a : relativeRoots C.i) (z : D.neutral.integralSections)
    (hz : D.neutral.integralPointMap z ∈ rootGroupPoints C.i a.val) :
    Q.reductiveReduction z = 1 ↔
      D.neutral.integralPointMap z ∈ C.apartment.filtrationPlus x a 0 := by
  have hp := mem_positivePoints_iff_of_rootFixerIntersections hinter
    (Set.singleton_nonempty x) T hT Q hQ a hz ⟨z, rfl⟩
  simp only [Set.mem_singleton_iff, exists_eq_left] at hp
  rw [← hp]
  constructor
  · intro h1
    refine ⟨z, ?_, rfl⟩
    rw [← MonoidHom.mem_ker, Q.ker_reductiveReduction hQ.2.1] at h1
    exact h1
  · rintro ⟨w, hw, hwz⟩
    have hwz' := D.neutral.integralPointMap_injective hwz
    subst hwz'
    rw [← MonoidHom.mem_ker, Q.ker_reductiveReduction hQ.2.1]
    exact hw

/-- A zero-depth root point outside strict depth times the doubled-root group
forces its character to survive in the supplied reductive quotient. -/
theorem quotient_root_of_depth_boundary_of_rootFixerIntersections
    {x : C.Apartment} (hinter : HasRootFixerIntersections C {x} D)
    (T : IntegralTorusData D C.S C.i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)
    (a : relativeRoots C.i) (g : rationalPoints G)
    (hg : g ∈ C.apartment.filtration x a 0)
    (hout : g ∉ (C.apartment.filtrationPlus x a 0 : Set (rationalPoints G)) *
      (doubleRootGroupPoints C.i a.val : Set (rationalPoints G))) :
    T.characterSpecialization hT a.val ∈
      relativeRoots (T.specialFibreInclusion ≫ Q.projection) := by
  let : Smooth G.X.hom := C.isConnectedReductive.smooth
  let : Smooth D.neutral.group.X.hom := D.neutral_smooth
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  let : Mono C.i.hom.hom.left := mono_of_isMaximalSplitTorus C.isMaximalSplitTorus
  have hroot := relativeRootSystem (inertiaFixedField F) G C.isConnectedReductive
    C.S C.i C.isMaximalSplitTorus
  have hgroot := C.apartment.filtration_le_rootGroupPoints x a 0 hg
  have hgint : g ∈ D.neutral.integralPoints := by
    have hi : g ∈ C.apartment.rootFixer a {x} := by
      rw [C.apartment.rootFixer_singleton]
      exact hg
    rw [← hinter a] at hi
    exact hi.2
  obtain ⟨z, hz⟩ := hgint
  have hzroot : D.neutral.integralPointMap z ∈ rootGroupPoints C.i a.val := hz.symm ▸ hgroot
  by_contra habsent
  have hcompare := T.quotient_subgroup_eq_double_of_absent_root hT Q hQ hroot a.property habsent
  have hzred := T.quotient_reduction_mem_rootFunctor hT Q a.val a.2.1 z hzroot
  rw [hcompare] at hzred
  have h2a0 : 2 • a.val ≠ 0 :=
    C.isMaximalSplitTorus.1.1.nsmul_ne_zero a.2.1 (by decide)
  obtain ⟨y, hyroot, hyred⟩ :=
    T.exists_integral_root_quotient_lift_of_perfectResidue hT Q hQ
      (2 • a.val) h2a0 (Q.reductiveReduction z) hzred
  have hydouble : D.neutral.integralPointMap y ∈ doubleRootGroupPoints C.i a.val := by
    rw [← rootGroupPoints_double_eq_doubleRootGroupPoints C.i
      C.isMaximalSplitTorus.1.1 hroot a.property]
    exact hyroot
  have hyfirst : D.neutral.integralPointMap y ∈ rootGroupPoints C.i a.val :=
    RelativeRoot.double_subgroup_le C.i a.val _ hyroot
  have hdiffroot : D.neutral.integralPointMap (z * y⁻¹) ∈ rootGroupPoints C.i a.val := by
    rw [map_mul, map_inv]
    exact (rootGroupPoints C.i a.val).mul_mem hzroot
      ((rootGroupPoints C.i a.val).inv_mem hyfirst)
  have hdiffred : Q.reductiveReduction (z * y⁻¹) = 1 := by
    rw [map_mul, map_inv]
    change Q.reductiveReduction z *
      (rationalPoints.map Q.projection (D.neutral.reduction y))⁻¹ = 1
    rw [hyred, mul_inv_cancel]
  have hdiffplus := (singleton_reductiveReduction_eq_one_iff_of_rootFixerIntersections
    hinter T hT Q hQ a (z * y⁻¹) hdiffroot).mp hdiffred
  apply hout
  refine ⟨D.neutral.integralPointMap (z * y⁻¹), hdiffplus,
    D.neutral.integralPointMap y, hydouble, ?_⟩
  change D.neutral.integralPointMap (z * y⁻¹) * D.neutral.integralPointMap y = g
  rw [map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one, hz]

/-- Every ordinary affine root through the modeled point has an actual
quotient root with its exact canonically specialized derivative character. -/
theorem exists_quotient_root_of_incidentAffineRoot_of_rootFixerIntersections
    {x : C.Apartment} (hinter : HasRootFixerIntersections C {x} D)
    (T : IntegralTorusData D C.S C.i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)
    {ψ : C.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ C.affineRoots) (hx : ψ x = 0) :
    ∃ a : relativeRoots C.i, ψ.linear = rootForm C.i a ∧
      T.characterSpecialization hT a.val ∈
        relativeRoots (T.specialFibreInclusion ≫ Q.projection) := by
  obtain ⟨a, hlin, g, -, hg⟩ :=
    C.apartment.exists_rootDepthBoundary_of_affineRoot hψ
  have hboundary : C.apartment.IsRootDepthBoundary x a 0 g := by
    simpa only [hx] using (hg x).1
  exact ⟨a, hlin, quotient_root_of_depth_boundary_of_rootFixerIntersections
    hinter T hT Q hQ a g hboundary.1 hboundary.2⟩

end Langlands.BruhatTits.IntegralModels
