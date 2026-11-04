import Langlands.Geometry.Building.ChamberSharpStatement
import Langlands.GroupScheme.Rational.RootSubgroupMultipleInclusion

/-! # Root filtrations on facets and chambers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- A finite value of a root valuation varies as the affine functional
with that derivative and that value at the chosen point. -/
theorem val_eq_affineFunctional {a : relativeRoots i} {x : D.Apartment}
    {u : rationalPoints G} {t : ℝ} (ht : x.val a u = (t : WithTop ℝ))
    (y : D.Apartment) :
    y.val a u = ((D.affineFunctional a x t y : ℝ) : WithTop ℝ) := by
  obtain ⟨v, hv⟩ := D.equipollent_of_mem x.mem y.mem
  rw [affineFunctional_apply, vsub_eq_mk hv, rootForm_mk, hv,
    RootFunctionFamily.vadd_apply, ht, ← WithTop.coe_add, add_comm]

/-- Every finite root-valuation value is a jump of the corresponding
affine root filtration, hence gives an extended affine root. -/
theorem affineFunctional_mem_extendedAffineRoots {a : relativeRoots i}
    {x : D.Apartment} {u : rationalPoints G} {t : ℝ}
    (hu : u ∈ rootGroupPoints i a) (ht : x.val a u = (t : WithTop ℝ)) :
    D.affineFunctional a x t ∈ D.extendedAffineRoots := by
  refine ⟨a, rfl, ?_⟩
  intro heq
  have hmem : u ∈ D.affineRootGroup a (D.affineFunctional a x t) :=
    (mem_affineRootGroup_iff (affineFunctional_linear a x t) x).2
      ⟨hu, by simp [ht]⟩
  have hplus : u ∈ D.affineRootGroupPlus a (D.affineFunctional a x t) := by
    rw [heq]
    exact hmem
  have hlt := (mem_affineRootGroupPlus_iff (affineFunctional_linear a x t) x).1 hplus
  simpa [ht] using hlt.2

/-- A nonidentity root element determines an extended affine root whose
value at every apartment point is its finite root valuation. -/
theorem exists_extendedAffineRoot_of_ne_one (x : D.Apartment)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {u : rationalPoints G} (hu : u ∈ rootGroupPoints i a) (hu1 : u ≠ 1) :
    ∃ ψ ∈ D.extendedAffineRoots, ψ.linear = rootForm i ⟨a, ha⟩ ∧
      ∀ y : D.Apartment, y.val a u = ((ψ y : ℝ) : WithTop ℝ) := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1
    (mt (x.isValuation.eq_top_iff a ha u hu).1 hu1)
  exact ⟨D.affineFunctional ⟨a, ha⟩ x t,
    D.affineFunctional_mem_extendedAffineRoots hu ht.symm, rfl,
    fun y => D.val_eq_affineFunctional (a := ⟨a, ha⟩) (x := x) ht.symm y⟩

section AS4

variable
  (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
    ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)

include hAS4

/-- AS 4 makes the facet signs of every extended affine root constant. -/
theorem sign_eq_of_extendedAffineRoot {x y : D.Apartment}
    (hxy : AffineRootSystem.facetRel D.affineRoots x y)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.extendedAffineRoots) :
    SignType.sign (ψ x) = SignType.sign (ψ y) := by
  rcases hAS4 ψ hψ with h | h
  · exact hxy ψ h
  · have hs := hxy ((2 : ℝ) • ψ) h
    change SignType.sign ((2 : ℝ) * ψ x) = SignType.sign ((2 : ℝ) * ψ y) at hs
    simpa only [sign_mul, sign_pos (by norm_num : (0 : ℝ) < 2), one_mul] using hs

/-- Both depth-zero filtrations are constant on a facet. -/
theorem filtration_eq_of_facetRel {x y : D.Apartment}
    (hxy : AffineRootSystem.facetRel D.affineRoots x y)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    D.filtration x a 0 = D.filtration y a 0 ∧
      D.filtrationPlus x a 0 = D.filtrationPlus y a 0 := by
  have hmem (u : rationalPoints G) (hu : u ∈ rootGroupPoints i a) :
      ((0 : WithTop ℝ) ≤ x.val a u ↔ 0 ≤ y.val a u) ∧
        ((0 : WithTop ℝ) < x.val a u ↔ 0 < y.val a u) := by
    by_cases hu1 : u = 1
    · subst u
      rw [(x.isValuation.eq_top_iff a ha 1 hu).2 rfl,
        (y.isValuation.eq_top_iff a ha 1 hu).2 rfl]
      exact ⟨Iff.rfl, Iff.rfl⟩
    · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1
        (mt (x.isValuation.eq_top_iff a ha u hu).1 hu1)
      have hψ := D.affineFunctional_mem_extendedAffineRoots (a := ⟨a, ha⟩) hu ht.symm
      have hs := D.sign_eq_of_extendedAffineRoot hAS4 hxy hψ
      have hy := D.val_eq_affineFunctional (a := ⟨a, ha⟩) (x := x) ht.symm y
      have hx : D.affineFunctional ⟨a, ha⟩ x t x = t := by simp
      rw [hx] at hs
      rw [← ht, hy]
      constructor
      · rw [← WithTop.coe_zero, WithTop.coe_le_coe, WithTop.coe_le_coe,
          ← sign_nonneg_iff (a := t),
          ← sign_nonneg_iff (a := D.affineFunctional ⟨a, ha⟩ x t y), hs]
      · rw [← WithTop.coe_zero, WithTop.coe_lt_coe, WithTop.coe_lt_coe,
          ← sign_eq_one_iff, ← sign_eq_one_iff, hs]
  constructor
  · ext u
    simp only [mem_filtration]
    exact and_congr_right fun hu => (hmem u hu).1
  · ext u
    simp only [mem_filtrationPlus]
    exact and_congr_right fun hu => (hmem u hu).2

/-- The two point filtrations agree at any two points of one facet. -/
theorem filtration_eq_of_mem_isFacet {F : Set D.Apartment}
    (hF : AffineRootSystem.IsFacet D.affineRoots F)
    {x y : D.Apartment} (hx : x ∈ F) (hy : y ∈ F)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    D.filtration x a 0 = D.filtration y a 0 ∧
      D.filtrationPlus x a 0 = D.filtrationPlus y a 0 := by
  obtain ⟨z, rfl⟩ := hF
  exact D.filtration_eq_of_facetRel hAS4
    ((AffineRootSystem.facetRel_equivalence D.affineRoots).trans
      ((AffineRootSystem.facetRel_equivalence D.affineRoots).symm hx) hy) ha

/-- Intersecting either depth over a facet gives the filtration at any
one of its points (KP 6.3.20). -/
theorem rootFixer_eq_filtration_of_isFacet {F : Set D.Apartment}
    (hF : AffineRootSystem.IsFacet D.affineRoots F)
    {x : D.Apartment} (hx : x ∈ F)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    D.rootFixer a F = D.filtration x a 0 ∧
      D.rootFixerPlus a F = D.filtrationPlus x a 0 := by
  constructor
  · apply le_antisymm
    · exact fun _ hu => (D.mem_rootFixer.1 hu).2 x hx
    · intro u hu
      refine D.mem_rootFixer.2 ⟨filtration_le_rootGroupPoints x a 0 hu, fun y hy => ?_⟩
      rwa [← (D.filtration_eq_of_mem_isFacet hAS4 hF hx hy ha).1]
  · apply le_antisymm
    · exact fun _ hu => (D.mem_rootFixerPlus_iff_forall_mem.1 hu).2 x hx
    · intro u hu
      refine D.mem_rootFixerPlus_iff_forall_mem.2
        ⟨filtrationPlus_le_rootGroupPoints x a 0 hu, fun y hy => ?_⟩
      rwa [← (D.filtration_eq_of_mem_isFacet hAS4 hF hx hy ha).2]

/-- The published facet-constancy target follows from AS 4. -/
theorem rootFacetConstancyConclusion_of_isFacet {F : Set D.Apartment}
    (hF : AffineRootSystem.IsFacet D.affineRoots F) :
    D.RootFacetConstancyConclusion F := by
  intro a ha x hx
  exact D.rootFixer_eq_filtration_of_isFacet hAS4 hF hx ha

/-- Neither an affine root nor its positive half can vanish at a point
of a chamber. -/
theorem extendedAffineRoot_ne_zero_of_mem_chamber {C : Set D.Apartment}
    (hC : AffineRootSystem.IsChamber D.affineRoots C)
    {x : D.Apartment} (hx : x ∈ C)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.extendedAffineRoots) :
    ψ x ≠ 0 := by
  have hn (psi : D.Apartment →ᵃ[ℝ] ℝ) (hpsi : psi ∈ D.affineRoots) : psi x ≠ 0 := by
    rcases hC.mem_positiveRoots_or_mem_negativeRoots hpsi with hp | hm
    · exact ne_of_gt (hp.2 x hx)
    · exact ne_of_lt (hm.2 x hx)
  rcases hAS4 ψ hψ with h | h
  · exact hn ψ h
  · intro hzero
    exact hn ((2 : ℝ) • ψ) h (by
      change (2 : ℝ) * ψ x = 0
      rw [hzero, mul_zero])

/-- At an interior chamber point depth `0` equals depth `0+`
(the observation in the proof of KP 7.4.9). -/
theorem filtration_eq_filtrationPlus_of_mem_chamber {C : Set D.Apartment}
    (hC : AffineRootSystem.IsChamber D.affineRoots C)
    {x : D.Apartment} (hx : x ∈ C)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    D.filtration x a 0 = D.filtrationPlus x a 0 := by
  apply le_antisymm
  · intro u hu
    by_cases hu1 : u = 1
    · subst u
      exact (D.filtrationPlus x a 0).one_mem
    · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1
        (mt (x.isValuation.eq_top_iff a ha u hu.1).1 hu1)
      have hψ := D.affineFunctional_mem_extendedAffineRoots (a := ⟨a, ha⟩) hu.1 ht.symm
      have hn := D.extendedAffineRoot_ne_zero_of_mem_chamber hAS4 hC hx hψ
      have htne : t ≠ 0 := by simpa using hn
      have htge : (0 : ℝ) ≤ t := by
        simpa only [← ht, ← WithTop.coe_zero, WithTop.coe_le_coe] using hu.2
      refine mem_filtrationPlus.2 ⟨hu.1, ?_⟩
      rw [← ht, WithTop.coe_lt_coe]
      exact lt_of_le_of_ne htge htne.symm
  · exact filtrationPlus_le_filtration x a 0

/-- AS 4 also transfers the closed-side relation to extended affine roots. -/
theorem sign_eq_zero_or_eq_of_extendedAffineRoot {x y : D.Apartment}
    (hyx : y ∈ AffineRootSystem.facetClosure D.affineRoots x)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.extendedAffineRoots) :
    SignType.sign (ψ y) = 0 ∨ SignType.sign (ψ y) = SignType.sign (ψ x) := by
  rcases hAS4 ψ hψ with h | h
  · exact hyx ψ h
  · have hs := hyx ((2 : ℝ) • ψ) h
    change SignType.sign ((2 : ℝ) * ψ y) = 0 ∨
      SignType.sign ((2 : ℝ) * ψ y) = SignType.sign ((2 : ℝ) * ψ x) at hs
    simpa only [sign_mul, sign_pos (by norm_num : (0 : ℝ) < 2), one_mul] using hs

/-- At a point of a facet closure, positive depth only shrinks and
depth zero only grows (KP 6.3.21). -/
theorem filtration_comparison_of_mem_facetClosure {x y : D.Apartment}
    (hyx : y ∈ AffineRootSystem.facetClosure D.affineRoots x)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    D.filtrationPlus y a 0 ≤ D.filtrationPlus x a 0 ∧
      D.filtration x a 0 ≤ D.filtration y a 0 := by
  constructor
  · intro u hu
    by_cases hu1 : u = 1
    · subst u
      exact (D.filtrationPlus x a 0).one_mem
    · obtain ⟨ψ, hψ, _, hv⟩ :=
        D.exists_extendedAffineRoot_of_ne_one x ha (mem_filtrationPlus.1 hu).1 hu1
      have hypos : 0 < ψ y := by
        simpa only [hv y, WithTop.coe_lt_coe] using (mem_filtrationPlus.1 hu).2
      have hxpos : 0 < ψ x := by
        rcases D.sign_eq_zero_or_eq_of_extendedAffineRoot hAS4 hyx hψ with hz | hs
        · exact False.elim ((ne_of_gt hypos) (sign_eq_zero_iff.1 hz))
        · exact sign_eq_one_iff.1 (hs.symm.trans (sign_pos hypos))
      exact mem_filtrationPlus.2
        ⟨(mem_filtrationPlus.1 hu).1, by simpa only [hv x, WithTop.coe_lt_coe] using hxpos⟩
  · intro u hu
    by_cases hu1 : u = 1
    · subst u
      exact (D.filtration y a 0).one_mem
    · obtain ⟨ψ, hψ, _, hv⟩ :=
        D.exists_extendedAffineRoot_of_ne_one x ha hu.1 hu1
      have hxge : 0 ≤ ψ x := by
        simpa only [hv x, WithTop.coe_le_coe] using hu.2
      have hyge : 0 ≤ ψ y := by
        rcases D.sign_eq_zero_or_eq_of_extendedAffineRoot hAS4 hyx hψ with hz | hs
        · exact le_of_eq (sign_eq_zero_iff.1 hz).symm
        · rw [← sign_nonneg_iff, hs, sign_nonneg_iff]
          exact hxge
      exact mem_filtration.2 ⟨hu.1, by simpa only [hv y, WithTop.coe_le_coe] using hyge⟩

end AS4

/-- V4 and the actual doubled-root inclusion give the depth-zero inclusion. -/
theorem filtration_double_le (x : D.Apartment)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (h2a : 2 • a ∈ relativeRoots i) :
    D.filtration x (2 • a) 0 ≤ D.filtration x a 0 := by
  intro u hu
  refine ⟨RelativeRoot.double_subgroup_le i a (Over.mk (𝟙 _)) hu.1, ?_⟩
  have hd := hu.2
  rw [x.isValuation.double a ha h2a u hu.1, two_nsmul] at hd
  induction hv : x.val a u using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
    rw [hv, ← WithTop.coe_add, WithTop.coe_le_coe] at hd
    rw [WithTop.coe_le_coe]
    linarith

/-- The same V4 inclusion holds at depth `0+`. -/
theorem filtrationPlus_double_le (x : D.Apartment)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (h2a : 2 • a ∈ relativeRoots i) :
    D.filtrationPlus x (2 • a) 0 ≤ D.filtrationPlus x a 0 := by
  intro u hu
  rw [mem_filtrationPlus] at hu ⊢
  refine ⟨RelativeRoot.double_subgroup_le i a (Over.mk (𝟙 _)) hu.1, ?_⟩
  have hd := hu.2
  rw [x.isValuation.double a ha h2a u hu.1, two_nsmul] at hd
  induction hv : x.val a u using WithTop.recTopCoe with
  | top => exact WithTop.coe_lt_top 0
  | coe t =>
    rw [hv, ← WithTop.coe_add, WithTop.coe_lt_coe] at hd
    rw [WithTop.coe_lt_coe]
    linarith

/-- Doubled-root depth-zero fixers are contained in the original root fixers. -/
theorem rootFixer_double_le (F : Set D.Apartment)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (h2a : 2 • a ∈ relativeRoots i) :
    D.rootFixer (2 • a) F ≤ D.rootFixer a F := by
  intro u hu
  rw [mem_rootFixer] at hu ⊢
  exact ⟨RelativeRoot.double_subgroup_le i a (Over.mk (𝟙 _)) hu.1,
    fun x hx => D.filtration_double_le x ha h2a (hu.2 x hx)⟩

/-- Doubled-root positive-depth fixers are contained in the original ones. -/
theorem rootFixerPlus_double_le (F : Set D.Apartment)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (h2a : 2 • a ∈ relativeRoots i) :
    D.rootFixerPlus (2 • a) F ≤ D.rootFixerPlus a F := by
  intro u hu
  rw [mem_rootFixerPlus_iff_forall_mem] at hu ⊢
  exact ⟨RelativeRoot.double_subgroup_le i a (Over.mk (𝟙 _)) hu.1,
    fun x hx => D.filtrationPlus_double_le x ha h2a (hu.2 x hx)⟩

private theorem subgroup_mul_eq_left_of_le {M : Type*} [Group M]
    (H K : Subgroup M) (hKH : K ≤ H) :
    (H : Set M) * (K : Set M) = (H : Set M) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨h, hh, k, hk, rfl⟩
    exact H.mul_mem hh (hKH hk)
  · intro h hh
    exact ⟨h, hh, 1, K.one_mem, mul_one h⟩

/-- The doubled factor is retained in the block definition; V4 shows that
it does not enlarge the depth-zero or positive-depth chamber root group. -/
theorem chamberRootBlock_eq_rootGroup (x : D.Apartment) (strict : Bool)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    D.chamberRootBlock x strict a =
      (D.chamberRootGroup x strict a : Set (rationalPoints G)) := by
  classical
  cases strict with
  | false =>
    change (D.filtration x a 0 : Set (rationalPoints G)) *
      (D.doubleFiltration x a 0 : Set (rationalPoints G)) = _
    apply subgroup_mul_eq_left_of_le
    unfold doubleFiltration
    split_ifs with h2a
    · exact D.filtration_double_le x ha h2a
    · exact bot_le
  | true =>
    change (D.filtrationPlus x a 0 : Set (rationalPoints G)) *
      (↑(if 2 • a ∈ relativeRoots i then D.filtrationPlus x (2 • a) 0 else ⊥) :
        Set (rationalPoints G)) = _
    apply subgroup_mul_eq_left_of_le
    split_ifs with h2a
    · exact D.filtrationPlus_double_le x ha h2a
    · exact bot_le

/-- The doubled-root inclusion also collapses the two facet blocks,
even before any facet or chamber hypotheses are imposed. -/
theorem facetRootBlock_eq_rootGroup (F : Set D.Apartment) (strict : Bool)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    D.facetRootBlock F strict a =
      (D.facetRootGroup F strict a : Set (rationalPoints G)) := by
  classical
  unfold facetRootBlock
  apply subgroup_mul_eq_left_of_le
  split_ifs with h2a
  · cases strict with
    | false => exact D.rootFixer_double_le F ha h2a
    | true => exact D.rootFixerPlus_double_le F ha h2a
  · exact bot_le

/-- Any two points of a facet are related by the facet relation. -/
theorem facetRel_of_mem_isFacet {F : Set D.Apartment}
    (hF : AffineRootSystem.IsFacet D.affineRoots F)
    {x y : D.Apartment} (hx : x ∈ F) (hy : y ∈ F) :
    AffineRootSystem.facetRel D.affineRoots x y := by
  obtain ⟨z, rfl⟩ := hF
  exact (AffineRootSystem.facetRel_equivalence D.affineRoots).trans
    ((AffineRootSystem.facetRel_equivalence D.affineRoots).symm hx) hy

/-- The defining closed-side relation for a face holds relative to every
point of its ambient facet. -/
theorem mem_facetClosure_of_isFaceOf {F C : Set D.Apartment}
    (hFC : AffineRootSystem.IsFaceOf D.affineRoots F C)
    {x y : D.Apartment} (hx : x ∈ C) (hy : y ∈ F) :
    y ∈ AffineRootSystem.facetClosure D.affineRoots x := by
  obtain ⟨_, z, hz, hsub⟩ := hFC
  have hzx : AffineRootSystem.facetRel D.affineRoots z x := by
    rwa [← hz] at hx
  rw [← AffineRootSystem.facetClosure_eq_of_facetRel hzx]
  exact hsub hy

/-- The geometric sign predicate implies positivity of the pairing of a
positive wall's derivative, evaluated on the actual cocharacter. -/
theorem pairing_pos_of_affineRoot_positive {F C : Set D.Apartment}
    {ν : cocharacterLattice S} (hPos : D.FacetChamberPositiveSystem F C ν)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.affineRoots)
    (hF : ∀ y ∈ F, ψ y = 0) (hC : ∀ y ∈ C, 0 < ψ y)
    {a : relativeRoots i} {c : ℝ} (hlin : ψ.linear = c • rootForm i a) :
    0 < c * (latticePairing S a ν : ℝ) := by
  obtain ⟨b, hb, hp⟩ := hPos ψ hψ hF hC
  have heval := congrArg (fun l : TranslationSpace i →ₗ[ℝ] ℝ =>
    l (Submodule.Quotient.mk (TensorProduct.tmul ℤ (1 : ℝ) ν)))
      (hb.symm.trans hlin)
  simp only [LinearMap.smul_apply, rootForm_mk, eval_tmul, one_mul, smul_eq_mul] at heval
  have hpR : (0 : ℝ) < (latticePairing S b ν : ℝ) := by exact_mod_cast hp
  rwa [heval] at hpR

section FacetComparisons

variable
  (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
    ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)

include hAS4

/-- The weak facet/chamber comparisons at the two zero depths. -/
theorem rootFixer_comparison_of_isFaceOf {F C : Set D.Apartment}
    (hC : AffineRootSystem.IsChamber D.affineRoots C)
    (hFC : AffineRootSystem.IsFaceOf D.affineRoots F C)
    {x : D.Apartment} (hx : x ∈ C)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    D.rootFixerPlus a F ≤ D.rootFixerPlus a C ∧
      D.rootFixerPlus a C ≤ D.rootFixer a C ∧
      D.rootFixer a C ≤ D.rootFixer a F := by
  obtain ⟨y, hy⟩ : F.Nonempty := by
    obtain ⟨y, hy⟩ := hFC.1
    exact ⟨y, hy ▸ AffineRootSystem.mem_facet_self D.affineRoots y⟩
  obtain ⟨hF0, hFp⟩ := D.rootFixer_eq_filtration_of_isFacet hAS4 hFC.1 hy ha
  obtain ⟨hC0, hCp⟩ := D.rootFixer_eq_filtration_of_isFacet hAS4 hC.isFacet hx ha
  have hc := D.filtration_comparison_of_mem_facetClosure hAS4
    (D.mem_facetClosure_of_isFaceOf hFC hx hy) ha
  rw [hF0, hFp, hC0, hCp]
  exact ⟨hc.1, filtrationPlus_le_filtration x a 0, hc.2⟩

/-- A positive extended wall has positive derivative pairing under the
facet/chamber sign predicate. -/
theorem pairing_pos_of_extendedAffineRoot_positive {F C : Set D.Apartment}
    {ν : cocharacterLattice S} (hPos : D.FacetChamberPositiveSystem F C ν)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.extendedAffineRoots)
    (hF : ∀ y ∈ F, ψ y = 0) (hC : ∀ y ∈ C, 0 < ψ y)
    {a : relativeRoots i} (hlin : ψ.linear = rootForm i a) :
    0 < latticePairing S a ν := by
  have hpR : (0 : ℝ) < (latticePairing S a ν : ℝ) := by
    rcases hAS4 ψ hψ with h | h
    · have hp := D.pairing_pos_of_affineRoot_positive hPos h hF hC
        (a := a) (c := 1) (by simpa using hlin)
      simpa using hp
    · have hp := D.pairing_pos_of_affineRoot_positive hPos h
        (fun y hy => by change (2 : ℝ) * ψ y = 0; rw [hF y hy, mul_zero])
        (fun y hy => by change 0 < (2 : ℝ) * ψ y; exact mul_pos (by norm_num) (hC y hy))
        (a := a) (c := 2) (by rw [AffineMap.smul_linear, hlin])
      linarith
  exact_mod_cast hpR

/-- Negative extended walls give the opposite strict pairing, by the
negation symmetry of the actual affine root system. -/
theorem pairing_neg_of_extendedAffineRoot_negative
    (hSys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    {F C : Set D.Apartment} {ν : cocharacterLattice S}
    (hPos : D.FacetChamberPositiveSystem F C ν)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.extendedAffineRoots)
    (hF : ∀ y ∈ F, ψ y = 0) (hC : ∀ y ∈ C, ψ y < 0)
    {a : relativeRoots i} (hlin : ψ.linear = rootForm i a) :
    latticePairing S a ν < 0 := by
  have hpR : (latticePairing S a ν : ℝ) < 0 := by
    rcases hAS4 ψ hψ with h | h
    · have hp := D.pairing_pos_of_affineRoot_positive hPos (hSys.neg_mem h)
        (fun y hy => by change -ψ y = 0; rw [hF y hy, neg_zero])
        (fun y hy => by change 0 < -ψ y; exact neg_pos.2 (hC y hy))
        (a := a) (c := -1) (by
          rw [AffineMap.neg_linear, hlin]
          apply LinearMap.ext
          intro v
          change -(rootForm i a v) = (-1 : ℝ) * rootForm i a v
          ring)
      linarith
    · have hp := D.pairing_pos_of_affineRoot_positive hPos (hSys.neg_mem h)
        (fun y hy => by change -((2 : ℝ) * ψ y) = 0; rw [hF y hy, mul_zero, neg_zero])
        (fun y hy => by
          change 0 < -((2 : ℝ) * ψ y)
          exact neg_pos.2 (mul_neg_of_pos_of_neg (by norm_num) (hC y hy)))
        (a := a) (c := -2) (by
          rw [AffineMap.neg_linear, AffineMap.smul_linear, hlin]
          apply LinearMap.ext
          intro v
          change -((2 : ℝ) * rootForm i a v) = (-2 : ℝ) * rootForm i a v
          ring)
      linarith
  exact_mod_cast hpR

/-- Extended affine-root signs agree at every two points of a facet. -/
theorem sign_eq_of_mem_isFacet {F : Set D.Apartment}
    (hF : AffineRootSystem.IsFacet D.affineRoots F)
    {x y : D.Apartment} (hx : x ∈ F) (hy : y ∈ F)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.extendedAffineRoots) :
    SignType.sign (ψ x) = SignType.sign (ψ y) :=
  D.sign_eq_of_extendedAffineRoot hAS4 (D.facetRel_of_mem_isFacet hF hx hy) hψ

/-- For a positive relative root the nonstrict facet and chamber groups
coincide, under the actual geometric positive-system condition. -/
theorem rootFixer_eq_of_isFaceOf_of_pairing_pos
    (hSys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    {F C : Set D.Apartment} {ν : cocharacterLattice S}
    (hC : AffineRootSystem.IsChamber D.affineRoots C)
    (hFC : AffineRootSystem.IsFaceOf D.affineRoots F C)
    (hPos : D.FacetChamberPositiveSystem F C ν)
    {x : D.Apartment} (hx : x ∈ C)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (hapos : 0 < latticePairing S a ν) :
    D.rootFixer a F = D.rootFixer a C := by
  apply le_antisymm
  · obtain ⟨y, hy⟩ : F.Nonempty := by
      obtain ⟨y, hy⟩ := hFC.1
      exact ⟨y, hy ▸ AffineRootSystem.mem_facet_self D.affineRoots y⟩
    intro u hu
    by_cases hu1 : u = 1
    · subst u
      exact (D.rootFixer a C).one_mem
    · have huRoot := (D.mem_rootFixer.1 hu).1
      obtain ⟨ψ, hψ, hlin, hv⟩ :=
        D.exists_extendedAffineRoot_of_ne_one x ha huRoot hu1
      have hyge : 0 ≤ ψ y := by
        simpa only [hv y, WithTop.coe_le_coe] using ((D.mem_rootFixer.1 hu).2 y hy).2
      have hxge : 0 ≤ ψ x := by
        by_contra! hxneg
        have hyzero : ψ y = 0 := by
          rcases D.sign_eq_zero_or_eq_of_extendedAffineRoot hAS4
              (D.mem_facetClosure_of_isFaceOf hFC hx hy) hψ with hz | hs
          · exact sign_eq_zero_iff.1 hz
          · have hyneg := sign_eq_neg_one_iff.1 (hs.trans (sign_neg hxneg))
            exact False.elim (not_lt_of_ge hyge hyneg)
        have hzeroF : ∀ z ∈ F, ψ z = 0 := by
          intro z hz
          exact sign_eq_zero_iff.1
            ((D.sign_eq_of_mem_isFacet hAS4 hFC.1 hy hz hψ).symm.trans
              (sign_eq_zero_iff.2 hyzero))
        have hnegativeC : ∀ z ∈ C, ψ z < 0 := by
          intro z hz
          exact sign_eq_neg_one_iff.1
            ((D.sign_eq_of_mem_isFacet hAS4 hC.isFacet hx hz hψ).symm.trans
              (sign_neg hxneg))
        have haneg := D.pairing_neg_of_extendedAffineRoot_negative hAS4 hSys
          hPos hψ hzeroF hnegativeC hlin
        exact lt_asymm hapos haneg
      rw [(D.rootFixer_eq_filtration_of_isFacet hAS4 hC.isFacet hx ha).1]
      exact mem_filtration.2
        ⟨huRoot, by simpa only [hv x, WithTop.coe_le_coe] using hxge⟩
  · exact (D.rootFixer_comparison_of_isFaceOf hAS4 hC hFC hx ha).2.2

/-- For a negative root the strict facet group is the nonstrict chamber
group, with the source's prescribed `0+` versus `0` depths. -/
theorem rootFixerPlus_eq_of_isFaceOf_of_pairing_neg
    {F C : Set D.Apartment} {ν : cocharacterLattice S}
    (hC : AffineRootSystem.IsChamber D.affineRoots C)
    (hFC : AffineRootSystem.IsFaceOf D.affineRoots F C)
    (hPos : D.FacetChamberPositiveSystem F C ν)
    {x : D.Apartment} (hx : x ∈ C)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (haneg : latticePairing S a ν < 0) :
    D.rootFixerPlus a F = D.rootFixer a C := by
  apply le_antisymm
  · exact (D.rootFixer_comparison_of_isFaceOf hAS4 hC hFC hx ha).1.trans
      (D.rootFixerPlus_le_rootFixer a C)
  · obtain ⟨y, hy⟩ : F.Nonempty := by
      obtain ⟨y, hy⟩ := hFC.1
      exact ⟨y, hy ▸ AffineRootSystem.mem_facet_self D.affineRoots y⟩
    intro u hu
    by_cases hu1 : u = 1
    · subst u
      exact (D.rootFixerPlus a F).one_mem
    · have huRoot := (D.mem_rootFixer.1 hu).1
      obtain ⟨ψ, hψ, hlin, hv⟩ :=
        D.exists_extendedAffineRoot_of_ne_one x ha huRoot hu1
      have hxpos : 0 < ψ x := by
        have huPlus : u ∈ D.filtrationPlus x a 0 := by
          rw [← D.filtration_eq_filtrationPlus_of_mem_chamber hAS4 hC hx ha]
          exact (D.mem_rootFixer.1 hu).2 x hx
        simpa only [hv x, WithTop.coe_lt_coe] using (mem_filtrationPlus.1 huPlus).2
      have hypos : 0 < ψ y := by
        by_contra! hyle
        have hyzero : ψ y = 0 := by
          rcases D.sign_eq_zero_or_eq_of_extendedAffineRoot hAS4
              (D.mem_facetClosure_of_isFaceOf hFC hx hy) hψ with hz | hs
          · exact sign_eq_zero_iff.1 hz
          · have hyp := sign_eq_one_iff.1 (hs.trans (sign_pos hxpos))
            exact False.elim (not_lt_of_ge hyle hyp)
        have hzeroF : ∀ z ∈ F, ψ z = 0 := by
          intro z hz
          exact sign_eq_zero_iff.1
            ((D.sign_eq_of_mem_isFacet hAS4 hFC.1 hy hz hψ).symm.trans
              (sign_eq_zero_iff.2 hyzero))
        have hpositiveC : ∀ z ∈ C, 0 < ψ z := by
          intro z hz
          exact sign_eq_one_iff.1
            ((D.sign_eq_of_mem_isFacet hAS4 hC.isFacet hx hz hψ).symm.trans
              (sign_pos hxpos))
        have hapos := D.pairing_pos_of_extendedAffineRoot_positive hAS4
          hPos hψ hzeroF hpositiveC hlin
        exact lt_asymm hapos haneg
      rw [(D.rootFixer_eq_filtration_of_isFacet hAS4 hFC.1 hy ha).2]
      exact mem_filtrationPlus.2
        ⟨huRoot, by simpa only [hv y, WithTop.coe_lt_coe] using hypos⟩

end FacetComparisons

/-- The root-filtration portion of the published sharp chamber conclusion. -/
theorem chamberRootFiltrationConclusion
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {C : Set D.Apartment} (hC : AffineRootSystem.IsChamber D.affineRoots C)
    {x : D.Apartment} (hx : x ∈ C) :
    ∀ a ∈ relativeRoots i,
      D.rootFixer a C = D.filtration x a 0 ∧
      D.rootFixerPlus a C = D.filtrationPlus x a 0 ∧
      D.filtration x a 0 = D.filtrationPlus x a 0 ∧
      ∀ strict : Bool, D.chamberRootBlock x strict a =
        (D.chamberRootGroup x strict a : Set (rationalPoints G)) := by
  intro a ha
  obtain ⟨h0, hp⟩ := D.rootFixer_eq_filtration_of_isFacet hAS4 hC.isFacet hx ha
  exact ⟨h0, hp, D.filtration_eq_filtrationPlus_of_mem_chamber hAS4 hC hx ha,
    fun strict => D.chamberRootBlock_eq_rootGroup x strict ha⟩

/-- The root-filtration portion of the published sharp facet conclusion,
including its distinct negative and positive depths. -/
theorem chamberFacetRootFiltrationConclusion
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    (hSys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    {F C : Set D.Apartment} {ν : cocharacterLattice S}
    (hC : AffineRootSystem.IsChamber D.affineRoots C)
    (hFC : AffineRootSystem.IsFaceOf D.affineRoots F C)
    (hPos : D.FacetChamberPositiveSystem F C ν)
    {x : D.Apartment} (hx : x ∈ C) :
    D.RootFacetConstancyConclusion F ∧
      ∀ a ∈ relativeRoots i,
        D.rootFixerPlus a F ≤ D.rootFixerPlus a C ∧
        D.rootFixerPlus a C ≤ D.rootFixer a C ∧
        D.rootFixer a C ≤ D.rootFixer a F ∧
        (∀ strict : Bool, D.facetRootBlock F strict a =
          (D.facetRootGroup F strict a : Set (rationalPoints G))) ∧
        (0 < latticePairing S a ν → D.rootFixer a F = D.rootFixer a C) ∧
        (latticePairing S a ν < 0 → D.rootFixerPlus a F = D.rootFixer a C) := by
  refine ⟨D.rootFacetConstancyConclusion_of_isFacet hAS4 hFC.1, ?_⟩
  intro a ha
  obtain ⟨h1, h2, h3⟩ := D.rootFixer_comparison_of_isFaceOf hAS4 hC hFC hx ha
  exact ⟨h1, h2, h3, fun strict => D.facetRootBlock_eq_rootGroup F strict ha,
    fun hp => D.rootFixer_eq_of_isFaceOf_of_pairing_pos hAS4 hSys hC hFC hPos hx ha hp,
    fun hn => D.rootFixerPlus_eq_of_isFaceOf_of_pairing_neg hAS4 hC hFC hPos hx ha hn⟩

/-- The block-to-subgroup identification is an actual equivalence of
factor types, preserving the underlying rational point. -/
def chamberRootBlockEquiv (x : D.Apartment) (strict : Bool)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    D.chamberRootBlock x strict a ≃ D.chamberRootGroup x strict a :=
  Set.equivOfEq (D.chamberRootBlock_eq_rootGroup x strict ha)

/-- The facet block-to-subgroup equivalence, for either prescribed depth. -/
def facetRootBlockEquiv (F : Set D.Apartment) (strict : Bool)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    D.facetRootBlock F strict a ≃ D.facetRootGroup F strict a :=
  Set.equivOfEq (D.facetRootBlock_eq_rootGroup F strict ha)

@[simp] theorem chamberRootBlockEquiv_coe (x : D.Apartment) (strict : Bool)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (u : D.chamberRootBlock x strict a) :
    (D.chamberRootBlockEquiv x strict ha u : rationalPoints G) = u :=
  rfl

@[simp] theorem facetRootBlockEquiv_coe (F : Set D.Apartment) (strict : Bool)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (u : D.facetRootBlock F strict a) :
    (D.facetRootBlockEquiv F strict ha u : rationalPoints G) = u :=
  rfl

end Langlands.Geometry.Building.KPApartmentData
