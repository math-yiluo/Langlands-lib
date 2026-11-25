import Langlands.Geometry.Building.RankOneCorootReduction
import Langlands.Geometry.Building.IntegerRankOneReflectionGeneration
import Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinatesStatement
import Langlands.Geometry.Building.KPLocalDoubleRootCommutatorStatement
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence

/-! # The doubled-input coroot estimate at an ordinary unitary root

For supplied `ValuedSU3RootCoordinates` at a multipliable root `b`, a commutator of
`u ∈ U_b(K)` and `u' ∈ U_{-b}(K)` with `u ∈ U_{2b}(K)` or `u' ∈ U_{-2b}(K)` has
`Z`-component in `Z(K)_{2r}`, where `r` is the depth sum at `b`. Together with the
divisibility facts for relative roots this reduces `KPLocalDoubleRootCommutatorStatement`
to `QuasiSplitValuedRankOneCoordinatesStatement`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.LocalField Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : MaximalUnramified.BuildingData F H) (hZ : IsTorus B.centralizer.Z)

/-- The conclusion of `KPLocalDoubleRootCommutatorStatement` at one specified character
`a`: for nontrivial `u ∈ U_a(K)`, `u' ∈ U_{-a}(K)` with `u ∈ U_{2a}(K)` or
`u' ∈ U_{-2a}(K)` and positive depth sum `r`, every `Z`-component of `u'⁻¹ u u' u⁻¹`
lies in `Z(K)_{2r}`. -/
def DoubledInputCommutatorProperty (a : characterLattice B.S) : Prop :=
  ∀ (x : B.Apartment) (u u' : rationalPoints H),
    u ∈ B.rootGroup a → u ≠ 1 → u' ∈ B.rootGroup (-a) → u' ≠ 1 →
    (u ∈ B.doubleRootGroup a ∨ u' ∈ B.doubleRootGroup (-a)) →
    ∀ r : ℝ≥0, 0 < r → (((r : ℝ) : WithTop ℝ) = x.val a u + x.val (-a) u') →
    ∀ (v' v : rationalPoints H) (z : rationalPoints B.centralizer.Z),
      v' ∈ B.rootGroup (-a) → v ∈ B.rootGroup a →
      u'⁻¹ * u * u' * u⁻¹ = v' * rationalPoints.map B.centralizer.j z * v →
      z ∈ B.centralizerTorusFiltration hZ (2 * r)

variable {B hZ}

/-- A point of `U_{2a}(K)`, with KP's convention `U_{2a}(K) = {1}` when `2a` is not a
root, lies in the root group of the character `2 • a`. -/
theorem mem_rootGroup_two_smul_of_mem_doubleRootGroup {a : characterLattice B.S}
    {g : rationalPoints H} (hg : g ∈ B.doubleRootGroup a) : g ∈ B.rootGroup (2 • a) := by
  change g ∈ doubleRootGroupPoints B.i a at hg
  unfold doubleRootGroupPoints at hg
  split_ifs at hg with h
  · exact hg
  · rw [Subgroup.mem_bot] at hg
    rw [hg]
    exact one_mem _

/-- A nontrivial point of `U_{2a}(K)` forces `2 • a` to be a relative root. -/
theorem two_smul_mem_relativeRoots_of_mem_doubleRootGroup {a : characterLattice B.S}
    {g : rationalPoints H} (hg : g ∈ B.doubleRootGroup a) (hg1 : g ≠ 1) :
    2 • a ∈ relativeRoots B.i := by
  by_contra h
  change g ∈ doubleRootGroupPoints B.i a at hg
  unfold doubleRootGroupPoints at hg
  split_ifs at hg with h2
  · exact h h2
  · rw [Subgroup.mem_bot] at hg
    exact hg1 hg

/-- A relative root whose double is a relative root is indivisible. -/
theorem mem_indivisibleRoots_of_two_smul_mem (a : relativeRoots B.i)
    (h2 : 2 • a.val ∈ relativeRoots B.i) : a.val ∈ RelativeRoot.indivisibleRoots B.i := by
  let : Smooth H.X.hom := B.isConnectedReductive.smooth
  have hS : IsSplitTorus B.S.toGrp := B.isMaximalSplitTorus.isSplitSubtorus.1
  refine ⟨a.property, fun c _ m hm hmc => ?_⟩
  have hmem : (2 * m) • c ∈ relativeRoots B.i := by
    rwa [mul_nsmul' c 2 m, hmc]
  rcases B.hasOppositeFactorPairs.eq_one_or_two_of_nsmul_mem B.i hS hmem with h | h <;> omega

/-- If `2 • (-a)` is a relative root, so is `2 • a`. -/
theorem two_smul_mem_relativeRoots_of_two_smul_neg_mem {a : characterLattice B.S}
    (h : 2 • (-a) ∈ relativeRoots B.i) : 2 • a ∈ relativeRoots B.i := by
  have hneg := B.neg_mem_relativeRoots_of_hasOppositeFactorPairs B.hasOppositeFactorPairs
    ⟨2 • (-a), h⟩
  simpa only [smul_neg, neg_neg] using hneg

/-- Halving both summands of a finite extended-real sum. -/
theorem add_eq_two_mul_of_halfTop_add_halfTop_eq {s t : WithTop ℝ} {r : ℝ}
    (h : SU3Root.halfTop s + SU3Root.halfTop t = (r : WithTop ℝ)) :
    s + t = ((2 * r : ℝ) : WithTop ℝ) := by
  cases s using WithTop.recTopCoe with
  | top => simp only [SU3Root.halfTop_top, top_add, WithTop.top_ne_coe] at h
  | coe s =>
    cases t using WithTop.recTopCoe with
    | top => simp only [SU3Root.halfTop_top, add_top, WithTop.top_ne_coe] at h
    | coe t =>
      rw [SU3Root.halfTop_coe, SU3Root.halfTop_coe, ← WithTop.coe_add] at h
      have h' : s / 2 + t / 2 = r := WithTop.coe_injective h
      rw [← WithTop.coe_add]
      congr 1
      linarith

namespace ValuedSU3RootCoordinates

variable {b : characterLattice B.S} (C : ValuedSU3RootCoordinates B hZ b)

/-- At an ordinary unitary root, if one input lies in the doubled root group, any
centralizer component is the coroot point of a unit whose normalized deviation from one is
exactly twice the depth sum. -/
theorem exists_corootPoint_of_doubledInput_factorization (hb : b ≠ 0)
    (x : B.Apartment) (u u' : rationalPoints H)
    (hu : u ∈ B.rootGroup b) (hu' : u' ∈ B.rootGroup (-b))
    (hdouble : u ∈ B.doubleRootGroup b ∨ u' ∈ B.doubleRootGroup (-b))
    (r : ℝ) (hr : 0 < r)
    (hdepth : x.val b u + x.val (-b) u' = (r : WithTop ℝ))
    (v' v : rationalPoints H) (z : rationalPoints B.centralizer.Z)
    (hv' : v' ∈ B.rootGroup (-b)) (hv : v ∈ B.rootGroup b)
    (hfactor : u'⁻¹ * u * u' * u⁻¹ =
      v' * rationalPoints.map B.centralizer.j z * v) :
    ∃ t : C.extensionˣ, C.corootPoint t = z ∧
      Langlands.FieldTheory.henselianSeparableAddValuation (MaximalUnramified.valuation F)
        (MaximalUnramified.valuationSubring_isHenselian F) C.extension ((t : C.extension) - 1) =
          ((2 * r : ℝ) : WithTop ℝ) := by
  obtain ⟨p, hp⟩ := C.positive.equiv.surjective ⟨u, hu⟩
  obtain ⟨q, hq⟩ := C.negative.equiv.surjective ⟨u', hu'⟩
  have hp' : (C.positive.equiv p : rationalPoints H) = u := congrArg Subtype.val hp
  have hq' : (C.negative.equiv q : rationalPoints H) = u' := congrArg Subtype.val hq
  have hcentral : p.first = 0 ∨ q.first = 0 := by
    rcases hdouble with hd | hd
    · obtain ⟨p₀, hp₀c, hp₀⟩ := (C.positive.double u).mp
        (mem_rootGroup_two_smul_of_mem_doubleRootGroup hd)
      obtain rfl : p₀ = p :=
        C.positive.equiv.injective (Subtype.ext (hp₀.trans hp'.symm))
      exact Or.inl hp₀c
    · obtain ⟨q₀, hq₀c, hq₀⟩ := (C.negative.double u').mp
        (mem_rootGroup_two_smul_of_mem_doubleRootGroup hd)
      obtain rfl : q₀ = q :=
        C.negative.equiv.injective (Subtype.ext (hq₀.trans hq'.symm))
      exact Or.inr hq₀c
  let omega := Langlands.FieldTheory.henselianSeparableAddValuation
    (MaximalUnramified.valuation F) (MaximalUnramified.valuationSubring_isHenselian F)
      C.extension
  have hvalue : SU3Root.Parameters.depthA omega p + SU3Root.Parameters.depthA omega q =
      (r : WithTop ℝ) := by
    change SU3Root.towerDepth (UnramifiedClosure F) C.base C.extension
      (MaximalUnramified.valuation F) (MaximalUnramified.valuationSubring_isHenselian F) p +
      SU3Root.towerDepth (UnramifiedClosure F) C.base C.extension
        (MaximalUnramified.valuation F) (MaximalUnramified.valuationSubring_isHenselian F) q = _
    rw [← C.depth_positive p, ← C.depth_negative q, hp', hq']
    exact (KPApartmentData.opposite_value_sum_eq B.i B.apartment C.origin x b u u').trans
      hdepth
  have hsecond : omega p.second + omega q.second = ((2 * r : ℝ) : WithTop ℝ) :=
    add_eq_two_mul_of_halfTop_add_halfTop_eq hvalue
  have hdeviation :
      omega (SU3Root.oppositeProductPivot p q - 1) = ((2 * r : ℝ) : WithTop ℝ) := by
    rw [SU3Root.oppositeProductPivot_sub_one_of_double p q hcentral, omega.map_mul]
    exact hsecond
  have ht : SU3Root.oppositeProductPivot p q ≠ 0 := by
    intro hzero
    rw [hzero, zero_sub, omega.map_neg, omega.map_one] at hdeviation
    have he : (0 : ℝ) = 2 * r := WithTop.coe_injective hdeviation
    linarith
  let t := Units.mk0 (SU3Root.oppositeProductPivot p q) ht
  refine ⟨t, ?_, hdeviation⟩
  apply (centralizerComponent_eq_of_root_factorizations B.i
    B.isMaximalSplitTorus.1.1 B.centralizer hb
    (C.negative.equiv _).property (C.positive.equiv _).property hv' hv)
  exact (C.commutator_factorization p q ht).symm.trans
    (by simpa only [hp', hq'] using hfactor)

include C in
/-- Supplied unitary coordinates at a nonzero character give the doubled-input estimate
there: the `Z`-component lies in `Z(K)_{2r}`. -/
theorem doubledInputCommutatorProperty (hb : b ≠ 0) :
    DoubledInputCommutatorProperty B hZ b := by
  intro x u u' hu _hu1 hu' _hu1' hdouble r hr hdepth v' v z hv' hv hfactor
  obtain ⟨t, htz, ht⟩ := C.exists_corootPoint_of_doubledInput_factorization hb x u u'
    hu hu' hdouble (r : ℝ) (by exact_mod_cast hr) hdepth.symm v' v z hv' hv hfactor
  have : Module.Free (UnramifiedClosure F) C.extension := Module.Free.of_divisionRing _ _
  let T := WeilGm.commGroupScheme (CommRingCat.of (UnramifiedClosure F)) C.extension
  have : IsAffine T.X.left := by
    change IsAffine (Spec _)
    infer_instance
  have hT : IsTorus T.toGrp :=
    WeilGm.isTorus_of_finite_separable (UnramifiedClosure F) C.extension
  have hind : IsInducedTorus T :=
    WeilGm.isInducedTorus_of_finite_separable (UnramifiedClosure F) C.extension
  have h2r : 0 < 2 * r := mul_pos two_pos hr
  let c : rationalPoints T.toGrp :=
    (WeilGm.rationalUnitsEquiv (UnramifiedClosure F) C.extension).symm t
  have hbound : (((2 * r : ℝ≥0) : ℝ) : WithTop ℝ) ≤
      Langlands.FieldTheory.henselianSeparableAddValuation (MaximalUnramified.valuation F)
        (MaximalUnramified.valuationSubring_isHenselian F) C.extension ((t : C.extension) - 1) := by
    rw [ht, NNReal.coe_mul, NNReal.coe_two]
  have hc : c ∈ localTorusFiltration F T hT (2 * r) := by
    rw [mem_localTorusFiltration_of_induced F T hT hind h2r c]
    intro χ
    exact MaximalUnramified.weilGm_geometricCharacter_bound F C.extension
      (MaximalUnramified.valuationSubring_isHenselian F) h2r t hbound χ
  have hmap := map_localTorusFiltration_le F T hT hZ C.corootMorphism (2 * r)
    (Subgroup.mem_map_of_mem _ hc)
  have hcz : rationalPoints.map (CommGroupScheme.groupHom C.corootMorphism) c = z := htz
  rw [← hcz]
  exact hmap

end ValuedSU3RootCoordinates

/-- Supplied coherent unitary coordinates at every indivisible multipliable root give the
doubled-input estimate at every actual relative root. -/
theorem doubledInputCommutatorProperty_of_valuedSU3RootCoordinates
    (hcoords : ∀ b : characterLattice B.S, b ∈ RelativeRoot.indivisibleRoots B.i →
      2 • b ∈ relativeRoots B.i → Nonempty (ValuedSU3RootCoordinates B hZ b))
    (a : relativeRoots B.i) : DoubledInputCommutatorProperty B hZ a.val := by
  intro x u u' hu hu1 hu' hu1' hdouble r hr hdepth v' v z hv' hv hfactor
  have h2a : 2 • a.val ∈ relativeRoots B.i := by
    rcases hdouble with hd | hd
    · exact two_smul_mem_relativeRoots_of_mem_doubleRootGroup hd hu1
    · exact two_smul_mem_relativeRoots_of_two_smul_neg_mem
        (two_smul_mem_relativeRoots_of_mem_doubleRootGroup hd hu1')
  obtain ⟨C⟩ := hcoords a.val (mem_indivisibleRoots_of_two_smul_mem a h2a) h2a
  exact C.doubledInputCommutatorProperty a.property.1 x u u' hu hu1 hu' hu1' hdouble r hr
    hdepth v' v z hv' hv hfactor

/-- The existence of coherent valued rank-one coordinates implies the doubled-root
commutator estimate over `K = F^ur`. -/
theorem kpLocalDoubleRootCommutator_of_valuedRankOneCoordinates
    (h : QuasiSplitValuedRankOneCoordinatesStatement.{u}) :
    KPLocalDoubleRootCommutatorStatement.{u} := by
  intro F _ _ _ _ H _ B hZ x a
  exact doubledInputCommutatorProperty_of_valuedSU3RootCoordinates
    (fun b hb h2b => (h F H B hZ b hb).2 h2b) a x

end Langlands.Geometry.Building
