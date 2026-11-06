import Langlands.Geometry.Building.RootFunctionFieldEquivariance
import Langlands.Geometry.Building.RootFunctionNontriviality
import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.Geometry.Building.UnramifiedZeroTransport

/-! # Root-valuation axioms on actual field restriction -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : S.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "a_K" a => characterLattice.baseChange b S a

private theorem rationalExtend_injective [IsAffineHom G.X.hom] :
    Function.Injective (rationalExtend k K G) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro x y h
  apply (rationalCoeffEquiv k G).injective
  apply GaloisPoint.extend_injective k K G
  simpa only [baseChangeCoeffEquiv_rationalExtend] using
    congrArg (baseChangeCoeffEquiv k K G) h

namespace RootFunctionFamily

variable {i} [IsAffineHom G.X.hom] [Smooth G.X.hom]

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- Actual field restriction preserves the split-torus compatibility formula,
with the scalar function restricted on field units. -/
theorem fieldRestrict_isSplitTorusCompatible
    (hS : IsSplitTorus S.toGrp)
    {ω : Kˣ → ℝ} {ψ : RootFunctionFamily S_K G_K}
    (hψ : IsSplitTorusCompatible (S := S_K) i_K ω ψ) :
    IsSplitTorusCompatible i
      (fun t => ω (Units.map (algebraMap k K).toMonoidHom t))
      (fieldRestrict (k := k) (K := K) ψ) := by
  intro a ha s u hu
  have hroot : (a_K a) ∈ relativeRoots (T := S_K) i_K := by
    exact (mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha
  have hχ : (rationalCharacters.equivCharacterLattice S_K).symm (a_K a) =
      rationalCharacters.baseChange b
        ((rationalCharacters.equivCharacterLattice S).symm a) := rfl
  have heval :
      rationalCharacterEval ((rationalCharacters.equivCharacterLattice S_K).symm (a_K a))
          (rationalExtend k K S.toGrp s) =
        Units.map (algebraMap k K).toMonoidHom
          (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) s) := by
    rw [hχ]
    exact rationalCharacterEval_extend k K S.toGrp
      ((rationalCharacters.equivCharacterLattice S).symm a) s
  have h := hψ (a_K a) hroot (rationalExtend k K S.toGrp s)
    (rationalExtend k K G u) (rationalExtend_mem_rootGroupPoints (K := K) i a hu)
  simp only [fieldRestrict_apply]
  rw [map_mul, map_mul, map_inv, rationalExtend_map k K i s, ← heval]
  exact h

end RootFunctionFamily

section Normalizer

variable [Mono i.hom.hom.left]

private instance extendedMono : Mono (i_K).hom.hom.left := by
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change Mono ((Over.pullback b).map i.hom.hom).left
  infer_instance

/-- A reflection realized by an original normalizer point is realized by its
actual field extension, on the entire upstairs real cocharacter space. -/
theorem RealizesReflection.fieldExtend (hS : IsSplitTorus S.toGrp)
    {a : characterLattice S} {n : normalizerPoints i}
    (hn : RealizesReflection i a n) :
    RealizesReflection (S := S_K) i_K (a_K a)
      (normalizerPointsFieldExtend (K := K) i n) := by
  refine ⟨?_, ?_⟩
  · rw [← characterBaseChange_weylAction, hn.1, map_neg]
  · intro v hv
    obtain ⟨w, rfl⟩ := (splitCocharacterBaseChange (K := K) S hS).surjective v
    have hw : eval S a w = 0 := by
      simpa only [eval_splitCocharacterBaseChange] using hv
    change normalizerAction (T := S_K) i_K _ _ = _
    rw [← splitCocharacterBaseChange_normalizerAction]
    exact congrArg (splitCocharacterBaseChange (K := K) S hS) (hn.2 w hw)

variable [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp)

namespace IsRootDatumValuation

include hS

/-- Normalization away from roots descends along actual root-support comparison. -/
theorem fieldRestrict_eq_top_of_not_mem_roots
    {ψ : RootFunctionFamily S_K G_K}
    (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (a : characterLattice S) (ha : a ∉ relativeRoots i) (g : rationalPoints G) :
    RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ a g = ⊤ := by
  apply hψ.eq_top_of_not_mem_roots
  exact fun h => ha ((mem_roots_baseChange_iff (K := K) G S hS i a).mp h)

/-- Normalization off a root group descends by actual root-membership reflection. -/
theorem fieldRestrict_eq_top_of_not_mem
    {ψ : RootFunctionFamily S_K G_K}
    (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (a : characterLattice S) (ha : a ∈ relativeRoots i)
    (g : rationalPoints G) (hg : g ∉ rootGroupPoints i a) :
    RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ a g = ⊤ := by
  apply hψ.eq_top_of_not_mem _
    ((mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha)
  exact fun h => hg ((rationalExtend_mem_rootGroupPoints_iff i hS a ha.1 g).mp h)

/-- The exact identity criterion descends through the injective actual point map. -/
theorem fieldRestrict_eq_top_iff
    {ψ : RootFunctionFamily S_K G_K}
    (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (a : characterLattice S) (ha : a ∈ relativeRoots i)
    (g : rationalPoints G) (hg : g ∈ rootGroupPoints i a) :
    RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ a g = ⊤ ↔ g = 1 := by
  rw [RootFunctionFamily.fieldRestrict_apply,
    hψ.eq_top_iff _ ((mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha)
      _ (rationalExtend_mem_rootGroupPoints (K := K) i a hg)]
  constructor
  · intro h
    apply rationalExtend_injective (K := K) (G := G)
    simpa only [map_one] using h
  · rintro rfl
    exact map_one _

/-- The identity belongs to every restricted filtration. -/
theorem fieldRestrict_one_mem
    {ψ : RootFunctionFamily S_K G_K}
    (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (a : characterLattice S) (ha : a ∈ relativeRoots i) (r : ℝ) :
    (1 : rationalPoints G) ∈
      rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ) a r := by
  rw [rootFiltration_fieldRestrict i hS ψ a ha.1 r]
  change rationalExtend k K G 1 ∈ rootFiltration (S := S_K) i_K ψ (a_K a) r
  rw [map_one]
  exact hψ.one_mem _ ((mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha) r

/-- The literal filtration preimage retains multiplication. -/
theorem fieldRestrict_mul_mem
    {ψ : RootFunctionFamily S_K G_K}
    (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (a : characterLattice S) (ha : a ∈ relativeRoots i) (r : ℝ)
    (g h : rationalPoints G)
    (hg : g ∈ rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ) a r)
    (hh : h ∈ rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ) a r) :
    g * h ∈ rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ) a r := by
  rw [rootFiltration_fieldRestrict i hS ψ a ha.1 r] at hg hh ⊢
  change rationalExtend k K G (g * h) ∈ rootFiltration (S := S_K) i_K ψ (a_K a) r
  rw [map_mul]
  exact hψ.mul_mem _ ((mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha) r
    _ _ hg hh

/-- The literal filtration preimage retains inversion. -/
theorem fieldRestrict_inv_mem
    {ψ : RootFunctionFamily S_K G_K}
    (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (a : characterLattice S) (ha : a ∈ relativeRoots i) (r : ℝ)
    (g : rationalPoints G)
    (hg : g ∈ rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ) a r) :
    g⁻¹ ∈ rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ) a r := by
  rw [rootFiltration_fieldRestrict i hS ψ a ha.1 r] at hg ⊢
  change rationalExtend k K G g⁻¹ ∈ rootFiltration (S := S_K) i_K ψ (a_K a) r
  rw [map_inv]
  exact hψ.inv_mem _ ((mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha) r _ hg

/-- Reflection constants descend through the actual extended normalizer point. -/
theorem fieldRestrict_reflection
    {ψ : RootFunctionFamily S_K G_K}
    (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (a : characterLattice S) (ha : a ∈ relativeRoots i)
    (n : normalizerPoints i) (hn : RealizesReflection i a n) :
    ∃ c : ℝ, ∀ u ∈ rootGroupPoints i a, u ≠ 1 →
      RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ a u =
        RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ (-a)
          ((n : rationalPoints G) * u * (n : rationalPoints G)⁻¹) + (c : WithTop ℝ) := by
  obtain ⟨c, hc⟩ := hψ.reflection _
    ((mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha)
    (normalizerPointsFieldExtend (K := K) i n) (hn.fieldExtend i hS)
  refine ⟨c, fun u hu hu1 => ?_⟩
  have huK : rationalExtend k K G u ≠ 1 := by
    intro h
    apply hu1
    apply rationalExtend_injective (K := K) (G := G)
    simpa only [map_one] using h
  have h := hc (rationalExtend k K G u)
    (rationalExtend_mem_rootGroupPoints (K := K) i a hu) huK
  simpa only [RootFunctionFamily.fieldRestrict_apply, map_neg, map_mul, map_inv,
    normalizerPointsFieldExtend_coe] using h

/-- The double-root value identity descends on the actual double-root group. -/
theorem fieldRestrict_double
    {ψ : RootFunctionFamily S_K G_K}
    (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (a : characterLattice S) (ha : a ∈ relativeRoots i)
    (h2a : 2 • a ∈ relativeRoots i) (u : rationalPoints G)
    (hu : u ∈ rootGroupPoints i (2 • a)) :
    RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ (2 • a) u =
      2 • RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ a u := by
  have h2aK : 2 • (a_K a) ∈ relativeRoots (T := S_K) i_K := by
    simpa only [map_nsmul, relativeRoots] using
      (mem_roots_baseChange_iff (K := K) G S hS i (2 • a)).mpr h2a
  have huK : rationalExtend k K G u ∈ rootGroupPoints (S := S_K) i_K (2 • (a_K a)) := by
    simpa only [map_nsmul] using
      rationalExtend_mem_rootGroupPoints (K := K) i (2 • a) hu
  simpa only [RootFunctionFamily.fieldRestrict_apply, map_nsmul] using
    hψ.double _ ((mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha) h2aK
      (rationalExtend k K G u) huK

/-- The opposite-root normalizer identity descends using the original factors. -/
theorem fieldRestrict_opposite
    {ψ : RootFunctionFamily S_K G_K}
    (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (a : characterLattice S) (ha : a ∈ relativeRoots i)
    (u : rationalPoints G) (hu : u ∈ rootGroupPoints i a) (hu1 : u ≠ 1)
    (u' : rationalPoints G) (hu' : u' ∈ rootGroupPoints i (-a))
    (u'' : rationalPoints G) (hu'' : u'' ∈ rootGroupPoints i (-a))
    (hn : u' * u * u'' ∈ normalizerPoints i) :
    RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ (-a) u' +
      RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ a u = 0 := by
  have huK : rationalExtend k K G u ≠ 1 := by
    intro h
    apply hu1
    apply rationalExtend_injective (K := K) (G := G)
    simpa only [map_one] using h
  have hneg (v : rationalPoints G) (hv : v ∈ rootGroupPoints i (-a)) :
      rationalExtend k K G v ∈ rootGroupPoints (S := S_K) i_K (-(a_K a)) := by
    simpa only [map_neg] using rationalExtend_mem_rootGroupPoints (K := K) i (-a) hv
  have hnK : rationalExtend k K G u' * rationalExtend k K G u * rationalExtend k K G u'' ∈
      normalizerPoints (T := S_K) i_K := by
    simpa only [normalizerPointsFieldExtend_coe, map_mul] using
      (normalizerPointsFieldExtend (K := K) i ⟨u' * u * u'', hn⟩).property
  simpa only [RootFunctionFamily.fieldRestrict_apply, map_neg] using
    hψ.opposite _ ((mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha)
      (rationalExtend k K G u) (rationalExtend_mem_rootGroupPoints (K := K) i a hu) huK
      (rationalExtend k K G u') (hneg u' hu')
      (rationalExtend k K G u'') (hneg u'' hu'') hnK

/-- Restriction has infinitely many values on each original root group whenever
the upstairs additive unit character is nontrivial on original field units. -/
theorem fieldRestrict_image_infinite
    {ψ : RootFunctionFamily S_K G_K}
    (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (ω : Kˣ →* Multiplicative ℝ)
    (hcompat : IsSplitTorusCompatible (S := S_K) i_K (fun t => (ω t).toAdd) ψ)
    (hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ a ''
      (rootGroupPoints i a : Set (rationalPoints G))).Infinite := by
  let ωk := ω.comp (Units.map (algebraMap k K).toMonoidHom)
  have hc : IsSplitTorusCompatible i (fun t => (ωk t).toAdd)
      (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ) :=
    RootFunctionFamily.fieldRestrict_isSplitTorusCompatible hS hcompat
  exact hc.image_infinite ωk hS hω (fieldRestrict_eq_top_iff i hS hψ) ha

/-- V0 of actual restriction follows from compatibility and actual rational root
points; it is not a separately supplied restriction hypothesis. -/
theorem fieldRestrict_three_le_encard
    {ψ : RootFunctionFamily S_K G_K}
    (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (ω : Kˣ →* Multiplicative ℝ)
    (hcompat : IsSplitTorusCompatible (S := S_K) i_K (fun t => (ω t).toAdd) ψ)
    (hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    3 ≤ (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ a ''
      (rootGroupPoints i a : Set (rationalPoints G))).encard := by
  rw [(fieldRestrict_image_infinite i hS hψ ω hcompat hω ha).encard_eq]
  exact le_top

/-- Construct the valuation on the literal restricted family, retaining only
its exact V3 commutator condition as a separate descent premise. All other
normalization, V0--V5 and split-torus conditions are derived above. -/
def fieldRestrictValuationOfCommutator
    {ψ : RootFunctionFamily S_K G_K}
    (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (ω : Kˣ →* Multiplicative ℝ)
    (hcompat : IsSplitTorusCompatible (S := S_K) i_K (fun t => (ω t).toAdd) ψ)
    (hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0)
    (hcomm : ∀ a ∈ relativeRoots i, ∀ a' ∈ relativeRoots i,
      (∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] a' : Vstar S) ≠
        -(t • (1 : ℝ) ⊗ₜ[ℤ] a)) → ∀ r s : ℝ,
      ⁅Subgroup.closure (rootFiltration i
          (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ) a r),
        Subgroup.closure (rootFiltration i
          (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ) a' s)⁆ ≤
        Subgroup.closure (⋃ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
          (_ : p • a + q • a' ∈ relativeRoots i),
          rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ)
            (p • a + q • a') (p * r + q * s))) :
    {φ : RootFunctionFamily S G // IsRootDatumValuation i φ} :=
  ⟨RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ,
    { eq_top_of_not_mem_roots := fieldRestrict_eq_top_of_not_mem_roots i hS hψ
      eq_top_of_not_mem := fieldRestrict_eq_top_of_not_mem i hS hψ
      three_le_encard := fun _ ha => fieldRestrict_three_le_encard i hS hψ ω hcompat hω ha
      one_mem := fieldRestrict_one_mem i hS hψ
      mul_mem := fieldRestrict_mul_mem i hS hψ
      inv_mem := fieldRestrict_inv_mem i hS hψ
      eq_top_iff := fieldRestrict_eq_top_iff i hS hψ
      reflection := fieldRestrict_reflection i hS hψ
      commutator := hcomm
      double := fieldRestrict_double i hS hψ
      opposite := fieldRestrict_opposite i hS hψ }⟩

end IsRootDatumValuation

end Normalizer

end Langlands.Geometry.Building
