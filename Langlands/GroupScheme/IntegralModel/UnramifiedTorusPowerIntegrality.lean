import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.IntegralModel.SplitIntegralPoints
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Integrality of a point from a power, through an unramified split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.LocalGalois.Separable GaloisPointComparison

section Topology

/-- In a topological group, every element of a compact subgroup has a positive power in a
given open subgroup. -/
theorem exists_pow_mem_of_isCompact_of_isOpen {X : Type*} [Group X] [TopologicalSpace X]
    [IsTopologicalGroup X] {C H : Subgroup X} (hC : IsCompact (C : Set X))
    (hH : IsOpen (H : Set X)) {g : X} (hg : g ∈ C) :
    ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hopen : IsOpen ((H.subgroupOf C : Subgroup C) : Set C) :=
    hH.preimage continuous_subtype_val
  have : Finite (C ⧸ H.subgroupOf C) := Subgroup.quotient_finite_of_isOpen _ hopen
  have hindex : (H.subgroupOf C).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨n, hn, -, hgn⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hindex ⟨g, hg⟩
  exact ⟨n, hn, by simpa [Subgroup.mem_subgroupOf] using hgn⟩

end Topology

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {H : GroupScheme (Spec (CommRingCat.of K))}
  (N : IntegralModel R K H)

/-- The generic split-torus value respects powers of the coordinates. -/
theorem genericSplitTorusValue_pow {I : Type u} [Finite I]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ N.group) (t : I → Kˣ) (n : ℕ) :
    N.genericSplitTorusValue i (t ^ n) = N.genericSplitTorusValue i t ^ n := by
  have h (s : I → Kˣ) : N.genericSplitTorusValue i s =
      rationalPoints.map (N.genericSplitTorusHom i)
        ((splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of K))))).symm
          (MonoidHom.compLeft
            (Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom) I s)) := by
    rw [rationalPoints.map_apply]
    rfl
  rw [h, h, map_pow, map_pow, map_pow]

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F G)

/-- A unit of the maximal unramified field whose positive power is a unit of its
integers is itself a unit of its integers. -/
theorem exists_unit_of_pow {x : (inertiaFixedField F)ˣ} {n : ℕ} (hn : n ≠ 0)
    (h : ∃ s : (fixedFieldIntegers F)ˣ,
      Units.map (algebraMap (fixedFieldIntegers F) (inertiaFixedField F) :
        fixedFieldIntegers F →* inertiaFixedField F) s = x ^ n) :
    ∃ s : (fixedFieldIntegers F)ˣ,
      Units.map (algebraMap (fixedFieldIntegers F) (inertiaFixedField F) :
        fixedFieldIntegers F →* inertiaFixedField F) s = x := by
  obtain ⟨s, hs⟩ := h
  have hs' : ((s : fixedFieldIntegers F) : inertiaFixedField F) = (x : inertiaFixedField F) ^ n :=
    congrArg Units.val hs
  have hval_unit : fixedFieldValuation F ((s : fixedFieldIntegers F) : inertiaFixedField F) = 1 := by
    have h1 : fixedFieldValuation F ((s : fixedFieldIntegers F) : inertiaFixedField F) ≤ 1 :=
      (s : fixedFieldIntegers F).property
    have h2 : fixedFieldValuation F
        (((s⁻¹ : (fixedFieldIntegers F)ˣ) : fixedFieldIntegers F) : inertiaFixedField F) ≤ 1 :=
      ((s⁻¹ : (fixedFieldIntegers F)ˣ) : fixedFieldIntegers F).property
    have hmul : fixedFieldValuation F ((s : fixedFieldIntegers F) : inertiaFixedField F) *
        fixedFieldValuation F
          (((s⁻¹ : (fixedFieldIntegers F)ˣ) : fixedFieldIntegers F) : inertiaFixedField F) = 1 := by
      rw [← map_mul]
      have : ((s : fixedFieldIntegers F) : inertiaFixedField F) *
          (((s⁻¹ : (fixedFieldIntegers F)ˣ) : fixedFieldIntegers F) : inertiaFixedField F) = 1 := by
        exact congrArg Subtype.val s.mul_inv
      rw [this, map_one]
    by_contra hne
    have hlt : fixedFieldValuation F ((s : fixedFieldIntegers F) : inertiaFixedField F) < 1 :=
      lt_of_le_of_ne h1 hne
    have : fixedFieldValuation F ((s : fixedFieldIntegers F) : inertiaFixedField F) *
        fixedFieldValuation F
          (((s⁻¹ : (fixedFieldIntegers F)ˣ) : fixedFieldIntegers F) : inertiaFixedField F) < 1 :=
      mul_lt_one_of_lt_of_le hlt h2
    exact absurd hmul (ne_of_lt this)
  have hx : fixedFieldValuation F (x : inertiaFixedField F) = 1 := by
    rw [hs', map_pow] at hval_unit
    exact (pow_eq_one_iff_of_nonneg zero_le hn).mp hval_unit
  have hxinv : fixedFieldValuation F ((x⁻¹ : (inertiaFixedField F)ˣ) : inertiaFixedField F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  let a : fixedFieldIntegers F := ⟨(x : inertiaFixedField F), le_of_eq hx⟩
  let b : fixedFieldIntegers F := ⟨((x⁻¹ : (inertiaFixedField F)ˣ) : inertiaFixedField F),
    le_of_eq hxinv⟩
  refine ⟨⟨a, b, Subtype.ext (by simp [a, b]), Subtype.ext (by simp [a, b])⟩, ?_⟩
  ext
  rfl

/-- **Integrality from a power through an unramified split torus.** Let `i` be a closed split
torus of the base change of `M` to the maximal unramified integers. If the extension of a
rational point `g` is the generic value of `i` at some coordinates, and some positive power of
`g` is integral, then `g` is integral. -/
theorem mem_integralPoints_of_pow_mem_of_unramifiedSplitTorus {I : Type u} [Finite I]
    (i : splitTorus (Spec (CommRingCat.of (fixedFieldIntegers F))) I ⟶
      M.baseChangeUnramified.group)
    (hi : IsClosedSubgroup i) {g : rationalPoints G} {t : I → (inertiaFixedField F)ˣ}
    (hg : rationalExtend F (inertiaFixedField F) G g =
      M.baseChangeUnramified.genericSplitTorusValue i t)
    {n : ℕ} (hn : n ≠ 0) (hgn : g ^ n ∈ M.integralPoints) : g ∈ M.integralPoints := by
  have hext := (M.mem_integralPoints_rationalExtend_iff_unramified (g ^ n)).mpr hgn
  rw [map_pow, hg, ← genericSplitTorusValue_pow,
    M.baseChangeUnramified.genericSplitTorusValue_mem_integralPoints_iff i hi] at hext
  rw [← M.mem_integralPoints_rationalExtend_iff_unramified, hg,
    M.baseChangeUnramified.genericSplitTorusValue_mem_integralPoints_iff i hi]
  intro j
  exact exists_unit_of_pow hn (hext j)

end Langlands.GroupScheme.IntegralModel
