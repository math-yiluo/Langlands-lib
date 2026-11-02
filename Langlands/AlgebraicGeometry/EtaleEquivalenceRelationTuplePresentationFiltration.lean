import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTuplePresentation
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleThresholdInvariance

/-! # Invariant threshold opens on finite tuple presentations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

/-- An open assembled on a scheme coproduct restricts to the prescribed open
on each component. -/
theorem sigma_ι_mem_iSup_image_iff {I : Type} (X : I → Scheme.{u})
    (V : ∀ i, (X i).Opens) (i : I) (x : X i) :
    Sigma.ι X i x ∈ (⨆ j, (Sigma.ι X j) ''ᵁ V j) ↔ x ∈ V i := by
  simp only [Opens.mem_iSup]
  constructor
  · rintro ⟨j, y, hy, heq⟩
    have hji : j = i := congrArg Sigma.fst ((sigmaι_eq_iff X j i y x).mp heq)
    subst j
    exact (Sigma.ι X i).isOpenEmbedding.injective heq ▸ hy
  · intro hx
    exact ⟨i, x, hx, rfl⟩

namespace EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R] [IsClosedImmersion (prod.lift E.t E.s)]

instance tupleChartObjectι_isOpenImmersion {I : Type} [Finite I]
    (length : I → ℕ) (i : I) : IsOpenImmersion (E.tupleChartObjectι length i) := by
  change IsOpenImmersion (Sigma.ι (fun i => E.tupleSymmetricScheme (length i)) i)
  infer_instance

instance tupleChartRelationι_isOpenImmersion {I : Type} [Finite I]
    (length : I → ℕ) (i j : I) : IsOpenImmersion (E.tupleChartRelationι length i j) := by
  change IsOpenImmersion (Sigma.ι (fun p : I × I =>
    E.tupleSymmetricCrossScheme (length p.1) (length p.2)) (i, j))
  infer_instance

/-- The invariant `k`th threshold on the total finite tuple presentation. -/
def tupleChartThresholdOpen {I : Type} [Finite I] (length : I → ℕ) (k : ℕ) :
    (E.tupleChartPresentation length).U.Opens :=
  ⨆ i, E.tupleChartObjectι length i ''ᵁ E.tupleSymmetricThresholdOpen (length i) k

@[simp]
theorem tupleChartObjectι_mem_threshold_iff {I : Type} [Finite I]
    (length : I → ℕ) (k : ℕ) (i : I) (x : E.tupleSymmetricScheme (length i)) :
    E.tupleChartObjectι length i x ∈ E.tupleChartThresholdOpen length k ↔
      x ∈ E.tupleSymmetricThresholdOpen (length i) k := by
  exact sigma_ι_mem_iSup_image_iff
    (fun i => E.tupleSymmetricScheme (length i))
    (fun i => E.tupleSymmetricThresholdOpen (length i) k) i x

theorem tupleChartObjectι_threshold_preimage {I : Type} [Finite I]
    (length : I → ℕ) (k : ℕ) (i : I) :
    E.tupleChartObjectι length i ⁻¹ᵁ E.tupleChartThresholdOpen length k =
      E.tupleSymmetricThresholdOpen (length i) k := by
  apply Opens.ext
  exact Set.ext (E.tupleChartObjectι_mem_threshold_iff length k i)

theorem tupleChartThresholdOpen_antitone {I : Type} [Finite I] (length : I → ℕ) :
    Antitone (E.tupleChartThresholdOpen length) := by
  intro k l h
  exact iSup_mono fun i =>
    (E.tupleChartObjectι length i).image_mono
      (E.tupleSymmetricThresholdOpen_antitone (length i) h)

theorem tupleChartThresholdOpen_isCompact {I : Type} [Finite I]
    (length : I → ℕ) (k : ℕ) :
    IsCompact (E.tupleChartThresholdOpen length k :
      Set (E.tupleChartPresentation length).U) := by
  rw [tupleChartThresholdOpen, Opens.coe_iSup]
  exact isCompact_iUnion fun i =>
    (E.tupleSymmetricThresholdOpen_isCompact (length i) k).image
      (E.tupleChartObjectι length i).continuous

/-- The two total endpoints have the same threshold inverse image. -/
theorem tupleChartThresholdOpen_preimage_eq {I : Type} [Finite I]
    (length : I → ℕ) (k : ℕ) :
    (E.tupleChartPresentation length).t ⁻¹ᵁ E.tupleChartThresholdOpen length k =
      (E.tupleChartPresentation length).s ⁻¹ᵁ E.tupleChartThresholdOpen length k := by
  apply Opens.ext
  apply Set.ext
  intro z
  obtain ⟨⟨⟨i, j⟩⟩, z, rfl⟩ :=
    Scheme.IsLocallyDirected.ι_jointly_surjective
      (Discrete.functor (fun p : I × I =>
        E.tupleSymmetricCrossScheme (length p.1) (length p.2))) z
  change (E.tupleChartRelationι length i j ≫ (E.tupleChartPresentation length).t) z ∈
      E.tupleChartThresholdOpen length k ↔
    (E.tupleChartRelationι length i j ≫ (E.tupleChartPresentation length).s) z ∈
      E.tupleChartThresholdOpen length k
  rw [E.tupleChartRelationι_t, E.tupleChartRelationι_s]
  simp only [Scheme.Hom.comp_apply, E.tupleChartObjectι_mem_threshold_iff]
  exact E.tupleSymmetricCross_threshold_iff (length i) (length j) k z

theorem tupleChartThresholdOpen_invariant {I : Type} [Finite I]
    (length : I → ℕ) (k : ℕ) :
    (E.tupleChartPresentation length).PointInvariant
      (E.tupleChartThresholdOpen length k) := by
  rintro x y ⟨z, rfl, rfl⟩ hx
  have h := congrArg (fun V => z ∈ V)
    (E.tupleChartThresholdOpen_preimage_eq length k)
  exact (eq_iff_iff.mp h).mpr hx

/-- On a family whose charts all have at least `k+1` entries, the `k`th
threshold is the entire object scheme. -/
theorem tupleChartThresholdOpen_eq_top {I : Type} [Finite I]
    (length : I → ℕ) (k : ℕ) (hk : ∀ i, k ≤ length i) :
    E.tupleChartThresholdOpen length k = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨⟨i⟩, z, rfl⟩ :=
    Scheme.IsLocallyDirected.ι_jointly_surjective
      (Discrete.functor (fun i => E.tupleSymmetricScheme (length i))) z
  apply (E.tupleChartObjectι_mem_threshold_iff length k i z).mpr
  have h := E.tupleSymmetricThresholdOpen_antitone (length i) (hk i)
  rw [E.tupleSymmetricThresholdOpen_self] at h
  exact h (Set.mem_univ z)

@[simp]
theorem tupleChartThresholdOpen_zero {I : Type} [Finite I] (length : I → ℕ) :
    E.tupleChartThresholdOpen length 0 = ⊤ :=
  E.tupleChartThresholdOpen_eq_top length 0 (fun _ => Nat.zero_le _)

/-- The filtration vanishes at the uniform bound, for any finite family. -/
theorem tupleChartThresholdOpen_eq_bot {I : Type} [Finite I]
    (length : I → ℕ) (k : ℕ) (hk : E.tupleLengthBound ≤ k) :
    E.tupleChartThresholdOpen length k = ⊥ := by
  simp [tupleChartThresholdOpen, E.tupleSymmetricThresholdOpen_eq_bot _ k hk]

theorem tupleTailThresholdOpen_eq_top (N p : ℕ) :
    E.tupleChartThresholdOpen
      (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) p = ⊤ :=
  E.tupleChartThresholdOpen_eq_top _ p (fun i => i.property)

end EtaleEquivalenceRelation
end Langlands.AlgebraicGeometry
