import Langlands.Global.ArthurTruncationL2Criterion
import Langlands.Global.LeftCosetImageMajorant
import Langlands.Global.LeftCosetUnfoldingBound

/-! # Transferring the projection criterion to a left coset space

For a locally compact group `H` and a subgroup `Γ`, an operator `Λ` on functions on `H` induces
the operator `f ↦ (q ↦ Λ (f ∘ mk) q.out)` on functions on `Γ \ H`. Its orthogonal projection
extension follows from the corresponding statements for left `Γ`-invariant functions on `H`:
preservation of measurable invariant functions bounded on compact sets, idempotence, and the
pairing with continuous invariant functions compactly supported modulo `Γ`, written as integrals
over `Γ \ H` evaluated at the chosen representatives `y.out`. -/

noncomputable section

open MeasureTheory Set Filter Topology ComplexConjugate

namespace Langlands.Global

namespace LeftCosetSpace

section Topology

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  (Γ : Subgroup H)

/-- Every compact subset of `Γ \ H` is covered by the image of a compact subset of `H`. -/
theorem exists_isCompact_image_superset {C : Set (LeftCosetSpace Γ)} (hC : IsCompact C) :
    ∃ K : Set H, IsCompact K ∧ C ⊆ mk Γ '' K := by
  classical
  choose K hKc hKn using fun x : H => exists_compact_mem_nhds x
  have hcover : C ⊆ ⋃ x : H, mk Γ '' interior (K x) := by
    intro c _
    obtain ⟨x, rfl⟩ := mk_surjective Γ c
    exact Set.mem_iUnion.mpr ⟨x, x, mem_interior_iff_mem_nhds.mpr (hKn x), rfl⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : H => mk Γ '' interior (K x))
    (fun _ => (isOpenQuotientMap_mk Γ).isOpenMap _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ t, K x, t.finite_toSet.isCompact_biUnion (fun x _ => hKc x), ?_⟩
  intro c hc
  obtain ⟨y, hyt, z, hz, hzc⟩ := Set.mem_iUnion₂.mp (ht hc)
  exact ⟨z, Set.mem_iUnion₂.mpr ⟨y, hyt, interior_subset hz⟩, hzc⟩

/-- A left `Γ`-invariant function bounded on compact subsets of `H` gives, at the chosen
representatives, a function bounded on compact subsets of `Γ \ H`. -/
theorem bounded_out_of_invariant {φ : H → ℂ}
    (hb : ∀ C : Set H, IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖φ x‖ ≤ M)
    (hφ : ∀ g ∈ Γ, ∀ x, φ (g * x) = φ x) :
    ∀ C : Set (LeftCosetSpace Γ), IsCompact C → ∃ M : ℝ, ∀ q ∈ C, ‖φ q.out‖ ≤ M := by
  intro C hC
  obtain ⟨K, hK, hCK⟩ := exists_isCompact_image_superset Γ hC
  obtain ⟨M, hM⟩ := hb K hK
  refine ⟨M, fun q hq => ?_⟩
  obtain ⟨k, hk, rfl⟩ := hCK hq
  rw [apply_out_mk Γ hφ]
  exact hM k hk

omit [IsTopologicalGroup H] [LocallyCompactSpace H] in
/-- A function on `Γ \ H` bounded on compact sets pulls back to a function on `H` bounded on
compact sets. -/
theorem bounded_comp_mk {f : LeftCosetSpace Γ → ℂ}
    (hb : ∀ C : Set (LeftCosetSpace Γ), IsCompact C → ∃ M : ℝ, ∀ q ∈ C, ‖f q‖ ≤ M) :
    ∀ C : Set H, IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖f (mk Γ x)‖ ≤ M := by
  intro C hC
  obtain ⟨M, hM⟩ := hb _ (hC.image (continuous_mk Γ))
  exact ⟨M, fun x hx => hM _ ⟨x, hx, rfl⟩⟩

/-- A compactly supported function on `Γ \ H` pulls back to a function supported on the
`Γ`-saturation of a compact subset of `H`. -/
theorem exists_compact_support_comp_mk {E : Type*} [Zero E] {ψ : LeftCosetSpace Γ → E}
    (hψ : HasCompactSupport ψ) :
    ∃ Cs : Set H, IsCompact Cs ∧ ∀ x, ψ (mk Γ x) ≠ 0 → ∃ g ∈ Γ, g * x ∈ Cs := by
  obtain ⟨K, hK, hsub⟩ := exists_isCompact_image_superset Γ hψ
  refine ⟨K, hK, fun x hx => ?_⟩
  obtain ⟨k, hk, hkx⟩ := hsub (subset_tsupport ψ hx)
  have hmem : k * x⁻¹ ∈ Γ := (mk_eq_mk_iff Γ x k).mp hkx.symm
  exact ⟨k * x⁻¹, hmem, by rwa [inv_mul_cancel_right]⟩

end Topology

section Measurable

variable {H : Type*} [Group H] [MeasurableSpace H] (Γ : Subgroup H)

/-- A measurable left `Γ`-invariant complex-valued function gives a measurable function on
`Γ \ H` at the chosen representatives. -/
theorem measurable_out_of_invariant_complex {φ : H → ℂ} (hm : Measurable φ)
    (hφ : ∀ g ∈ Γ, ∀ x, φ (g * x) = φ x) :
    Measurable (fun q : LeftCosetSpace Γ => φ q.out) := by
  refine measurable_from_quotient.mpr ?_
  convert hm using 1
  funext x
  exact apply_out_mk Γ hφ x

end Measurable

end LeftCosetSpace

namespace ArthurTruncation

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [MeasurableSpace H] (Γ : Subgroup H)
  [BorelSpace (LeftCosetSpace Γ)] [T2Space (LeftCosetSpace Γ)]
  [SecondCountableTopology (LeftCosetSpace Γ)]

/-- **Transfer to `Γ \ H`.** Let `Λ` preserve measurable left `Γ`-invariant functions bounded on
compact sets, be idempotent on them, and satisfy the pairing identity against continuous
left `Γ`-invariant functions compactly supported modulo `Γ`, where the integrals over `Γ \ H` are
evaluated at the chosen representatives. Then the induced operator on `Γ \ H` has an orthogonal
projection extension on `L²(Γ \ H, μ)`. -/
theorem isOrthogonalL2Extension_leftCosetSpace (μ : Measure (LeftCosetSpace Γ)) [μ.Regular]
    (Λ : (H → ℂ) → H → ℂ)
    (hB : ∀ φ : H → ℂ, Measurable φ → (∀ C : Set H, IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖φ x‖ ≤ M) →
      (∀ g ∈ Γ, ∀ x, φ (g * x) = φ x) →
      Measurable (Λ φ) ∧ (∀ C : Set H, IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖Λ φ x‖ ≤ M) ∧
        ∀ g ∈ Γ, ∀ x, Λ φ (g * x) = Λ φ x)
    (hI : ∀ φ : H → ℂ, Measurable φ →
      (∀ C : Set H, IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖φ x‖ ≤ M) →
      (∀ g ∈ Γ, ∀ x, φ (g * x) = φ x) → Λ (Λ φ) = Λ φ)
    (hP : ∀ φ₁ φ₂ : H → ℂ, Measurable φ₁ →
      (∀ C : Set H, IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖φ₁ x‖ ≤ M) →
      (∀ g ∈ Γ, ∀ x, φ₁ (g * x) = φ₁ x) → Continuous φ₂ →
      (∀ g ∈ Γ, ∀ x, φ₂ (g * x) = φ₂ x) →
      (∃ Cs : Set H, IsCompact Cs ∧ ∀ x, φ₂ x ≠ 0 → ∃ g ∈ Γ, g * x ∈ Cs) →
      Integrable (fun y : LeftCosetSpace Γ => φ₁ y.out * conj (Λ φ₂ y.out)) μ ∧
        ∫ y, Λ φ₁ y.out * conj (φ₂ y.out) ∂μ = ∫ y, φ₁ y.out * conj (Λ φ₂ y.out) ∂μ) :
    IsOrthogonalL2Extension μ (fun f q => Λ (fun x => f (LeftCosetSpace.mk Γ x)) q.out) := by
  have hinv : ∀ f : LeftCosetSpace Γ → ℂ, ∀ g ∈ Γ, ∀ x : H,
      f (LeftCosetSpace.mk Γ (g * x)) = f (LeftCosetSpace.mk Γ x) :=
    fun f g hg x => congrArg f (LeftCosetSpace.mk_subgroup_mul Γ ⟨g, hg⟩ x)
  have hlift : ∀ f : LeftCosetSpace Γ → ℂ, Measurable f →
      (∀ C : Set (LeftCosetSpace Γ), IsCompact C → ∃ M : ℝ, ∀ q ∈ C, ‖f q‖ ≤ M) →
      Measurable (fun x => f (LeftCosetSpace.mk Γ x)) ∧
        (∀ C : Set H, IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖f (LeftCosetSpace.mk Γ x)‖ ≤ M) ∧
        ∀ g ∈ Γ, ∀ x, f (LeftCosetSpace.mk Γ (g * x)) = f (LeftCosetSpace.mk Γ x) :=
    fun f hf hb => ⟨hf.comp (LeftCosetSpace.measurable_mk Γ),
      LeftCosetSpace.bounded_comp_mk Γ hb, hinv f⟩
  apply isOrthogonalL2Extension_of_pairing
  · intro f hf hb
    obtain ⟨h1, h2, h3⟩ := hlift f hf hb
    obtain ⟨k1, k2, k3⟩ := hB _ h1 h2 h3
    exact ⟨LeftCosetSpace.measurable_out_of_invariant_complex Γ k1 k3,
      LeftCosetSpace.bounded_out_of_invariant Γ k2 k3⟩
  · intro ψ hψ hψc
    have hb : ∀ C : Set (LeftCosetSpace Γ), IsCompact C → ∃ M : ℝ, ∀ q ∈ C, ‖ψ q‖ ≤ M :=
      fun C hC => hC.exists_bound_of_continuousOn hψ.continuousOn
    obtain ⟨h1, h2, h3⟩ := hlift ψ hψ.measurable hb
    obtain ⟨-, -, k3⟩ := hB _ h1 h2 h3
    funext q
    have heq : (fun x => Λ (fun y => ψ (LeftCosetSpace.mk Γ y)) (LeftCosetSpace.mk Γ x).out) =
        Λ (fun y => ψ (LeftCosetSpace.mk Γ y)) :=
      funext fun x => LeftCosetSpace.apply_out_mk Γ k3 x
    simp only [heq, hI _ h1 h2 h3]
  · intro f ψ hf hb hψ hψc
    obtain ⟨h1, h2, h3⟩ := hlift f hf hb
    have hc : Continuous (fun x => ψ (LeftCosetSpace.mk Γ x)) :=
      hψ.comp (LeftCosetSpace.continuous_mk Γ)
    obtain ⟨hint, heq⟩ := hP _ _ h1 h2 h3 hc (hinv ψ)
      (LeftCosetSpace.exists_compact_support_comp_mk Γ hψc)
    simp only [LeftCosetSpace.mk_out] at hint heq
    exact ⟨hint, heq⟩

end ArthurTruncation

end Langlands.Global
