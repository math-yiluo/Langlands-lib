import Langlands.Representation.CuspidalSupport.HarishChandraConverseProof
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility

/-! # Compact coefficients and escaping Iwahori contractions -/

noncomputable section

open Filter Topology

namespace Langlands.Jacquet

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The nonnegative powers of a group element eventually leave every compact
subset of the ambient group. -/
def HasEscapingPowers (g : G) : Prop :=
  ∀ C : Set G, IsCompact C → ∀ᶠ n : ℕ in atTop, g ^ n ∉ C

/-- A fixed vector has zero Jacquet class if compression uses an Iwahori
contraction whose powers lie in a subgroup with compact smooth-dual
coefficients and eventually leave every ambient compact set. -/
theorem mem_relations_of_compactCoefficients_of_iwahoriContraction
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (H : Subgroup G) (hcoeff : HasCompactSmoothDualCoefficients (ρ.comp H.subtype))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (N M Nbar : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (g : G) (hg : g ∈ H) (hc : IsIwahoriContraction K N M Nbar g)
    (hescape : HasEscapingPowers g)
    (v : V) (hv : v ∈ fixedVectors ρ K.toSubgroup) :
    v ∈ relations ρ N := by
  have hex : ∃ r : ℕ, Compact.averageMap ρ hρ K hK (ρ (g ^ r) v) = 0 := by
    apply CuspidalSupport.HarishChandra.exists_eq_zero_of_eventually_dual
    intro ℓ
    let ℓ' : Module.Dual ℂ V := ℓ ∘ₗ Compact.averageMap ρ hρ K hK
    have hℓ' : IsSmoothVector (Representation.dual (ρ.comp H.subtype)) ℓ' := by
      refine ⟨OpenSubgroup.comap H.subtype continuous_subtype_val K, ?_⟩
      intro k
      apply LinearMap.ext
      intro x
      change ℓ (Compact.averageMap ρ hρ K hK (ρ (k.val.val)⁻¹ x)) =
        ℓ (Compact.averageMap ρ hρ K hK x)
      rw [CuspidalSupport.HarishChandra.averageMap_apply_mem ρ hρ K hK
        (k := (k.val.val)⁻¹) (K.inv_mem k.property)]
    have hcompact := (hcoeff v ℓ' hℓ').isCompact.image
      (continuous_subtype_val : Continuous (Subtype.val : H → G))
    filter_upwards [hescape _ hcompact] with r hr
    have hnot : (⟨g ^ r, pow_mem hg r⟩ : H) ∉
        tsupport (matrixCoefficient (ρ.comp H.subtype) ℓ' v) := by
      intro hmem
      exact hr ⟨_, hmem, rfl⟩
    have hz := image_eq_zero_of_notMem_tsupport hnot
    exact hz
  obtain ⟨r, hr⟩ := hex
  have hsup : (⟨v, hv⟩ : fixedVectors ρ K.toSubgroup) ∈
      powerKernelSup ρ hρ K hK g := by
    apply le_iSup (fun s : ℕ => LinearMap.ker (compressedAction ρ hρ K hK g ^ s)) r
    rw [LinearMap.mem_ker, ← hc.compressedAction_pow ρ hρ hK r]
    exact Subtype.ext hr
  rw [powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ hK hc hMN,
    LinearMap.mem_ker] at hsup
  exact (mk_eq_zero ρ N v).mp (congrArg Subtype.val hsup)

/-- An ambient-cofinal Iwahori contraction basis with one escaping element
in the coefficient subgroup makes the entire Jacquet relation space top. -/
theorem relations_eq_top_of_compactCoefficients_of_iwahoriBasis
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (H : Subgroup G) (hcoeff : HasCompactSmoothDualCoefficients (ρ.comp H.subtype))
    (N M Nbar : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (g : G) (hg : g ∈ H)
    (hbasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O ∧
        IsIwahoriContraction K N M Nbar g)
    (hescape : HasEscapingPowers g) :
    relations ρ N = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨L, hL⟩ := hρ v
  obtain ⟨K, hK, hKL, hc⟩ := hbasis (L : Set G) L.isOpen L.one_mem
  exact mem_relations_of_compactCoefficients_of_iwahoriContraction ρ hρ H hcoeff
    K hK N M Nbar hMN g hg hc hescape v (fun k => hL ⟨k.val, hKL k.property⟩)

end Langlands.Jacquet
