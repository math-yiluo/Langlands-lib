import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.CuspidalSupport.HarishChandraConverseProof
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility

/-!
# Compact restriction coefficients and escaping Iwahori contractions

These internal helpers isolate the representation-theoretic step in the
compact-restriction converse. Geometric existence of the escaping contractions
is a separate obligation.
-/

noncomputable section

open Filter Topology

namespace Langlands.CompactCoefficient

universe uG uV

/-- A sequence eventually leaves each compact subset of its space. -/
def EscapesCompactSets {X : Type*} [TopologicalSpace X] (x : ℕ → X) : Prop :=
  ∀ C : Set X, IsCompact C → ∀ᶠ r in atTop, x r ∉ C

/-- Escape after a continuous map implies escape in the source. -/
theorem EscapesCompactSets.of_continuous
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : ℕ → X} {f : X → Y} (hx : EscapesCompactSets (f ∘ x))
    (hf : Continuous f) : EscapesCompactSets x := by
  intro C hC
  filter_upwards [hx (f '' C) (hC.image hf)] with r hr
  exact fun h => hr ⟨x r, h, rfl⟩

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Compact coefficients of a subgroup restriction force some compact average
along every escaping subgroup sequence to vanish. -/
theorem exists_average_eq_zero_of_compact_restriction
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (H : Subgroup G)
    (hc : HasCompactSmoothDualCoefficients (ρ.comp H.subtype))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (x : ℕ → H) (hx : EscapesCompactSets x) (v : V) :
    ∃ r, Compact.averageMap ρ hρ K hK (ρ (x r).val v) = 0 := by
  apply CuspidalSupport.HarishChandra.exists_eq_zero_of_eventually_dual
  intro ℓ
  let τ : Representation ℂ H V := ρ.comp H.subtype
  let ℓ' : Module.Dual ℂ V := ℓ.comp (Compact.averageMap ρ hρ K hK)
  have hι : Continuous H.subtype := continuous_subtype_val
  have hℓ' : IsSmoothVector τ.dual ℓ' := by
    refine ⟨K.comap H.subtype hι, ?_⟩
    intro k
    apply LinearMap.ext
    intro w
    change ℓ (Compact.averageMap ρ hρ K hK (ρ k.val.val⁻¹ w)) =
      ℓ (Compact.averageMap ρ hρ K hK w)
    exact congrArg ℓ (CuspidalSupport.HarishChandra.averageMap_apply_mem ρ hρ K hK
      (k := k.val.val⁻¹) (K.inv_mem k.property) w)
  have hsupport := hc v ℓ' hℓ'
  filter_upwards [hx _ hsupport.isCompact] with r hr
  exact image_eq_zero_of_notMem_tsupport (f := matrixCoefficient τ ℓ' v) hr

/-- An escaping Iwahori contraction in a compact-coefficient subgroup kills
the actual Jacquet class of every vector fixed by its compact open level. -/
theorem mk_eq_zero_of_escaping_iwahoriContraction
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (H : Subgroup G)
    (hc : HasCompactSmoothDualCoefficients (ρ.comp H.subtype))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (N M Nbar : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (g : H) (hg : Jacquet.IsIwahoriContraction K N M Nbar g.val)
    (hescape : EscapesCompactSets (fun r : ℕ => g ^ r))
    (v : V) (hv : v ∈ fixedVectors ρ K.toSubgroup) :
    Jacquet.mk ρ N v = 0 := by
  obtain ⟨r, hr⟩ := exists_average_eq_zero_of_compact_restriction
    ρ hρ H hc K hK (fun r => g ^ r) hescape v
  have hpow : (⟨v, hv⟩ : fixedVectors ρ K.toSubgroup) ∈
      Jacquet.powerKernelSup ρ hρ K hK g.val := by
    apply le_iSup (fun s : ℕ =>
      LinearMap.ker (Jacquet.compressedAction ρ hρ K hK g.val ^ s)) r
    rw [LinearMap.mem_ker, ← hg.compressedAction_pow ρ hρ hK r]
    apply Subtype.ext
    exact hr
  rw [Jacquet.powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ hK hg hMN,
    LinearMap.mem_ker] at hpow
  exact Subtype.ext_iff.mp hpow

/-- Ambient cofinality of compact open Iwahori contractions whose contracting
elements lie in the specified subgroup and whose powers escape there. -/
def HasEscapingIwahoriContractionBasis (H N M Nbar : Subgroup G) : Prop :=
  ∀ U : OpenSubgroup G, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
    K.toSubgroup ≤ U.toSubgroup ∧
    ∃ g : H, Jacquet.IsIwahoriContraction K N M Nbar g.val ∧
      EscapesCompactSets (fun r : ℕ => g ^ r)

/-- Compact subgroup-restriction coefficients and an ambient cofinal escaping
contraction basis imply vanishing of the actual coinvariant space. -/
theorem subsingleton_coinvariants_of_compact_restriction
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (H N M Nbar : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N)
    (hc : HasCompactSmoothDualCoefficients (ρ.comp H.subtype))
    (hbasis : HasEscapingIwahoriContractionBasis H N M Nbar) :
    Subsingleton (Jacquet.Coinvariants ρ N) := by
  have hzero (v : V) : Jacquet.mk ρ N v = 0 := by
    obtain ⟨U, hU⟩ := hρ v
    obtain ⟨K, hK, hKU, g, hg, hescape⟩ := hbasis U
    exact mk_eq_zero_of_escaping_iwahoriContraction ρ hρ H hc K hK
      N M Nbar hMN g hg hescape v (fun k => hU ⟨k.val, hKU k.property⟩)
  refine ⟨fun x y => ?_⟩
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N x
  obtain ⟨w, rfl⟩ := Jacquet.mk_surjective ρ N y
  rw [hzero v, hzero w]

end Langlands.CompactCoefficient
