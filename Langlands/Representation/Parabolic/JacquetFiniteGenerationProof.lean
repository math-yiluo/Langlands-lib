import Langlands.Representation.Parabolic.JacquetFiniteGenerationStatement
import Langlands.Representation.Parabolic.QuotientCompactProof
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
import Mathlib.RepresentationTheory.Subrepresentation

/-! Finite generation of the actual normalized standard Jacquet module. -/

noncomputable section

namespace Langlands.Parabolic

universe uF uV

namespace JacquetFiniteGeneration

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

variable [TopologicalSpace (GeneralLinear n F.Carrier)]
  [IsTopologicalGroup (GeneralLinear n F.Carrier)]

/-- Compactness of the parabolic quotient turns finitely many smooth ambient
 generators into finitely many generators of the normalized Jacquet module. -/
theorem finite_of_compactQuotient
    [CompactSpace (Induction.LeftQuotient (B.parabolic F.Carrier))]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsSmooth ρ)
    (hfg : Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) ρ.asModule) :
    Module.Finite (MonoidAlgebra ℂ (B.Levi F.Carrier))
      (T.normalizedJacquet B ρ).asModule := by
  classical
  obtain ⟨s, hs⟩ := hfg.fg_top
  have hcover : ∀ v : V, ∃ t : Finset (GeneralLinear n F.Carrier),
      ∀ S : Subrepresentation (T.normalizedJacquet B ρ),
        (∀ i ∈ t, B.jacquetMk ρ (ρ i v) ∈ S) →
        ∀ g, B.jacquetMk ρ (ρ g v) ∈ S := by
    intro v
    obtain ⟨K, hK⟩ := hρ v
    obtain ⟨t, ht⟩ := Induction.exists_finset_doubleCoset_cover (B.parabolic F.Carrier) K
    refine ⟨t, ?_⟩
    intro S hS g
    obtain ⟨i, hi, q, hq, k, hk, rfl⟩ := ht g
    have hk' : ρ k v = v := hK ⟨k, hk⟩
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hk']
    have h := Langlands.CuspidalSupport.QuasicuspidalEmbedding.jacquetMk_parabolic
      T B ρ ⟨q, hq⟩ (ρ i v)
    change B.jacquetMk ρ (ρ q (ρ i v)) = _ at h
    rw [h]
    exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule _ (hS i hi))
  choose t ht using hcover
  let y : Finset (T.normalizedJacquet B ρ).asModule :=
    s.biUnion fun v => (t v).image fun i => B.jacquetMk ρ (ρ i v)
  let N := Submodule.span (MonoidAlgebra ℂ (B.Levi F.Carrier))
    (y : Set (T.normalizedJacquet B ρ).asModule)
  let S := Subrepresentation.ofSubmodule' N
  have hmem : ∀ v ∈ s, ∀ g, B.jacquetMk ρ (ρ g v) ∈ S := by
    intro v hv
    apply ht v S
    intro i hi
    change B.jacquetMk ρ (ρ i v) ∈ N
    apply Submodule.subset_span
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image_of_mem _ hi⟩
  let C : Subrepresentation ρ :=
    { toSubmodule := ⨅ g, S.toSubmodule.comap ((B.jacquetMk ρ).comp (ρ g))
      apply_mem_toSubmodule := by
        intro g v hv
        rw [Submodule.mem_iInf] at hv ⊢
        intro a
        change B.jacquetMk ρ (ρ a (ρ g v)) ∈ S
        rw [← Module.End.mul_apply, ← map_mul]
        exact hv (a * g) }
  have hle : Submodule.span (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      (s : Set ρ.asModule) ≤ C.asSubmodule := by
    apply Submodule.span_le.mpr
    intro v hv
    change (show V from v) ∈ C.toSubmodule
    exact (Submodule.mem_iInf _).mpr (hmem v hv)
  have hN : N = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ x
    have hv : v ∈ C.asSubmodule := hle (hs.symm ▸ Submodule.mem_top)
    change v ∈ C.toSubmodule at hv
    have hv1 := (Submodule.mem_iInf _).mp hv 1
    change B.jacquetMk ρ (ρ 1 v) ∈ S at hv1
    change B.jacquetMk ρ v ∈ S
    simpa only [map_one, Module.End.one_apply] using hv1
  exact ⟨⟨y, hN⟩⟩

end JacquetFiniteGeneration

/-- Smooth finite generation is preserved by every actual normalized standard
 GL Jacquet functor, including rank zero and arbitrary carrier universe. -/
theorem normalizedJacquetFiniteGeneration :
    NormalizedJacquetFiniteGenerationStatement.{uF, uV} := by
  intro p hp F T n B
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V hV hCV ρ hρ hfg
  let : CompactSpace (Induction.LeftQuotient (B.parabolic F.Carrier)) :=
    parabolicQuotientCompact F T B
  exact JacquetFiniteGeneration.finite_of_compactQuotient T B ρ hρ hfg

end Langlands.Parabolic
