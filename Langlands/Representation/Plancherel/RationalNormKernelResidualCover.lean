import Langlands.Representation.Plancherel.RationalNormKernelCentralCover
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! # Restricting central residual covers to the actual norm kernel -/

noncomputable section

open scoped Pointwise

namespace Langlands

universe uG uA

variable {G : Type uG} [Group G]

/-- Enlarge an ambient subgroup by the central part of `H`, and restrict the
result to `H`. This absorbs the central corrections in a residual cover. -/
def centralResidualNormalizer (H Γ : Subgroup G) : Subgroup H :=
  (Γ ⊔ (H ⊓ Subgroup.center G)).comap H.subtype

/-- Finitely many central cosets that meet a subgroup have finitely many
representatives in that subgroup, modulo its intersection with the center. -/
theorem exists_finite_subgroup_central_representatives (H : Subgroup G)
    (T : Set G) (hT : T.Finite) :
    ∃ R : Set H, R.Finite ∧
      ∀ f ∈ T, ∀ z ∈ Subgroup.center G, f * z ∈ H →
        ∃ r ∈ R, ∃ c ∈ H ⊓ Subgroup.center G, f * z = (r : G) * c := by
  classical
  let S := {f : G | f ∈ T ∧ ∃ z ∈ Subgroup.center G, f * z ∈ H}
  have hS : S.Finite := hT.subset fun _ hf => hf.1
  have hz : ∀ f : S, ∃ z : G, z ∈ Subgroup.center G ∧ (f : G) * z ∈ H := by
    intro f
    exact f.property.2
  choose z hzcentral hzH using hz
  let rep : S → H := fun f => ⟨(f : G) * z f, hzH f⟩
  let : Finite S := hS.to_subtype
  refine ⟨Set.range rep, Set.finite_range rep, ?_⟩
  intro f hf w hw hfw
  let s : S := ⟨f, hf, w, hw, hfw⟩
  refine ⟨rep s, ⟨s, rfl⟩, (z s)⁻¹ * w, ⟨?_, ?_⟩, ?_⟩
  · change (z s)⁻¹ * w ∈ H
    have h := H.mul_mem (H.inv_mem (hzH s)) hfw
    change (f * z s)⁻¹ * (f * w) ∈ H at h
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using h
  · exact (Subgroup.center G).mul_mem
      ((Subgroup.center G).inv_mem (hzcentral s)) hw
  · change f * w = (f * z s) * ((z s)⁻¹ * w)
    group

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Adjoining a compact central subgroup to a compact subgroup stays compact. -/
theorem isCompact_sup_of_central (Γ C : Subgroup G)
    (hΓ : IsCompact (Γ : Set G)) (hC : IsCompact (C : Set G))
    (hcentral : C ≤ Subgroup.center G) :
    IsCompact ((Γ ⊔ C : Subgroup G) : Set G) := by
  let : C.Normal := Subgroup.normal_of_le_center hcentral
  rw [Subgroup.mul_normal]
  exact hΓ.mul hC

/-- A central finite-residual cover with subgroup-valued positive parameters
restricts to a literal finite-residual cover inside the subgroup. The compact
central kernel is absorbed into the compact normalizer. -/
theorem exists_compact_subgroup_residual_cover_of_central_cover
    (H K Γ : Subgroup G) (hH : IsClosed (H : Set G))
    (hΓc : IsCompact (Γ : Set G)) (hΓH : Γ ≤ H)
    (hΓK : Γ ≤ Subgroup.normalizer (K : Set G))
    (hHZ : IsCompact ((H ⊓ Subgroup.center G : Subgroup G) : Set G))
    {A : Type uA} (e : A → H) (T : Set G) (hT : T.Finite)
    (hcover : ∀ g : H, ∃ γ ∈ Γ, ∃ γ' ∈ Γ, ∃ f ∈ T, ∃ a : A,
      ∃ z ∈ Subgroup.center G, (g : G) = γ * ((e a : G) * f) * γ' * z) :
    ∃ ΓH : Subgroup H, IsCompact (ΓH : Set H) ∧
      Γ.comap H.subtype ≤ ΓH ∧
      ΓH ≤ Subgroup.normalizer ((K.comap H.subtype : Subgroup H) : Set H) ∧
      ∃ R : Set H, R.Finite ∧
        ∀ g : H, ∃ γ ∈ ΓH, ∃ γ' ∈ ΓH, ∃ f ∈ R, ∃ a : A,
          g = γ * (e a * f) * γ' := by
  let C := H ⊓ Subgroup.center G
  let ΓG := Γ ⊔ C
  let ΓH := centralResidualNormalizer H Γ
  have hΓGc : IsCompact (ΓG : Set G) :=
    isCompact_sup_of_central Γ C hΓc hHZ inf_le_right
  have hΓGK : ΓG ≤ Subgroup.normalizer (K : Set G) :=
    sup_le hΓK (inf_le_right.trans (Subgroup.center_le_normalizer _))
  have hΓHc : IsCompact (ΓH : Set H) :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage hΓGc
  obtain ⟨R, hR, hrep⟩ := exists_finite_subgroup_central_representatives H T hT
  refine ⟨ΓH, hΓHc, ?_, ?_, R, hR, ?_⟩
  · exact Subgroup.comap_mono le_sup_left
  · exact (Subgroup.comap_mono hΓGK).trans (Subgroup.le_normalizer_comap H.subtype)
  · intro g
    obtain ⟨γ, hγ, γ', hγ', f, hf, a, z, hz, hg⟩ := hcover g
    have hzcomm := Subgroup.mem_center_iff.mp hz γ'
    have hmove :
        γ * ((e a : G) * (f * z)) * γ' = γ * ((e a : G) * f) * γ' * z := by
      simp only [mul_assoc]
      rw [hzcomm]
    have hfz : f * z ∈ H := by
      have h := H.mul_mem
        (H.mul_mem (H.inv_mem ((e a).property))
          (H.mul_mem (H.inv_mem (hΓH hγ)) g.property))
        (H.inv_mem (hΓH hγ'))
      rw [hg, ← hmove] at h
      convert h using 1
      group
    obtain ⟨r, hr, c, hc, hrc⟩ := hrep f hf z hz hfz
    let left : H := ⟨γ, hΓH hγ⟩
    let right : H := ⟨c * γ', H.mul_mem hc.1 (hΓH hγ')⟩
    refine ⟨left, ?_, right, ?_, r, hr, a, ?_⟩
    · exact Subgroup.mem_sup_left hγ
    · exact ΓG.mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hγ')
    · apply Subtype.ext
      change (g : G) = γ * ((e a : G) * (r : G)) * (c * γ')
      rw [hg, ← hmove, hrc]
      group

end Langlands

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe uF uA

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)

/-- An ambient finite-residual Cartan cover with norm-kernel-valued parameters
gives actual finite-residual data in the inherited norm-kernel topology. -/
theorem exists_rationalNormKernel_residual_cover
    {A : Type uA} :
    haveI := hG.isAffineHom
    haveI := hG.smooth
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ (K Γ : Subgroup (rationalPoints G)), IsCompact (Γ : Set (rationalPoints G)) →
      Γ ≤ Subgroup.normalizer (K : Set (rationalPoints G)) →
      ∀ (e : A → rationalCommonNormKernel G)
        (T : Set (rationalPoints G)), T.Finite →
        (∀ g : rationalCommonNormKernel G,
          ∃ k₁ ∈ Γ, ∃ k₂ ∈ Γ, ∃ f ∈ T, ∃ a : A,
            ∃ z ∈ Subgroup.center (rationalPoints G),
              (g : rationalPoints G) = k₁ * ((e a : rationalPoints G) * f) * k₂ * z) →
        ∃ ΓH : Subgroup (rationalCommonNormKernel G),
          IsCompact (ΓH : Set (rationalCommonNormKernel G)) ∧
          Γ.comap (rationalCommonNormKernel G).subtype ≤ ΓH ∧
          ΓH ≤ Subgroup.normalizer
            ((K.comap (rationalCommonNormKernel G).subtype :
              Subgroup (rationalCommonNormKernel G)) : Set (rationalCommonNormKernel G)) ∧
          ∃ R : Set (rationalCommonNormKernel G), R.Finite ∧
            ∀ g : rationalCommonNormKernel G,
              ∃ k₁ ∈ ΓH, ∃ k₂ ∈ ΓH, ∃ f ∈ R, ∃ a : A,
                g = k₁ * (e a * f) * k₂ := by
  let := hG.isAffineHom
  let := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro K Γ hΓ hΓK e T hT hcover
  exact exists_compact_subgroup_residual_cover_of_central_cover
    (rationalCommonNormKernel G) K Γ (isClosed_rationalCommonNormKernel G)
    hΓ (compactSubgroup_le_rationalCommonNormKernel G Γ hΓ) hΓK
    (isCompact_rationalCommonNormKernel_inf_center G hG) e T hT hcover

end Langlands.Plancherel
