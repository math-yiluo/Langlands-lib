import Langlands.Representation.Aubert.General.JacquetFiniteGenerationStatement
import Mathlib.RepresentationTheory.Subrepresentation

/-! Finite generation of the actual normalized Jacquet functor with compact quotient. -/

noncomputable section

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}

namespace JacquetFiniteGeneration

/-- The quotient of a parabolic translate is a scalar multiple of the
normalized action of its actual Levi projection. -/
theorem mk_parabolic (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ G)
    (p : P) (v : A) :
    Jacquet.Localization.mk A.representation U 1 (A.representation p v) =
      (((HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer
          (h.projection p))⁻¹ : ℂˣ) : ℂ) •
        ((jacquetFunctor h hU).obj A).representation (h.projection p)
          (Jacquet.Localization.mk A.representation U 1 v) := by
  let m : M := h.projection p
  let u : U := ⟨(m : G)⁻¹ * (p : G), h.projection_inv_mul_mem p⟩
  have hp : (p : G) = (m : G) * (u : G) := by simp [u]
  have hcoinv : Jacquet.Localization.mk A.representation U 1
      (A.representation p v) =
      Jacquet.Localization.mk A.representation U 1 (A.representation m v) := by
    rw [hp, map_mul, Module.End.mul_apply]
    rw [← Jacquet.Localization.action_mk A.representation U 1 M
      h.levi_le_normalizer (Jacquet.Localization.isInvariant_one U M h.levi_le_normalizer)]
    simp only [Jacquet.Localization.mk_apply_subgroup, MonoidHom.one_apply,
      Units.val_one, one_smul]
    rfl
  rw [hcoinv]
  let c := HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer
    (h.projection p)
  change Jacquet.Localization.mk A.representation U 1 (A.representation m v) =
    ((c⁻¹ : ℂˣ) : ℂ) • ((c : ℂ) •
      Jacquet.Localization.mk A.representation U 1 (A.representation m v))
  rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/-- Compactness of `P \ G` turns finite ambient generation into finite
Levi generation for the intrinsic Haar-normalized Jacquet functor. -/
theorem finite_of_compactQuotient (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) [CompactSpace (Induction.LeftQuotient P)]
    (A : SmoothRep.{0, uG, uV} ℂ G)
    (hfg : Module.Finite (MonoidAlgebra ℂ G) A.representation.asModule) :
    Module.Finite (MonoidAlgebra ℂ M)
      ((jacquetFunctor h hU).obj A).representation.asModule := by
  classical
  let J := ((jacquetFunctor h hU).obj A).representation
  let q := Jacquet.Localization.mk A.representation U 1
  obtain ⟨s, hs⟩ := hfg.fg_top
  have hcover : ∀ v : A, ∃ t : Finset G,
      ∀ S : Subrepresentation J,
        (∀ i ∈ t, q (A.representation i v) ∈ S) →
        ∀ g, q (A.representation g v) ∈ S := by
    intro v
    obtain ⟨K, hK⟩ := A.isSmooth v
    obtain ⟨t, ht⟩ := Induction.exists_finset_doubleCoset_cover P K
    refine ⟨t, ?_⟩
    intro S hS g
    obtain ⟨i, hi, p, hp, k, hk, rfl⟩ := ht g
    have hk' : A.representation k v = v := hK ⟨k, hk⟩
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hk']
    change Jacquet.Localization.mk A.representation U 1
      (A.representation p (A.representation i v)) ∈ S
    rw [mk_parabolic h hU A ⟨p, hp⟩]
    exact S.toSubmodule.smul_mem _
      (S.apply_mem_toSubmodule _ (hS i hi))
  choose t ht using hcover
  let y : Finset J.asModule :=
    s.biUnion fun v => (t v).image fun i => q (A.representation i v)
  let N := Submodule.span (MonoidAlgebra ℂ M) (y : Set J.asModule)
  let S := Subrepresentation.ofSubmodule' N
  have hmem : ∀ v ∈ s, ∀ g, q (A.representation g v) ∈ S := by
    intro v hv
    apply ht v S
    intro i hi
    change q (A.representation i v) ∈ N
    apply Submodule.subset_span
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image_of_mem _ hi⟩
  let C : Subrepresentation A.representation :=
    { toSubmodule := ⨅ g, S.toSubmodule.comap (q.comp (A.representation g))
      apply_mem_toSubmodule := by
        intro g v hv
        rw [Submodule.mem_iInf] at hv ⊢
        intro a
        change q (A.representation a (A.representation g v)) ∈ S
        rw [← Module.End.mul_apply, ← map_mul]
        exact hv (a * g) }
  have hle : Submodule.span (MonoidAlgebra ℂ G)
      (s : Set A.representation.asModule) ≤ C.asSubmodule := by
    apply Submodule.span_le.mpr
    intro v hv
    change (show A from v) ∈ C.toSubmodule
    exact (Submodule.mem_iInf _).mpr (hmem v hv)
  have hN : N = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective A.representation U 1 x
    have hv : v ∈ C.asSubmodule := hle (hs.symm ▸ Submodule.mem_top)
    change v ∈ C.toSubmodule at hv
    have hv1 := (Submodule.mem_iInf _).mp hv 1
    change q (A.representation 1 v) ∈ S at hv1
    change q v ∈ S
    simpa only [map_one, Module.End.one_apply] using hv1
  exact ⟨⟨y, hN⟩⟩

/-- A finite-length input is finitely generated over the ambient group
algebra, so the compact-quotient result applies. -/
theorem finite_of_hasFiniteLength_of_compactQuotient
    (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) [CompactSpace (Induction.LeftQuotient P)]
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.HasFiniteLength) :
    Module.Finite (MonoidAlgebra ℂ M)
      ((jacquetFunctor h hU).obj A).representation.asModule := by
  have hN : IsNoetherian (MonoidAlgebra ℂ G) A.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hA).1
  let := hN
  exact finite_of_compactQuotient h hU A inferInstance

end JacquetFiniteGeneration

/-- The compact-quotient finite-generation input, with independent group
and representation-carrier universes. -/
theorem jacquetFiniteGenerationOfCompactQuotient :
    JacquetFiniteGenerationOfCompactQuotientStatement.{uG, uV} := by
  intro G hG tG lG nG P M U h hU hcompact A hA
  exact JacquetFiniteGeneration.finite_of_compactQuotient h hU A hA

end Langlands.Aubert.General
