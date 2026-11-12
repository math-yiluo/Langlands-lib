import Langlands.Representation.Families.RenardFamilyParabolicStatements
import Langlands.Representation.Exponents.ArbitraryParabolicFiniteSupportReduction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.BruhatTits.Parabolic.QuotientCompactProof
import Langlands.Representation.Induction.CompactQuotientProof
import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Renard VI.8.3: Jacquet modules of families preserve finite generation

If `P = M ⋉ U` with `P \ G` compact, the normalized Jacquet module of a smooth family that is
finitely generated over `B[G]` is finitely generated over `B[M]`
(`finite_jacquet_comp_of_compactQuotient`). Applied to a represented parabolic, whose
quotient `P(F)\G(F)` is compact by the published structural theorems, this proves the VI.8.3
Proposition `JacquetFiniteTypeStatement` (`jacquetFiniteType`).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily

universe u uB uG uH uM uV uW

section Generation

variable {B : Type uB} [CommRing B] {H : Type uH} [Group H] {M : Type uM} [Group M]
  {V : Type uV} [AddCommGroup V] [Module B V] {W : Type uW} [AddCommGroup W] [Module B W]

/-- Finite generation passes from a `B[H]`-module `V` to a `B[M]`-module `W` along a
surjective `B`-linear map `q : V → W`, provided that for every `v` there are finitely many
`i ∈ H` such that each subrepresentation of `W` containing the `q (i v)` contains every
`q (g v)`. -/
theorem finite_asModule_of_translateCover (ρ : Representation B H V)
    (J : Representation B M W) (q : V →ₗ[B] W) (hq : Function.Surjective q)
    (hfg : Module.Finite (MonoidAlgebra B H) ρ.asModule)
    (hcover : ∀ v : V, ∃ t : Finset H, ∀ S : Subrepresentation J,
      (∀ i ∈ t, q (ρ i v) ∈ S) → ∀ g, q (ρ g v) ∈ S) :
    Module.Finite (MonoidAlgebra B M) J.asModule := by
  classical
  obtain ⟨s, hs⟩ := hfg.fg_top
  choose t ht using hcover
  let y : Finset J.asModule :=
    s.biUnion fun v => (t v).image fun i => q (ρ i v)
  let N := Submodule.span (MonoidAlgebra B M) (y : Set J.asModule)
  let S := Subrepresentation.ofSubmodule' N
  have hmem : ∀ v ∈ s, ∀ g, q (ρ g v) ∈ S := by
    intro v hv
    apply ht v S
    intro i hi
    change q (ρ i v) ∈ N
    apply Submodule.subset_span
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image_of_mem _ hi⟩
  let C : Subrepresentation ρ :=
    { toSubmodule := ⨅ g, S.toSubmodule.comap (q.comp (ρ g))
      apply_mem_toSubmodule := by
        intro g v hv
        rw [Submodule.mem_iInf] at hv ⊢
        intro a
        change q (ρ a (ρ g v)) ∈ S
        rw [← Module.End.mul_apply, ← map_mul]
        exact hv (a * g) }
  have hle : Submodule.span (MonoidAlgebra B H) (s : Set ρ.asModule) ≤ C.asSubmodule := by
    apply Submodule.span_le.mpr
    intro v hv
    change (show V from v) ∈ C.toSubmodule
    exact (Submodule.mem_iInf _).mpr (hmem v hv)
  have hN : N = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    obtain ⟨v, rfl⟩ := hq x
    have hv : v ∈ C.asSubmodule := hle (hs.symm ▸ Submodule.mem_top)
    change v ∈ C.toSubmodule at hv
    have hv1 := (Submodule.mem_iInf _).mp hv 1
    change q (ρ 1 v) ∈ S at hv1
    change q v ∈ S
    simpa only [map_one, Module.End.one_apply] using hv1
  exact ⟨⟨y, hN⟩⟩

end Generation

section Parabolic

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
  {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} {V : Type uV} [AddCommGroup V] [Module B V]

/-- A subrepresentation of the normalized Jacquet module that contains the class of `v`
contains the class of every translate of `v` by the parabolic `P`. -/
theorem mk_parabolic_mem (h : Aubert.General.IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (ρ : Representation B G V)
    (S : Subrepresentation (jacquetRepresentation ρ U M hU h.levi_le_normalizer))
    {v : V} (hv : Jacquet.Localization.mk ρ U 1 v ∈ S) (p : P) :
    Jacquet.Localization.mk ρ U 1 (ρ p v) ∈ S := by
  let m : M := h.projection p
  let n : U := ⟨(m : G)⁻¹ * (p : G), h.projection_inv_mul_mem p⟩
  have hp : (p : G) = (m : G) * (n : G) := by simp [n]
  have hn : Jacquet.Localization.mk ρ U 1 (ρ n v) = Jacquet.Localization.mk ρ U 1 v := by
    rw [Jacquet.Localization.mk_apply_subgroup]
    simp
  have hm := S.apply_mem_toSubmodule m hv
  rw [← hn, jacquet_action_mk h hU ρ m] at hm
  rw [hp, map_mul, Module.End.mul_apply]
  exact (Submodule.smul_mem_iff' _ _).mp hm

/-- Compactness of `P \ G` turns finite generation over `B[G]` into finite generation of the
normalized Jacquet module over `B[M]`, also after pulling back along a surjection onto `M`. -/
theorem finite_jacquet_comp_of_compactQuotient (h : Aubert.General.IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) [CompactSpace (Induction.LeftQuotient P)]
    {M' : Type uM} [Group M'] (φ : M' →* M) (hφ : Function.Surjective φ)
    (ρ : Representation B G V) (hρ : IsSmooth ρ)
    (hfg : Module.Finite (MonoidAlgebra B G) ρ.asModule) :
    Module.Finite (MonoidAlgebra B M')
      (Representation.asModule ((jacquetRepresentation ρ U M hU h.levi_le_normalizer).comp φ)) := by
  refine finite_asModule_of_translateCover ρ _ (Jacquet.Localization.mk ρ U 1)
    (Jacquet.Localization.mk_surjective ρ U 1) hfg fun v => ?_
  obtain ⟨K, hK⟩ := hρ v
  obtain ⟨t, ht⟩ := Induction.exists_finset_doubleCoset_cover P K
  refine ⟨t, fun S hS g => ?_⟩
  obtain ⟨i, hi, p, hp, k, hk, rfl⟩ := ht g
  have hk' : ρ k v = v := hK ⟨k, hk⟩
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hk']
  let S' : Subrepresentation (jacquetRepresentation ρ U M hU h.levi_le_normalizer) :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun m x hx => by
        obtain ⟨m', rfl⟩ := hφ m
        exact S.apply_mem_toSubmodule m' hx }
  exact mk_parabolic_mem h hU ρ S' (hS i hi) ⟨p, hp⟩

end Parabolic

section Statement

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

/-- Renard VI.8.3 Proposition: the normalized Jacquet module of a smooth family that is
finitely generated over `B[G(F)]` is finitely generated over `B[M(F)]`. -/
theorem jacquetFiniteType : JacquetFiniteTypeStatement.{u, uB, uV} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul B _ _ _ _ _ V _ _ ρ hρ _ hfg
  let := compactSpace_leftQuotient_pointImage_of_dynamic parabolicDynamic
    BruhatTits.dynamicParabolicQuotientCompact hG p hp
  let := leviPointTopology l hl
  exact finite_jacquet_comp_of_compactQuotient
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (leviPointsEquiv p l hp hl).toMonoidHom (leviPointsEquiv p l hp hl).surjective ρ hρ hfg

end Statement

end Langlands.Renard.AlgebraicFamily
