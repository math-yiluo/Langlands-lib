import Langlands.AlgebraicGeometry.PointTopology.AffineEtaleBoundedCluster

/-!
# Field-valued points of an étale algebra are uniformly bounded in number

For an étale `R`-algebra `A` there is a bound `D` such that for every field `L` with an
`R`-algebra structure, there are at most `D` homomorphisms of `R`-algebras `A → L`. A
standard étale algebra `(R[X]/f)[1/g]` has at most `deg f` of them, one for each root of `f`
in `L`, and an étale algebra is covered by finitely many standard étale basic opens.
-/

noncomputable section

universe u v w

open Polynomial

namespace Langlands.AlgebraicGeometry.PointTopology

namespace EtaleAlgHomCount

variable {R : Type u} [CommRing R]

/-- A standard étale algebra has at most `deg f` field-valued points. -/
theorem card_algHom_le_of_presentation {S : Type v} [CommRing S] [Algebra R S]
    (P : StandardEtalePresentation R S) (L : Type w) [Field L] [Algebra R L] :
    Finite (S →ₐ[R] L) ∧ Nat.card (S →ₐ[R] L) ≤ P.f.natDegree := by
  classical
  let T : Finset L := (P.f.map (algebraMap R L)).roots.toFinset
  have hT : ∀ φ : S →ₐ[R] L, φ P.x ∈ T := by
    intro φ
    rw [Multiset.mem_toFinset, mem_roots (P.monic_f.map _).ne_zero, IsRoot.def,
      eval_map_algebraMap, aeval_algHom_apply, P.hasMap.1, map_zero]
  let ι : (S →ₐ[R] L) → T := fun φ => ⟨φ P.x, hT φ⟩
  have hι : Function.Injective ι := fun φ ψ h => P.hom_ext (congrArg Subtype.val h)
  have : Finite (S →ₐ[R] L) := Finite.of_injective ι hι
  refine ⟨this, ?_⟩
  calc Nat.card (S →ₐ[R] L) ≤ Nat.card T := Nat.card_le_card_of_injective ι hι
    _ = T.card := Nat.card_eq_finsetCard T
    _ ≤ Multiset.card (P.f.map (algebraMap R L)).roots :=
        Multiset.toFinset_card_le (P.f.map (algebraMap R L)).roots
    _ ≤ (P.f.map (algebraMap R L)).natDegree := card_roots' _
    _ ≤ P.f.natDegree := natDegree_map_le

/-- **Uniform bound for field-valued points of an étale algebra.** -/
theorem exists_card_algHom_le (A : Type v) [CommRing A] [Algebra R A] [Algebra.Etale R A] :
    ∃ D : ℕ, ∀ (L : Type w) [Field L] [Algebra R L],
      Finite (A →ₐ[R] L) ∧ Nat.card (A →ₐ[R] L) ≤ D := by
  classical
  obtain ⟨s, hs, hst⟩ := EtaleBoundedCluster.exists_finset_isStandardEtale (R := R) (A := A)
  let P : ∀ f : s, StandardEtalePresentation R (Localization.Away f.1) := fun f =>
    have := hst f.1 f.2
    Classical.choice Algebra.IsStandardEtale.nonempty_standardEtalePresentation
  refine ⟨∑ f : s, (P f).f.natDegree, fun L _ _ => ?_⟩
  -- every point is nonzero on some element of `s`
  have hex : ∀ φ : A →ₐ[R] L, ∃ f : s, φ f.1 ≠ 0 := by
    intro φ
    by_contra h
    push Not at h
    have hle : Ideal.span (s : Set A) ≤ RingHom.ker φ := by
      rw [Ideal.span_le]
      intro f hf
      exact h ⟨f, hf⟩
    rw [hs] at hle
    have h1 : (1 : A) ∈ RingHom.ker φ := hle Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  choose c hc using hex
  have hunit : ∀ (φ : A →ₐ[R] L) (y : Submonoid.powers (c φ).1), IsUnit (φ y) := by
    rintro φ ⟨y, n, rfl⟩
    exact (map_pow φ _ n) ▸ (IsUnit.pow n (Ne.isUnit (hc φ)))
  let Φ : (A →ₐ[R] L) → Σ f : s, (Localization.Away f.1 →ₐ[R] L) := fun φ =>
    ⟨c φ, IsLocalization.liftAlgHom (M := Submonoid.powers (c φ).1) (hunit φ)⟩
  let Ψ : (Σ f : s, (Localization.Away f.1 →ₐ[R] L)) → (A →ₐ[R] L) := fun χ =>
    χ.2.comp (IsScalarTower.toAlgHom R A (Localization.Away χ.1.1))
  have hΨΦ : Function.LeftInverse Ψ Φ := by
    intro φ
    ext a
    exact IsLocalization.lift_eq (M := Submonoid.powers (c φ).1) (hunit φ) a
  have hfin : ∀ f : s, Finite (Localization.Away f.1 →ₐ[R] L) := fun f =>
    (card_algHom_le_of_presentation (P f) L).1
  have : Finite (A →ₐ[R] L) := Finite.of_injective Φ hΨΦ.injective
  refine ⟨this, ?_⟩
  calc Nat.card (A →ₐ[R] L) ≤ Nat.card (Σ f : s, (Localization.Away f.1 →ₐ[R] L)) :=
        Nat.card_le_card_of_injective Φ hΨΦ.injective
    _ = ∑ f : s, Nat.card (Localization.Away f.1 →ₐ[R] L) := Nat.card_sigma
    _ ≤ ∑ f : s, (P f).f.natDegree :=
        Finset.sum_le_sum fun f _ => (card_algHom_le_of_presentation (P f) L).2

end EtaleAlgHomCount

end Langlands.AlgebraicGeometry.PointTopology
