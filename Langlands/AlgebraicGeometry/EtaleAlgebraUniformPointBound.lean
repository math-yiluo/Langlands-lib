import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.SetTheory.Cardinal.Finite

/-!
# A uniform bound for points of an étale algebra
-/

universe u v w

namespace Langlands.AlgebraicGeometry.EtaleAlgebraPointBound

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A homomorphism out of a standard étale algebra determines a root of its
monic defining polynomial. -/
def standardEtaleRootMap (P : StandardEtalePresentation R S)
    (K : Type w) [CommRing K] [IsDomain K] [Algebra R K] :
    (S →ₐ[R] K) → P.f.rootSet K :=
  fun a => ⟨a P.x, P.monic_f.mem_rootSet.mpr (P.hasMap.map a).1⟩

theorem standardEtaleRootMap_injective (P : StandardEtalePresentation R S)
    (K : Type w) [CommRing K] [IsDomain K] [Algebra R K] :
    Function.Injective (standardEtaleRootMap P K) := by
  intro a b h
  exact P.hom_ext (congrArg Subtype.val h)

theorem standardEtale_hom_finite_card_le (P : StandardEtalePresentation R S)
    (K : Type w) [CommRing K] [IsDomain K] [Algebra R K] :
    Finite (S →ₐ[R] K) ∧ Nat.card (S →ₐ[R] K) ≤ P.f.natDegree := by
  refine ⟨Finite.of_injective _ (standardEtaleRootMap_injective P K), ?_⟩
  exact (Nat.card_le_card_of_injective _ (standardEtaleRootMap_injective P K)).trans
    (Polynomial.ncard_rootSet_le P.f K)

theorem exists_finite_standardEtale_cover [Algebra.Etale R S] :
    ∃ t : Finset S, Ideal.span (t : Set S) = ⊤ ∧
      ∀ f ∈ t, Algebra.IsStandardEtale R (Localization.Away f) := by
  classical
  let P : Set S := {f | Algebra.IsStandardEtale R (Localization.Away f)}
  have hP : Ideal.span P = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal (Ideal.span P) h
    let : M.IsMaximal := hM
    obtain ⟨f, hfM, hf⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) M
    exact hfM (hPM (Ideal.subset_span hf))
  obtain ⟨t, htP, ht⟩ := (Ideal.span_eq_top_iff_finite P).mp hP
  exact ⟨t, ht, fun f hf => htP hf⟩

/-- A finite principal cover together with standard étale presentations on its
members. -/
structure StandardEtaleCover (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] where
  elements : Finset S
  span_eq_top : Ideal.span (elements : Set S) = ⊤
  presentation : (f : elements) → StandardEtalePresentation R (Localization.Away (f : S))

noncomputable def StandardEtaleCover.ofEtale (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S] :
    StandardEtaleCover R S := by
  classical
  let h := exists_finite_standardEtale_cover (R := R) (S := S)
  refine ⟨h.choose, h.choose_spec.1, fun f => ?_⟩
  have := h.choose_spec.2 f f.property
  exact Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some

noncomputable def StandardEtaleCover.bound (C : StandardEtaleCover R S) : ℕ :=
  ∑ f : C.elements, (C.presentation f).f.natDegree

theorem StandardEtaleCover.hom_finite_card_le (C : StandardEtaleCover R S)
    (K : Type w) [Field K] [Algebra R K] :
    Finite (S →ₐ[R] K) ∧ Nat.card (S →ₐ[R] K) ≤ C.bound := by
  classical
  let π : (Σ f : C.elements, Localization.Away (f : S) →ₐ[R] K) → (S →ₐ[R] K) :=
    fun b => b.2.comp (IsScalarTower.toAlgHom R S (Localization.Away (b.1 : S)))
  have hπ : Function.Surjective π := by
    intro a
    have hn : ∃ f : C.elements, a (f : S) ≠ 0 := by
      by_contra! h
      have hle : Ideal.span (C.elements : Set S) ≤ RingHom.ker a.toRingHom := by
        rw [Ideal.span_le]
        intro f hf
        exact h ⟨f, hf⟩
      have h1 : (1 : S) ∈ RingHom.ker a.toRingHom := by
        apply hle
        rw [C.span_eq_top]
        trivial
      simp at h1
    obtain ⟨f, hf⟩ := hn
    refine ⟨⟨f, IsLocalization.Away.liftAlgHom (f : S) (isUnit_iff_ne_zero.mpr hf)⟩, ?_⟩
    ext x
    exact IsLocalization.Away.lift_eq (f : S) (isUnit_iff_ne_zero.mpr hf) x
  let : ∀ f : C.elements, Finite (Localization.Away (f : S) →ₐ[R] K) :=
    fun f => (standardEtale_hom_finite_card_le (C.presentation f) K).1
  refine ⟨Finite.of_surjective π hπ, ?_⟩
  calc
    Nat.card (S →ₐ[R] K) ≤
        Nat.card (Σ f : C.elements, Localization.Away (f : S) →ₐ[R] K) :=
      Nat.card_le_card_of_surjective π hπ
    _ = ∑ f : C.elements, Nat.card (Localization.Away (f : S) →ₐ[R] K) :=
      Nat.card_sigma
    _ ≤ C.bound := Finset.sum_le_sum fun f _ =>
      (standardEtale_hom_finite_card_le (C.presentation f) K).2

/-- The sum of the polynomial degrees on a chosen finite standard étale cover. -/
noncomputable def uniformBound (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S] : ℕ :=
  (StandardEtaleCover.ofEtale R S).bound

theorem hom_finite_card_le [Algebra.Etale R S]
    (K : Type w) [Field K] [Algebra R K] :
    Finite (S →ₐ[R] K) ∧ Nat.card (S →ₐ[R] K) ≤ uniformBound R S :=
  (StandardEtaleCover.ofEtale R S).hom_finite_card_le K

end Langlands.AlgebraicGeometry.EtaleAlgebraPointBound
