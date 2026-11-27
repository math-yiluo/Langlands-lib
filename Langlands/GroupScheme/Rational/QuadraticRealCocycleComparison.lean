import Langlands.GroupScheme.GaloisCocycleScalarExtension
import Mathlib.NumberTheory.NumberField.Completion.Ramification

/-! # Quadratic cocycle values at real places -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped NumberField.LiesOver CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisCocycle

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem quadratic_aut_eq_one_or {K M : Type u} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M] (hdeg : Module.finrank K M = 2)
    (τ : M ≃ₐ[K] M) (hτ : τ ≠ 1) (s : M ≃ₐ[K] M) :
    s = 1 ∨ s = τ := by
  have hc := (IsGalois.card_aut_eq_finrank K M).trans hdeg
  obtain ⟨_, _, hu⟩ := (Nat.card_eq_two_iff' (1 : M ≃ₐ[K] M)).mp hc
  by_cases hs : s = 1
  · exact Or.inl hs
  · exact Or.inr ((hu s hs).trans (hu τ hτ).symm)

section LocalComparison

variable {F K L M : Type u} [Field F] [Field K] [Field L] [Field M]
  [Algebra F K] [Algebra F L] [Algebra F M] [Algebra K M] [Algebra L M]
  [IsScalarTower F K M] [IsScalarTower F L M] [Normal F L]
  [FiniteDimensional K M] [IsGalois K M]
  {G : GroupScheme (Spec (CommRingCat.of F))}

/-- With a quadratic local coefficient field, triviality on the entire
pullback cover is equivalent to the one crossed coboundary equation. -/
theorem isTrivial_baseChangePullback_iff_quadratic_value (ξ : Cocycle G (cover F L))
    (hdeg : Module.finrank K M = 2) (τ : M ≃ₐ[K] M) (hτ : τ ≠ 1) :
    (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial ↔
      ∃ a : G.affinePoints (CommAlgCat.of F M),
        GaloisPoint.relativeExtend F L M G (value ξ ((τ.restrictScalars F).restrictNormal L)) =
          a * (GaloisPoint.relativeConjugate F K M G τ a)⁻¹ := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := exists_galois_coboundary_of_baseChange_isTrivial (K := K) (M := M) ξ h
    exact ⟨a, ha τ⟩
  · rintro ⟨a, ha⟩
    apply isTrivial_baseChange_of_scalarExtension (M := M) ξ
    let e := scalarExtensionPointsEquiv (F := F) (K := K) (M := M) G
    apply (isTrivial_iff _).mpr
    refine ⟨e.symm a, fun s => ?_⟩
    rcases quadratic_aut_eq_one_or hdeg τ hτ s with hs | hs
    · subst s
      change (scalarExtension (K := K) (M := M) ξ).toFun (𝟙 _) (arrow K M 1) = _
      rw [arrow_one, Cocycle.toFun_self, GaloisPoint.conjugate_one, mul_inv_cancel]
    · subst s
      apply e.injective
      rw [map_mul, map_inv, show e (GaloisPoint.conjugate K M _ τ (e.symm a)) =
        GaloisPoint.relativeConjugate F K M G τ (e (e.symm a)) from
          scalarExtensionPointsEquiv_conjugate (e.symm a) τ, e.apply_symm_apply]
      rw [← ha]
      exact value_scalarExtension ξ τ

end LocalComparison

section Completions

open InfinitePlace InfinitePlace.Completion

variable {F Q : Type u} [Field F] [Field Q] [Algebra F Q]
  (v : InfinitePlace F) (w : InfinitePlace Q) [w.LiesOver v]

/-- The original inclusion into the upper completion respects the
intermediate number field. -/
theorem infiniteCompletionScalarTower : IsScalarTower F Q w.Completion :=
  .of_algebraMap_eq fun x => by
    apply InfinitePlace.Completion.ext
    simp [InfinitePlace.Completion.algebraMap_toCompletion,
      UniformSpace.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]

attribute [local instance] infiniteCompletionScalarTower

/-- A complex place above a real place has quadratic local degree. -/
theorem finrank_complexCompletion_of_real (hv : v.IsReal) (hw : w.IsComplex) :
    Module.finrank v.Completion w.Completion = 2 := by
  apply InfinitePlace.IsRamified.finrank_eq_two v
  exact InfinitePlace.isRamified_iff.mpr ⟨hw, by rwa [InfinitePlace.LiesOver.comap_eq w v]⟩

/-- Complex conjugation on the completion at a complex place above a real place. -/
def realCompletionConjugation (hv : v.IsReal) (hw : w.IsComplex) :
    w.Completion ≃ₐ[v.Completion] w.Completion :=
  AlgEquiv.ofRingEquiv
    (f := (ringEquivComplexOfIsComplex hw).trans
      ((starRingAut (R := ℂ)).trans (ringEquivComplexOfIsComplex hw).symm)) fun x => by
      let : ComplexEmbedding.LiesOver (extensionEmbedding w) (extensionEmbedding v) :=
        InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w hv
      apply (ringEquivComplexOfIsComplex hw).injective
      change ringEquivComplexOfIsComplex hw ((ringEquivComplexOfIsComplex hw).symm
          (star (extensionEmbedding w (algebraMap v.Completion w.Completion x)))) =
        extensionEmbedding w (algebraMap v.Completion w.Completion x)
      rw [RingEquiv.apply_symm_apply, liesOver_extensionEmbedding_apply w v,
        ← extensionEmbeddingOfIsReal_apply hv]
      exact Complex.conj_ofReal _

theorem continuous_realCompletionConjugation (hv : v.IsReal) (hw : w.IsComplex) :
    Continuous (realCompletionConjugation v w hv hw) := by
  change Continuous (fun x : w.Completion =>
    (ringEquivComplexOfIsComplex hw).symm (star (ringEquivComplexOfIsComplex hw x)))
  exact (isometryEquivComplexOfIsComplex hw).symm.continuous.comp
    (continuous_star.comp (isometryEquivComplexOfIsComplex hw).continuous)

variable [FiniteDimensional F Q] [IsGalois F Q]

/-- The local conjugation restricts to the nonidentity element of the
quadratic number-field extension. -/
theorem realCompletionConjugation_restrictNormal (hv : v.IsReal) (hw : w.IsComplex)
    (hdeg : Module.finrank F Q = 2) (σ : Q ≃ₐ[F] Q) (hσ : σ ≠ 1) :
    ((realCompletionConjugation v w hv hw).restrictScalars F).restrictNormal Q = σ := by
  let τ := realCompletionConjugation v w hv hw
  have hne : (τ.restrictScalars F).restrictNormal Q ≠ 1 := by
    intro h
    apply (InfinitePlace.isComplex_iff.mp hw)
    apply ComplexEmbedding.isReal_iff.mpr
    ext x
    have hx := (τ.restrictScalars F).restrictNormal_commutes Q x
    rw [h] at hx
    have he := congrArg (ringEquivComplexOfIsComplex hw) hx
    change extensionEmbedding w (algebraMap Q w.Completion x) =
      (ringEquivComplexOfIsComplex hw) ((ringEquivComplexOfIsComplex hw).symm
        (star (extensionEmbedding w (algebraMap Q w.Completion x)))) at he
    rw [RingEquiv.apply_symm_apply] at he
    simpa using he.symm
  exact (quadratic_aut_eq_one_or hdeg σ hσ _).resolve_left hne

theorem realCompletionConjugation_ne_one (hv : v.IsReal) (hw : w.IsComplex)
    (hdeg : Module.finrank F Q = 2) (σ : Q ≃ₐ[F] Q) (hσ : σ ≠ 1) :
    realCompletionConjugation v w hv hw ≠ 1 := by
  intro h
  apply hσ
  have hr := realCompletionConjugation_restrictNormal v w hv hw hdeg σ hσ
  rw [h] at hr
  change AlgEquiv.restrictNormalHom Q (1 : w.Completion ≃ₐ[F] w.Completion) = σ at hr
  rw [map_one] at hr
  exact hr.symm

end Completions

end Langlands.GroupScheme.GaloisCocycle
