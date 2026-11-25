import Langlands.GroupScheme.Rational.CentralDefectUnitLocalization
import Langlands.GroupScheme.Rational.NumberFieldHasseKernelReduction
import Langlands.ClassFieldTheory.Global.IdeleArchimedean
import Langlands.Global.AdelicFunctoriality.Extension

/-! # Archimedean vanishing of the unit-valued central defect -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry groupCohomology NumberField
open scoped CategoryTheory.MonObj NumberField.LiesOver
open scoped Langlands.Global.AdelicFunctoriality.InfiniteExtension

namespace Langlands.GroupScheme.IsCentralIsogeny

open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local
open Langlands.Global.AdelicFunctoriality

set_option backward.isDefEq.respectTransparency false

/-- Complex conjugation on the actual completion at a complex infinite place. -/
def complexCompletionConjugation {L : Type u} [Field L] {w : InfinitePlace L} (hw : w.IsComplex) :
    w.Completion ≃+* w.Completion :=
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  (e.trans (starRingAut : ℂ ≃+* ℂ)).trans e.symm

theorem extensionEmbedding_complexCompletionConjugation {L : Type u} [Field L]
    {w : InfinitePlace L} (hw : w.IsComplex) (z : w.Completion) :
    InfinitePlace.Completion.extensionEmbedding w (complexCompletionConjugation hw z) =
      star (InfinitePlace.Completion.extensionEmbedding w z) := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  change e (e.symm (star (e z))) = star (e z)
  exact e.apply_symm_apply _

variable {F L : Type u} [Field F] [Field L] [NumberField F]
  [Algebra F L] [IsGalois F L] {G H : GroupScheme (Spec (CommRingCat.of F))}
  {f : G ⟶ H} (hf : IsCentralIsogeny f)
  (χ : kernel f ⟶ (GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp)
  {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ)

private theorem signClass_kernelUnitDefect (w : InfinitePlace L) (c : L ≃ₐ[F] L)
    (hc : ComplexEmbedding.IsConj w.embedding c) (hc₁ : c ≠ 1)
    (h : let b := Spec.algebraMap F (w.comap (algebraMap F L)).Completion
      (ξ.baseChange b ((Over.pullback b).obj (GaloisCocycle.cover F L))
        ((Over.mapPullbackAdj b).counit.app (GaloisCocycle.cover F L))).IsTrivial) :
    Reciprocity.signClass (w.embedding
      (((hf.kernelUnitDefect χ d) (c, c) * (hf.kernelUnitDefect χ d) (1, 1) : Lˣ) : L)) = 0 := by
  have hw : w.IsComplex := by
    apply InfinitePlace.not_isReal_iff_isComplex.mp
    intro hr
    apply hc₁
    apply AlgEquiv.ext
    intro x
    apply w.embedding.injective
    exact (hc.eq x).trans (congrArg (fun p : L →+* ℂ => p x)
      (InfinitePlace.conjugate_embedding_eq_of_isReal hr))
  let v := w.comap (algebraMap F L)
  let : w.LiesOver v := ⟨rfl⟩
  let K := v.Completion
  let M := w.Completion
  let : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F K M]
    exact NumberField.LiesOver.completionMap_coe (v := v) (w := w) (WithAbs.toAbs v.1 x)
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let : FiniteDimensional K M := InfiniteExtension.local_finite v w
  let β := InfinitePlace.Completion.extensionEmbedding w
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  let : IsAlgClosed M := ⟨fun p => Polynomial.Splits.of_splits_map β
    (IsAlgClosed.splits _) (fun x _ => e.surjective x)⟩
  let : Normal K M := ⟨fun x => IsAlgClosed.splits _⟩
  let s := complexCompletionConjugation hw
  have hs (z : M) : β (s z) = star (β z) := by
    exact extensionEmbedding_complexCompletionConjugation hw z
  have hbase (x : K) : star (β (algebraMap K M x)) = β (algebraMap K M x) := by
    induction x using InfinitePlace.Completion.induction_on with
    | hp =>
      have ht : Continuous (fun x : K => β (algebraMap K M x)) :=
        (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
          (NumberField.LiesOver.continuous_completionMap (v := v) (w := w))
      exact isClosed_eq (continuous_star.comp ht) ht
    | ih x =>
      change star (β (algebraMap K M (algebraMap F K (WithAbs.ofAbs x)))) =
        β (algebraMap K M (algebraMap F K (WithAbs.ofAbs x)))
      rw [← IsScalarTower.algebraMap_apply F K M, IsScalarTower.algebraMap_apply F L M]
      change star (InfinitePlace.Completion.extensionEmbedding w
        (algebraMap L M (algebraMap F L (WithAbs.ofAbs x)))) = _
      rw [extensionEmbedding_algebraMap, ← hc.eq, c.commutes]
  let σ : M ≃ₐ[K] M := { s with commutes' := fun x => β.injective ((hs _).trans (hbase x)) }
  have hσ (x : L) : σ (algebraMap L M x) = algebraMap L M (c x) := by
    apply β.injective
    change β (s (algebraMap L M x)) = β (algebraMap L M (c x))
    rw [hs]
    change star (InfinitePlace.Completion.extensionEmbedding w (algebraMap L M x)) =
      InfinitePlace.Completion.extensionEmbedding w (algebraMap L M (c x))
    rw [extensionEmbedding_algebraMap, extensionEmbedding_algebraMap]
    exact (hc.eq x).symm
  obtain ⟨N, _, _, _, _, _, _, _, _, _, _, _, _, a, ha⟩ :=
    hf.exists_primitive_of_baseChange_isTrivial (K := K) (M := M) ξ d h
  let : FiniteDimensional M N := FiniteDimensional.right K M N
  let j : M ≃ₐ[K] N := AlgEquiv.ofBijective (IsScalarTower.toAlgHom K M N)
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let τ : N ≃ₐ[K] N := (j.symm.trans σ).trans j
  let jC : N →+* ℂ := β.comp j.symm.toRingHom
  have hτ (z : N) : jC (τ z) = star (jC z) := by
    change β (j.symm (j (s (j.symm z)))) = star (β (j.symm z))
    rw [AlgEquiv.symm_apply_apply, hs]
  have hjC (x : L) : jC (algebraMap L N x) = w.embedding x := by
    rw [IsScalarTower.algebraMap_apply L M N]
    change β (j.symm (j (algebraMap L M x))) = _
    rw [AlgEquiv.symm_apply_apply]
    exact extensionEmbedding_algebraMap w x
  have hτ₂ : τ * τ = 1 := by
    apply AlgEquiv.ext
    intro x
    apply jC.injective
    change jC (τ (τ x)) = jC x
    rw [hτ, hτ, star_star]
  have hr : (τ.restrictScalars F).restrictNormal L = c := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L N).injective
    rw [(τ.restrictScalars F).restrictNormal_commutes L]
    rw [IsScalarTower.algebraMap_apply L M N, IsScalarTower.algebraMap_apply L M N]
    change j (σ (j.symm (j (algebraMap L M x)))) = j (algebraMap L M (c x))
    rw [AlgEquiv.symm_apply_apply, hσ]
  let p (ρ : N ≃ₐ[K] N) := hf.kernelUnitMap χ N (a ρ)
  let D := hf.kernelUnitDefect χ d
  have hp (g₁ g₂ : N ≃ₐ[K] N) :
      g₁ • p g₂ / p (g₁ * g₂) * p g₁ =
        Units.map (algebraMap L N) (D ((g₁.restrictScalars F).restrictNormal L,
          (g₂.restrictScalars F).restrictNormal L)) := by
    have hpair := congrArg (hf.kernelUnitMap χ N) (ha g₁ g₂)
    have he : hf.kernelUnitMap χ N (GaloisPoint.relativeConjugate F K N hf.commutativeKernel.toGrp g₁
        (a g₂)) = g₁ • p g₂ := hf.kernelUnitMap_naturality χ (g₁.restrictScalars F).toAlgHom _
    have hu (x : GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F L)) :
        hf.kernelUnitMap χ N (GaloisPoint.relativeExtend F L N hf.commutativeKernel.toGrp x) =
          Units.map (algebraMap L N) (hf.kernelUnitMap χ L x) :=
      hf.kernelUnitMap_naturality χ (IsScalarTower.toAlgHom F L N) x
    simpa only [D, p, kernelUnitDefect, map_mul, map_div, he, hu] using hpair
  have h₁ := hp 1 1
  have hr₁ : ((1 : N ≃ₐ[K] N).restrictScalars F).restrictNormal L = 1 :=
    ((AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom F : (N ≃ₐ[K] N) →* (N ≃ₐ[F] N))).map_one
  rw [hr₁, one_mul, one_smul, div_self', one_mul] at h₁
  have h₂ := hp τ τ
  rw [hr, hτ₂] at h₂
  have hnorm : Units.map (algebraMap L N) (D (c, c) * D (1, 1)) = (τ • p τ) * p τ := by
    rw [map_mul, ← h₂, ← h₁, div_mul_eq_mul_div, div_mul_cancel]
  change Reciprocity.signClass (w.embedding ((D (c, c) * D (1, 1) : Lˣ) : L)) = 0
  rw [← hjC]
  have h' := congrArg (fun u : Nˣ => jC (u : N)) hnorm
  change jC (algebraMap L N ((D (c, c) * D (1, 1) : Lˣ) : L)) =
    jC (τ (p τ : N) * (p τ : N)) at h'
  rw [h', map_mul, hτ]
  exact Reciprocity.signClass_star_mul_self _

/-- A trivialization at the underlying infinite completion kills the archimedean
invariant of the kernel character's unit class. -/
theorem archimedeanInvariant_kernelUnitObstruction_eq_zero (w : InfinitePlace L)
    (h : let b := Spec.algebraMap F (w.comap (algebraMap F L)).Completion
      (ξ.baseChange b ((Over.pullback b).obj (GaloisCocycle.cover F L))
        ((Over.mapPullbackAdj b).counit.app (GaloisCocycle.cover F L))).IsTrivial) :
    Reciprocity.archimedeanInvariant w (hf.kernelUnitObstruction χ d) = 0 := by
  classical
  unfold kernelUnitObstruction relativeUnitsClass₂ Reciprocity.archimedeanInvariant
  rw [Reciprocity.H2Lift_H2π]
  simp only [Reciprocity.archimedeanCocycleHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with q
  · exact hf.signClass_kernelUnitDefect χ d w q.choose
      (Reciprocity.isConj_of_mem_stabilizer w q.choose_spec.1 q.choose_spec.2) q.choose_spec.2 h
  · rfl

/-- For an everywhere locally trivial cocycle, each kernel character gives zero global
relative unit class. -/
theorem kernelUnitObstruction_eq_zero [NumberField L] (h : ξ.LocallyTrivial) :
    hf.kernelUnitObstruction χ d = 0 := by
  apply Reciprocity.eq_zero_of_local_eq_zero ideleClassH1Vanishing
    (fun p _ => localInvariantFamily unramifiedH2Exhaustion p)
    (fun p _ => localInvariantFamilyRelativeImages unramifiedH2Exhaustion p)
  · intro v w _
    exact hf.unitsLocalMap_kernelUnitObstruction_eq_zero χ d v w (h (.inr v))
  · intro w
    exact hf.archimedeanInvariant_kernelUnitObstruction_eq_zero χ d w
      (h (.inl (w.comap (algebraMap F L))))

end Langlands.GroupScheme.IsCentralIsogeny
