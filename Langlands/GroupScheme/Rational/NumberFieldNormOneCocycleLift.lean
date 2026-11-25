import Langlands.ClassFieldTheory.Global.FundamentalClassReduction
import Langlands.GroupScheme.Rational.CentralNormOneLocalNorm

/-! # Global central lifting through quadratic and coprime norm-one torsion kernels -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem lifts_of_refined_lift
    {F L E : Type u} [Field F] [Field L] [Field E] [Algebra F L] [Algebra F E] [Algebra L E]
    [IsScalarTower F L E] {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}
    {ξ : Cocycle H (GaloisCocycle.cover F L)}
    (h : (ξ.refine (GaloisCocycle.coverMap F L E)).LiftsAfterFiniteGaloisRefinement f) :
    ξ.LiftsAfterFiniteGaloisRefinement f := by
  obtain ⟨N, _, _, _, _, _, _, ζ, hζ⟩ := h
  let : Algebra L N := Algebra.compHom N (algebraMap L E)
  let : IsScalarTower L E N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower F L N := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F E N, IsScalarTower.algebraMap_apply L E N,
      ← IsScalarTower.algebraMap_apply F L E]
  let r := GaloisCocycle.coverMap F L E
  let s := GaloisCocycle.coverMap F E N
  have ht : s ≫ r = GaloisCocycle.coverMap F L N := by
    change (algSpec (CommRingCat.of F)).map
          (CommAlgCat.ofHom (IsScalarTower.toAlgHom F E N)).op ≫
        (algSpec (CommRingCat.of F)).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom F L E)).op = _
    rw [← Functor.map_comp]
    rfl
  refine ⟨N, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ζ, hζ.trans ?_⟩
  rw [← ht]
  have hh {Z : Over (Spec (CommRingCat.of F))} (x y : Z ⟶ GaloisCocycle.cover F N) :
      ((ξ.refine r).refine s).toFun x y = (ξ.refine (s ≫ r)).toFun x y := by
    simp only [Cocycle.refine_toFun, Category.assoc]
  generalize ((ξ.refine r).refine s) = ξ₁ at hh ⊢
  generalize (ξ.refine (s ≫ r)) = ξ₂ at hh ⊢
  cases ξ₁
  cases ξ₂
  congr
  funext Z x y
  exact hh x y

namespace IsCentralIsogeny

open Langlands.Algebra Langlands.Global Langlands.ClassFieldTheory.Global
open TensorUnitShapiro KummerCocycle

variable {F B L : Type u} [Field F] [Field B] [Field L] [NumberField F] [NumberField B]
  [Algebra F B] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H} (hf : IsCentralIsogeny f)
  (n : ℕ) (hn : n ≠ 0) (e : kernel f ≅ WeilGm.normOneTorsion F B n)
  (hB : Module.finrank F B = 2 ∨ (Module.finrank F B).Coprime n)

include hn e hB in
private theorem lifts_of_normOne_galoisLift [NumberField L] [Algebra B L] [IsScalarTower F B L]
    {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ) (h : ξ.LocallyTrivial) :
    ξ.LiftsAfterFiniteGaloisRefinement f := by
  obtain ⟨M, _, _, _, _, _, _, a, ha, hδ⟩ :=
    hf.tensorTorsionPrimitiveAfterRefinement_of_normOneKernel n hn e d h
  let : NumberField M := NumberField.of_module_finite F M
  let : Algebra B M := Algebra.compHom M (algebraMap B L)
  let : IsScalarTower B L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower F B M := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F L M, IsScalarTower.algebraMap_apply B L M,
      ← IsScalarTower.algebraMap_apply F B L]
  let r := GaloisCocycle.coverMap F L M
  let rd := hf.restrictGaloisLift (K := F) (M := M) ξ d
  let d' : hf.GaloisLift (ξ.refine r) :=
    ⟨rd.value, fun σ => by
      rw [GaloisCocycle.value_refine]
      exact rd.project σ, rd.defect, rd.defect_spec⟩
  let k := kernelNormOneToWeil n e
  have hδ' (σ τ : Gal(M/F)) : tensorDifferential a σ τ = hf.kernelTensorDefect k d' (σ, τ) :=
    (hδ σ τ).trans (kernelTensorUnitMap_naturality k (IsScalarTower.toAlgHom F L M)
      (d.defect (σ.restrictNormal L, τ.restrictNormal L))).symm
  have hnorm (σ τ : Gal(M/F)) : tensorNormUnits F B M (tensorDifferential a σ τ) = 1 := by
    rw [hδ']
    exact kernelTensorUnitMap_norm_eq_one n e M (d'.defect (σ, τ))
  obtain ⟨s, z, hz, hN⟩ := exists_tensorNorm_radical n a ha hnorm
  have hs : IsNormMulPower (E := B) n s := by
    rcases hB with hB | hB
    · exact numberFieldQuadraticNormOneRadicalDescent F B M hB hf n e d' (h.refine r) a ha hδ'
        s z hz (fun σ => (hN σ).symm)
    · exact isNormMulPower_of_coprime n hB s
  have hp := tensorNormOnePrimitiveAfterRefinement_of_normPower n hn a ha hz
    (fun σ => (hN σ).symm) hs
  have hc : (fun p : Gal(M/F) × Gal(M/F) => tensorDifferential a p.1 p.2) =
      hf.kernelTensorDefect k d' := by
    funext p
    exact hδ' p.1 p.2
  rw [hc] at hp
  exact lifts_of_refined_lift (hf.liftsAfterFiniteGaloisRefinement_of_normOnePrimitive n e d' hp)

include hf hn e hB in
/-- Local triviality gives a global lift after finite Galois refinement for norm-one torsion
of quadratic degree or degree coprime to the torsion exponent. -/
theorem liftsAfterFiniteGaloisRefinement_of_normOneKernel
    (ξ : Cocycle H (GaloisCocycle.cover F L)) (h : ξ.LocallyTrivial) :
    ξ.LiftsAfterFiniteGaloisRefinement f := by
  let : NumberField L := NumberField.of_module_finite F L
  obtain ⟨D, hDfin, hDgal, ⟨j⟩⟩ := exists_finite_galois_algHom F B
  let : NumberField D := NumberField.of_module_finite F D
  obtain ⟨K, _, _, _, _, _, hLK, hDK, hKg⟩ := FundamentalClass.exists_galois_tower F L D
  let jB : B →ₐ[F] K := (IsScalarTower.toAlgHom F D K).comp j
  let : Algebra B K := jB.toRingHom.toAlgebra
  let : IsScalarTower F B K := IsScalarTower.of_algebraMap_eq fun x => (jB.commutes x).symm
  let r := GaloisCocycle.coverMap F L K
  obtain ⟨E, _, _, _, _, _, _, ⟨d⟩⟩ := hf.exists_finiteGalois_refine_galoisLift (ξ.refine r)
  let : NumberField E := NumberField.of_module_finite F E
  let : Algebra B E := Algebra.compHom E (algebraMap B K)
  let : IsScalarTower B K E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower F B E := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F K E, IsScalarTower.algebraMap_apply B K E,
      ← IsScalarTower.algebraMap_apply F B K]
  exact lifts_of_refined_lift (lifts_of_refined_lift
    (hf.lifts_of_normOne_galoisLift n hn e hB d ((h.refine r).refine (GaloisCocycle.coverMap F K E))))

end IsCentralIsogeny

/-- Norm-one torsion kernels of quadratic or coprime degree satisfy the global lifting property. -/
def NumberFieldNormOneKernelLiftingStatement : Prop :=
  ∀ (F B L : Type u) [Field F] [Field B] [Field L] [NumberField F] [NumberField B]
    [Algebra F B] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {G H : GroupScheme (Spec (CommRingCat.of F))} (f : G ⟶ H), IsCentralIsogeny f →
    ∀ n : ℕ, 0 < n → Nonempty (kernel f ≅ WeilGm.normOneTorsion F B n) →
      (Module.finrank F B = 2 ∨ (Module.finrank F B).Coprime n) →
      ∀ ξ : Cocycle H (GaloisCocycle.cover F L), ξ.LocallyTrivial →
        ξ.LiftsAfterFiniteGaloisRefinement f

/-- The norm-one central lifting theorem on an arbitrary finite Galois cover. -/
theorem numberFieldNormOneKernelLifting : NumberFieldNormOneKernelLiftingStatement.{u} := by
  rintro F B L _ _ _ _ _ _ _ _ _ G H f hf n hn ⟨e⟩ hB ξ h
  exact hf.liftsAfterFiniteGaloisRefinement_of_normOneKernel n hn.ne' e hB ξ h

end Langlands.GroupScheme
